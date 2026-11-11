import Lean.Compiler.IR
import Lean.Compiler.CSimpAttr

/-! # lean-ts: a Lean IR -> TypeScript backend, mirroring EmitC.

We obtain IR `Decl`s via `Lean.IR.findEnvDecl`, then walk `FnBody`/`Expr`
and emit a typed TypeScript module that calls the runtime (`lean-ts/runtime`)
through the namespace import `L`. Reference-counting nodes
(inc/dec/del/reset/reuse) are omitted because the JS engine has a tracing GC. -/

open Lean Lean.IR

namespace LeanTs

/-- How a known Lean function is emitted: a call to a runtime function, or a JS literal. -/
inductive Known where
  | call (sym : String)
  | lit (js : String)

/-- Emission state: the output buffer and indent level, the tables of the
    collected declarations, and what the emitted code references. -/
structure EmitState where
  out    : String := ""
  indent : Nat    := 0
  /-- Extern Lean-name → resolved C symbol map (the link table); read by the
      `.fap` emission path so extern aliases route to their runtime function. -/
  externMap : Std.HashMap Name String := {}
  /-- Function name → full JS arity (count of non-erased/non-void params, the
      same params `funRef` declares). Read by the `.pap` emission path so a
      partial application records the worker's arity, letting `lean_apply` do the
      C runtime's three-way exact/under/over dispatch. -/
  arityMap : Std.HashMap Name Nat := {}
  /-- Collected decl → which params survive into the emitted signature (the
      non-erased, non-void ones). A direct call passes only the args at those
      positions, exactly as the signature declares them. -/
  masks : Std.HashMap Name (Array Bool) := {}
  /-- Collected `.fdecl` names (emitted as functions). -/
  fdecls : Std.HashSet Name := {}
  /-- 0-param globals backed by an `initialize ... ← ...` init fn (IR body `⊥`,
      `getInitFnNameFor? = some`). These are emitted as a mutable `let` slot (not
      a `function`), assigned by the init thunk, and referenced WITHOUT `()` at
      `.fap c []` use sites — mirroring EmitC, which emits a C global and assigns
      `lean_io_result_get_value(res)` to it. -/
  initGlobals : Std.HashSet Name := {}
  /-- Names that have a `__tc` core (thunk targets). A `.pap` over such a worker
      records the core (`tcRef`) as the closure's fn, so `lean_apply` returns a
      `tc` thunk naming the core that the single outer `lean_trampoline` unrolls
      — instead of naming the public wrapper, whose own nested `lean_trampoline`
      would re-grow the JS stack once per tail-`.ap` step. -/
  cores : Std.HashSet Name := {}
  /-- Variables of the decl being emitted that the emitted code reads. -/
  used : Std.HashSet Nat := {}
  /-- Function identifiers referenced by the piece being emitted. -/
  refs : Std.HashSet String := {}
  /-- Runtime functions referenced through `L.`. -/
  syms : Std.HashSet String := {}
  /-- Scalar variables switched on by an enclosing `case`. -/
  switched : Std.HashSet Nat := {}
  errors : Array String := #[]

abbrev EmitM := StateM EmitState

def line (s : String) : EmitM Unit := do
  let st ← get
  let pad := String.ofList (List.replicate (st.indent * 2) ' ')
  set { st with out := st.out ++ pad ++ s ++ "\n" }

def withIndent (act : EmitM Unit) : EmitM Unit := do
  modify (fun st => { st with indent := st.indent + 1 })
  act
  modify (fun st => { st with indent := st.indent - 1 })

/-- TS identifier for an IR variable. -/
def varName (x : VarId) : String := s!"x_{x.idx}"
def jpName  (j : JoinPointId) : String := s!"block_{j.idx}"

def argToJs : Arg → String
  | .var id => varName id
  | .erased => "undefined"

def argsToJs (ys : Array Arg) : String :=
  ", ".intercalate (ys.toList.map argToJs)

/-- TS type of a value of an IR type: scalars are JS numbers or bigints, every
    other value (objects, boxed scalars, erased values) is the runtime's `Obj`. -/
def tsType : IRType → String
  | .uint8 | .uint16 | .uint32 | .float | .float32 => "number"
  | .uint64 | .usize => "bigint"
  | _ => "Obj"

/-- Narrow an `Obj`-typed expression to the TS type of a scalar IR type. -/
def coerce (ty : IRType) (e : String) : String :=
  match ty with
  | .uint8 | .uint16 | .uint32 | .float | .float32 => s!"L.lean_unbox({e})"
  | .uint64 | .usize => s!"L.lean_unbox_uint64({e})"
  | _ => e

def isLive (p : Param) : Bool := !p.ty.isErased && !p.ty.isVoid

/-- TS function reference for an arbitrary FunId: `l_` (the C backend's prefix)
    and the name with dots turned into `_`; any other character that is not a
    valid JS identifier char (`?`, `!`, `'`, Greek/subscript hygiene markers,
    etc. — all legal in Lean names) is escaped to `_x<code point>_` so the
    emitted name is always a valid JS identifier. -/
def funRef (c : FunId) : String := Id.run do
  let mut acc := "l_"
  let chars := (toString c).toList
  for (ch, i) in chars.zipIdx do
    if ch == '.' then acc := acc ++ "_"
    else if (ch.isAlphanum || ch == '_') && ch.toNat < 128 then acc := acc.push ch
    else
      -- escape any other char (incl. non-ASCII) by its code point, bracketed by
      -- `_` so it cannot merge with adjacent digits/letters (the closing `_` is
      -- left off at the end of the name, which nothing can merge with).
      acc := acc ++ "_x" ++ toString ch.toNat ++ (if i + 1 == chars.length then "" else "_")
  return acc

/-- Trampoline core suffix: `funRef` of a thunk-returning core. -/
def tcRef (c : FunId) : String := funRef c ++ "__tc"

/-- `L.<sym>`, recording that the module uses the runtime function `sym`. -/
def sym (s : String) : EmitM String := do
  modify fun st => { st with syms := st.syms.insert s }
  return s!"L.{s}"

/-- A function identifier, recording the reference. -/
def ref (s : String) : EmitM String := do
  modify fun st => { st with refs := st.refs.insert s }
  return s

def addError (msg : String) : EmitM Unit :=
  modify fun st => { st with errors := st.errors.push msg }

/-! ## Extern → runtime-function single source of truth (analogue of EmitC)

Rather than hand-keying a table on Lean *decl* names (every `@[extern]` alias —
`USize.ofNat`/`USize.ofNatLT`/`Nat.toUSize` all share the C symbol
`lean_usize_of_nat` — has to be re-listed), we resolve the actual C symbol via
`Lean.getExternNameFor env `c name`, exactly like `EmitC.toCName`. The runtime
is keyed on that same C symbol, so all aliases route for free.

`externSymbol env c` returns the C symbol for an extern decl `c` (the `standard`
entry's literal string for backend `c`/`all`), or `none` for a non-extern decl
or an extern with no usable C entry (adhoc/inline/opaque). -/
def externSymbol (env : Environment) (c : Name) : Option String :=
  getExternNameFor env `c c

def tsExternTarget (env : Environment) (c : Name) : Option String :=
  match externSymbol env c with
  | some s => if s.startsWith "ts:" then some s else none
  | none => none

def csimpToTs (env : Environment) : Std.HashMap Name Name :=
  (Compiler.CSimp.ext.getState env).map.toList.foldl (init := {}) fun acc (k, e) =>
    if (tsExternTarget env e.toDeclName).isSome then acc.insert k e.toDeclName else acc

def substExpr (s : Std.HashMap Name Name) : IR.Expr → IR.Expr
  | .fap c ys => .fap (s.getD c c) ys
  | .pap c ys => .pap (s.getD c c) ys
  | e => e

partial def substBody (s : Std.HashMap Name Name) : FnBody → FnBody
  | .vdecl x ty e b => .vdecl x ty (substExpr s e) (substBody s b)
  | .jdecl j xs v b => .jdecl j xs (substBody s v) (substBody s b)
  | .case tid x xty alts => .case tid x xty (alts.map (·.modifyBody (substBody s)))
  | other => if other.isTerminal then other else other.setBody (substBody s other.body)

def substDecl (s : Std.HashMap Name Name) : Decl → Decl
  | .fdecl f xs ty b info => if s.isEmpty then .fdecl f xs ty b info else .fdecl f xs ty (substBody s b) info
  | d => d

/-- Escape a Lean string literal into a JS double-quoted string,
    mirroring `EmitC.quoteString` (\n \r \t \\ \" and control chars). -/
def quoteString (s : String) : String := Id.run do
  let mut acc := "\""
  for c in s.toList do
    let n := c.toNat
    if c == '\\' then acc := acc ++ "\\\\"
    else if c == '"' then acc := acc ++ "\\\""
    else if c == '\n' then acc := acc ++ "\\n"
    else if c == '\r' then acc := acc ++ "\\r"
    else if c == '\t' then acc := acc ++ "\\t"
    else if n < 32 then
      let hex := String.ofList (Nat.toDigits 16 n)
      let hex := if hex.length == 1 then "0" ++ hex else hex
      acc := acc ++ "\\u00" ++ hex
    else
      acc := acc.push c
  return acc ++ "\""

/-- Lean functions emitted by an explicit arm instead of their own IR or their
    resolved C symbol: a runtime function whose name differs from the C symbol
    (`Nat.toUInt32` -> `lean_uint32_of_nat2`, libm `Float.tan` ->
    `lean_float_tan`), or a literal (`Array.empty` -> `[]`). Everything else that
    is an extern routes to its C symbol (`externMap`). -/
def knownFap : FunId → Option Known
  -- Nat: total arithmetic (/0 -> 0, %0 -> lhs, truncated sub).
  | `Nat.add => some (.call "lean_nat_add")
  | `Nat.mul => some (.call "lean_nat_mul")
  | `Nat.sub => some (.call "lean_nat_sub")
  | `Nat.div => some (.call "lean_nat_div")
  | `Nat.mod => some (.call "lean_nat_mod")
  | `Nat.pow      => some (.call "lean_nat_pow")
  | `Nat.gcd      => some (.call "lean_nat_gcd")
  | `Nat.pred     => some (.call "lean_nat_pred")
  | `Nat.decEq    => some (.call "lean_nat_dec_eq")
  | `Nat.decLt    => some (.call "lean_nat_dec_lt")
  | `Nat.decLe    => some (.call "lean_nat_dec_le")
  | `Nat.beq      => some (.call "lean_nat_dec_eq")
  | `Nat.ble      => some (.call "lean_nat_dec_le")
  | `Nat.blt      => some (.call "lean_nat_dec_lt")
  -- Int
  | `Int.neg      => some (.call "lean_int_neg")
  | `Int.add      => some (.call "lean_int_add")
  | `Int.sub      => some (.call "lean_int_sub")
  | `Int.mul      => some (.call "lean_int_mul")
  | `Int.div      => some (.call "lean_int_div")
  | `Int.mod      => some (.call "lean_int_mod")
  | `Int.ediv     => some (.call "lean_int_ediv")
  | `Int.emod     => some (.call "lean_int_emod")
  | `Int.decEq    => some (.call "lean_int_dec_eq")
  | `Int.decLt    => some (.call "lean_int_dec_lt")
  | `Int.decLe    => some (.call "lean_int_dec_le")
  -- String
  | `String.length    => some (.call "lean_string_length")
  | `String.append    => some (.call "lean_string_append")
  | `String.push      => some (.call "lean_string_push")
  | `String.decEq     => some (.call "lean_string_dec_eq")
  | `String.data      => some (.call "lean_string_data")
  | `String.toList    => some (.call "lean_string_data")
  | `String.mk        => some (.call "lean_string_mk")
  | `String.isEmpty   => some (.call "lean_string_isempty")
  | `String.hash      => some (.call "lean_string_hash")
  -- String: UTF-8 byte-position layer (Pos == byte offset).
  | `String.utf8ByteSize => some (.call "lean_string_utf8_byte_size")
  | `String.get       => some (.call "lean_string_utf8_get")
  | `String.get!      => some (.call "lean_string_utf8_get_bang")
  | `String.get?      => some (.call "lean_string_utf8_get_opt")
  | `String.next      => some (.call "lean_string_utf8_next")
  | `String.prev      => some (.call "lean_string_utf8_prev")
  | `String.atEnd     => some (.call "lean_string_utf8_at_end")
  | `String.Pos.Raw.extract => some (.call "lean_string_utf8_extract")
  | `String.Pos.Raw.get => some (.call "lean_string_utf8_get")
  | `String.Pos.Raw.next => some (.call "lean_string_utf8_next")
  | `String.Pos.Raw.prev => some (.call "lean_string_utf8_prev")
  | `String.posOf     => some (.call "lean_string_utf8_pos_of")
  | `String.contains  => some (.call "lean_string_contains")
  -- UIntN / USize: map to the wrapping runtime ops (src/runtime/uint.ts, int.ts).
  | `UInt8.add => some (.call "lean_uint8_add") | `UInt8.sub => some (.call "lean_uint8_sub")
  | `UInt8.mul => some (.call "lean_uint8_mul") | `UInt8.div => some (.call "lean_uint8_div")
  | `UInt8.mod => some (.call "lean_uint8_mod") | `UInt8.land => some (.call "lean_uint8_land")
  | `UInt8.lor => some (.call "lean_uint8_lor") | `UInt8.xor => some (.call "lean_uint8_xor")
  | `UInt8.complement => some (.call "lean_uint8_complement")
  | `UInt8.shiftLeft => some (.call "lean_uint8_shift_left") | `UInt8.shiftRight => some (.call "lean_uint8_shift_right")
  | `UInt8.decEq => some (.call "lean_uint8_dec_eq") | `UInt8.decLt => some (.call "lean_uint8_dec_lt")
  | `UInt8.decLe => some (.call "lean_uint8_dec_le") | `UInt8.toNat => some (.call "lean_uint8_to_nat")
  | `UInt8.ofNat => some (.call "lean_uint8_of_nat") | `UInt8.ofNatLF => some (.call "lean_uint8_of_nat")
  | `UInt16.add => some (.call "lean_uint16_add") | `UInt16.sub => some (.call "lean_uint16_sub")
  | `UInt16.mul => some (.call "lean_uint16_mul") | `UInt16.div => some (.call "lean_uint16_div")
  | `UInt16.mod => some (.call "lean_uint16_mod") | `UInt16.land => some (.call "lean_uint16_land")
  | `UInt16.lor => some (.call "lean_uint16_lor") | `UInt16.xor => some (.call "lean_uint16_xor")
  | `UInt16.complement => some (.call "lean_uint16_complement")
  | `UInt16.shiftLeft => some (.call "lean_uint16_shift_left") | `UInt16.shiftRight => some (.call "lean_uint16_shift_right")
  | `UInt16.decEq => some (.call "lean_uint16_dec_eq") | `UInt16.decLt => some (.call "lean_uint16_dec_lt")
  | `UInt16.decLe => some (.call "lean_uint16_dec_le") | `UInt16.toNat => some (.call "lean_uint16_to_nat")
  | `UInt16.ofNat => some (.call "lean_uint16_of_nat") | `UInt16.ofNatLF => some (.call "lean_uint16_of_nat")
  | `UInt32.add => some (.call "lean_uint32_add") | `UInt32.sub => some (.call "lean_uint32_sub")
  | `UInt32.mul => some (.call "lean_uint32_mul") | `UInt32.div => some (.call "lean_uint32_div")
  | `UInt32.mod => some (.call "lean_uint32_mod") | `UInt32.land => some (.call "lean_uint32_land")
  | `UInt32.lor => some (.call "lean_uint32_lor") | `UInt32.xor => some (.call "lean_uint32_xor")
  | `UInt32.complement => some (.call "lean_uint32_complement")
  | `UInt32.shiftLeft => some (.call "lean_uint32_shift_left") | `UInt32.shiftRight => some (.call "lean_uint32_shift_right")
  | `UInt32.decEq => some (.call "lean_uint32_dec_eq") | `UInt32.decLt => some (.call "lean_uint32_dec_lt")
  | `UInt32.decLe => some (.call "lean_uint32_dec_le") | `UInt32.toNat => some (.call "lean_uint32_to_nat")
  | `UInt32.ofNat => some (.call "lean_uint32_of_nat") | `UInt32.ofNatLF => some (.call "lean_uint32_of_nat")
  | `UInt64.add => some (.call "lean_uint64_add") | `UInt64.sub => some (.call "lean_uint64_sub")
  | `UInt64.mul => some (.call "lean_uint64_mul") | `UInt64.div => some (.call "lean_uint64_div")
  | `UInt64.mod => some (.call "lean_uint64_mod") | `UInt64.land => some (.call "lean_uint64_land")
  | `UInt64.lor => some (.call "lean_uint64_lor") | `UInt64.xor => some (.call "lean_uint64_xor")
  | `UInt64.complement => some (.call "lean_uint64_complement")
  | `UInt64.shiftLeft => some (.call "lean_uint64_shift_left") | `UInt64.shiftRight => some (.call "lean_uint64_shift_right")
  | `UInt64.decEq => some (.call "lean_uint64_dec_eq") | `UInt64.decLt => some (.call "lean_uint64_dec_lt")
  | `UInt64.decLe => some (.call "lean_uint64_dec_le") | `UInt64.toNat => some (.call "lean_uint64_to_nat")
  | `UInt64.ofNat => some (.call "lean_uint64_of_nat") | `UInt64.ofNatLF => some (.call "lean_uint64_of_nat")
  | `USize.add => some (.call "lean_usize_add") | `USize.sub => some (.call "lean_usize_sub")
  | `USize.mul => some (.call "lean_usize_mul") | `USize.div => some (.call "lean_usize_div")
  | `USize.mod => some (.call "lean_usize_mod") | `USize.land => some (.call "lean_usize_land")
  | `USize.lor => some (.call "lean_usize_lor") | `USize.xor => some (.call "lean_usize_xor")
  | `USize.complement => some (.call "lean_usize_complement")
  | `USize.shiftLeft => some (.call "lean_usize_shift_left") | `USize.shiftRight => some (.call "lean_usize_shift_right")
  | `USize.decEq => some (.call "lean_usize_dec_eq") | `USize.decLt => some (.call "lean_usize_dec_lt")
  | `USize.decLe => some (.call "lean_usize_dec_le") | `USize.toNat => some (.call "lean_usize_to_nat")
  | `USize.ofNat => some (.call "lean_usize_of_nat") | `USize.ofNatLF => some (.call "lean_usize_of_nat")
  -- Signed fixed-width ints (bigint repr; two's-complement wrap). 64-bit/ISize
  -- toInt uses the *_sint extern name; 8/16/32 use plain *_to_int.
  | `Int8.add => some (.call "lean_int8_add") | `Int8.sub => some (.call "lean_int8_sub")
  | `Int8.mul => some (.call "lean_int8_mul") | `Int8.div => some (.call "lean_int8_div")
  | `Int8.mod => some (.call "lean_int8_mod") | `Int8.neg => some (.call "lean_int8_neg")
  | `Int8.land => some (.call "lean_int8_land") | `Int8.lor => some (.call "lean_int8_lor")
  | `Int8.xor => some (.call "lean_int8_xor") | `Int8.complement => some (.call "lean_int8_complement")
  | `Int8.shiftLeft => some (.call "lean_int8_shift_left") | `Int8.shiftRight => some (.call "lean_int8_shift_right")
  | `Int8.decEq => some (.call "lean_int8_dec_eq") | `Int8.decLt => some (.call "lean_int8_dec_lt")
  | `Int8.decLe => some (.call "lean_int8_dec_le")
  | `Int8.ofInt => some (.call "lean_int8_of_int") | `Int8.ofNat => some (.call "lean_int8_of_nat")
  | `Int8.toInt => some (.call "lean_int8_to_int")
  | `Int16.add => some (.call "lean_int16_add") | `Int16.sub => some (.call "lean_int16_sub")
  | `Int16.mul => some (.call "lean_int16_mul") | `Int16.div => some (.call "lean_int16_div")
  | `Int16.mod => some (.call "lean_int16_mod") | `Int16.neg => some (.call "lean_int16_neg")
  | `Int16.land => some (.call "lean_int16_land") | `Int16.lor => some (.call "lean_int16_lor")
  | `Int16.xor => some (.call "lean_int16_xor") | `Int16.complement => some (.call "lean_int16_complement")
  | `Int16.shiftLeft => some (.call "lean_int16_shift_left") | `Int16.shiftRight => some (.call "lean_int16_shift_right")
  | `Int16.decEq => some (.call "lean_int16_dec_eq") | `Int16.decLt => some (.call "lean_int16_dec_lt")
  | `Int16.decLe => some (.call "lean_int16_dec_le")
  | `Int16.ofInt => some (.call "lean_int16_of_int") | `Int16.ofNat => some (.call "lean_int16_of_nat")
  | `Int16.toInt => some (.call "lean_int16_to_int")
  | `Int32.add => some (.call "lean_int32_add") | `Int32.sub => some (.call "lean_int32_sub")
  | `Int32.mul => some (.call "lean_int32_mul") | `Int32.div => some (.call "lean_int32_div")
  | `Int32.mod => some (.call "lean_int32_mod") | `Int32.neg => some (.call "lean_int32_neg")
  | `Int32.land => some (.call "lean_int32_land") | `Int32.lor => some (.call "lean_int32_lor")
  | `Int32.xor => some (.call "lean_int32_xor") | `Int32.complement => some (.call "lean_int32_complement")
  | `Int32.shiftLeft => some (.call "lean_int32_shift_left") | `Int32.shiftRight => some (.call "lean_int32_shift_right")
  | `Int32.decEq => some (.call "lean_int32_dec_eq") | `Int32.decLt => some (.call "lean_int32_dec_lt")
  | `Int32.decLe => some (.call "lean_int32_dec_le")
  | `Int32.ofInt => some (.call "lean_int32_of_int") | `Int32.ofNat => some (.call "lean_int32_of_nat")
  | `Int32.toInt => some (.call "lean_int32_to_int")
  | `Int64.add => some (.call "lean_int64_add") | `Int64.sub => some (.call "lean_int64_sub")
  | `Int64.mul => some (.call "lean_int64_mul") | `Int64.div => some (.call "lean_int64_div")
  | `Int64.mod => some (.call "lean_int64_mod") | `Int64.neg => some (.call "lean_int64_neg")
  | `Int64.land => some (.call "lean_int64_land") | `Int64.lor => some (.call "lean_int64_lor")
  | `Int64.xor => some (.call "lean_int64_xor") | `Int64.complement => some (.call "lean_int64_complement")
  | `Int64.shiftLeft => some (.call "lean_int64_shift_left") | `Int64.shiftRight => some (.call "lean_int64_shift_right")
  | `Int64.decEq => some (.call "lean_int64_dec_eq") | `Int64.decLt => some (.call "lean_int64_dec_lt")
  | `Int64.decLe => some (.call "lean_int64_dec_le")
  | `Int64.ofInt => some (.call "lean_int64_of_int") | `Int64.ofNat => some (.call "lean_int64_of_nat")
  | `Int64.toInt => some (.call "lean_int64_to_int_sint")
  | `ISize.add => some (.call "lean_isize_add") | `ISize.sub => some (.call "lean_isize_sub")
  | `ISize.mul => some (.call "lean_isize_mul") | `ISize.div => some (.call "lean_isize_div")
  | `ISize.mod => some (.call "lean_isize_mod") | `ISize.neg => some (.call "lean_isize_neg")
  | `ISize.land => some (.call "lean_isize_land") | `ISize.lor => some (.call "lean_isize_lor")
  | `ISize.xor => some (.call "lean_isize_xor") | `ISize.complement => some (.call "lean_isize_complement")
  | `ISize.shiftLeft => some (.call "lean_isize_shift_left") | `ISize.shiftRight => some (.call "lean_isize_shift_right")
  | `ISize.decEq => some (.call "lean_isize_dec_eq") | `ISize.decLt => some (.call "lean_isize_dec_lt")
  | `ISize.decLe => some (.call "lean_isize_dec_le")
  | `ISize.ofInt => some (.call "lean_isize_of_int") | `ISize.ofNat => some (.call "lean_isize_of_nat")
  | `ISize.toInt => some (.call "lean_isize_to_int_sint")
  -- Float / Float32
  | `Float.add => some (.call "lean_float_add") | `Float.sub => some (.call "lean_float_sub")
  | `Float.mul => some (.call "lean_float_mul") | `Float.div => some (.call "lean_float_div")
  | `Float.neg => some (.call "lean_float_negate")
  | `Float.beq => some (.call "lean_float_beq") | `Float.decLt => some (.call "lean_float_decLt")
  | `Float.decLe => some (.call "lean_float_decLe")
  | `Float.isNaN => some (.call "lean_float_isnan") | `Float.isFinite => some (.call "lean_float_isfinite")
  | `Float.isInf => some (.call "lean_float_isinf")
  | `Float.sqrt => some (.call "lean_float_sqrt") | `Float.sin => some (.call "lean_float_sin")
  | `Float.cos => some (.call "lean_float_cos") | `Float.exp => some (.call "lean_float_exp")
  | `Float.log => some (.call "lean_float_log") | `Float.pow => some (.call "lean_float_pow")
  | `Float.tan => some (.call "lean_float_tan")
  | `Float.asin => some (.call "lean_float_asin") | `Float.acos => some (.call "lean_float_acos")
  | `Float.atan => some (.call "lean_float_atan") | `Float.atan2 => some (.call "lean_float_atan2")
  | `Float.sinh => some (.call "lean_float_sinh") | `Float.cosh => some (.call "lean_float_cosh")
  | `Float.tanh => some (.call "lean_float_tanh")
  | `Float.asinh => some (.call "lean_float_asinh") | `Float.acosh => some (.call "lean_float_acosh")
  | `Float.atanh => some (.call "lean_float_atanh")
  | `Float.exp2 => some (.call "lean_float_exp2") | `Float.log2 => some (.call "lean_float_log2")
  | `Float.log10 => some (.call "lean_float_log10") | `Float.cbrt => some (.call "lean_float_cbrt")
  | `Float.frExp => some (.call "lean_float_frexp")
  | `Float.ofBits => some (.call "lean_float_of_bits") | `Float.toBits => some (.call "lean_float_to_bits")
  | `Float.floor => some (.call "lean_float_floor") | `Float.ceil => some (.call "lean_float_ceil")
  | `Float.abs => some (.call "lean_float_abs") | `Float.round => some (.call "lean_float_round")
  | `Float.scaleb => some (.call "lean_float_scaleb")
  | `Float.toUInt8 => some (.call "lean_float_to_uint8") | `Float.toUInt16 => some (.call "lean_float_to_uint16")
  | `Float.toUInt32 => some (.call "lean_float_to_uint32") | `Float.toUInt64 => some (.call "lean_float_to_uint64")
  | `Float.toUSize => some (.call "lean_float_to_usize")
  | `Float.toFloat32 => some (.call "lean_float_to_float32")
  | `Float.ofScientific => some (.call "lean_float_of_scientific")
  | `Float32.add => some (.call "lean_float32_add") | `Float32.sub => some (.call "lean_float32_sub")
  | `Float32.mul => some (.call "lean_float32_mul") | `Float32.div => some (.call "lean_float32_div")
  | `Float32.neg => some (.call "lean_float32_negate")
  | `Float32.beq => some (.call "lean_float32_beq") | `Float32.decLt => some (.call "lean_float32_decLt")
  | `Float32.decLe => some (.call "lean_float32_decLe")
  | `Float32.toFloat => some (.call "lean_float32_to_float")
  | `Float32.sqrt => some (.call "lean_float32_sqrt") | `Float32.abs => some (.call "lean_float32_abs")
  | `Float32.sin => some (.call "lean_float32_sin") | `Float32.cos => some (.call "lean_float32_cos")
  | `Float32.tan => some (.call "lean_float32_tan")
  | `Float32.asin => some (.call "lean_float32_asin") | `Float32.acos => some (.call "lean_float32_acos")
  | `Float32.atan => some (.call "lean_float32_atan") | `Float32.atan2 => some (.call "lean_float32_atan2")
  | `Float32.sinh => some (.call "lean_float32_sinh") | `Float32.cosh => some (.call "lean_float32_cosh")
  | `Float32.tanh => some (.call "lean_float32_tanh")
  | `Float32.asinh => some (.call "lean_float32_asinh") | `Float32.acosh => some (.call "lean_float32_acosh")
  | `Float32.atanh => some (.call "lean_float32_atanh")
  | `Float32.exp => some (.call "lean_float32_exp") | `Float32.exp2 => some (.call "lean_float32_exp2")
  | `Float32.log => some (.call "lean_float32_log") | `Float32.log2 => some (.call "lean_float32_log2")
  | `Float32.log10 => some (.call "lean_float32_log10") | `Float32.pow => some (.call "lean_float32_pow")
  | `Float32.cbrt => some (.call "lean_float32_cbrt")
  | `Float32.floor => some (.call "lean_float32_floor") | `Float32.ceil => some (.call "lean_float32_ceil")
  | `Float32.round => some (.call "lean_float32_round")
  | `Float32.isNaN => some (.call "lean_float32_isnan") | `Float32.isFinite => some (.call "lean_float32_isfinite")
  | `Float32.isInf => some (.call "lean_float32_isinf")
  | `Float32.ofBits => some (.call "lean_float32_of_bits") | `Float32.toBits => some (.call "lean_float32_to_bits")
  | `Float32.scaleb => some (.call "lean_float32_scaleb") | `Float32.frExp => some (.call "lean_float32_frexp")
  | `Float32.toUInt8 => some (.call "lean_float32_to_uint8") | `Float32.toUInt16 => some (.call "lean_float32_to_uint16")
  | `Float32.toUInt32 => some (.call "lean_float32_to_uint32") | `Float32.toUInt64 => some (.call "lean_float32_to_uint64")
  | `Float32.toUSize => some (.call "lean_float32_to_usize")
  | `USize.toFloat => some (.call "lean_usize_to_float")
  | `UInt8.toFloat32 => some (.call "lean_uint8_to_float32") | `UInt16.toFloat32 => some (.call "lean_uint16_to_float32")
  | `UInt32.toFloat32 => some (.call "lean_uint32_to_float32") | `UInt64.toFloat32 => some (.call "lean_uint64_to_float32")
  | `USize.toFloat32 => some (.call "lean_usize_to_float32")
  | `Float.toString => some (.call "lean_float_to_string")
  | `Float32.toString => some (.call "lean_float32_to_string")
  -- Char
  | `Char.ofNat       => some (.call "lean_uint32_of_nat")
  | `Char.toNat       => some (.call "lean_char_to_nat")
  -- Array
  | `Array.empty                  => some (.lit "[]")
  | `Array.mkEmpty                => some (.lit "[]")
  | `Array.emptyWithCapacity      => some (.lit "[]")
  | `Array.size                   => some (.call "lean_array_get_size")
  | `Array.get!                   => some (.call "lean_array_get")
  | `Array.getD                   => some (.call "lean_array_get")
  | `Array.get                    => some (.call "lean_array_fget")
  | `Array.set                    => some (.call "lean_array_set")
  | `Array.set!                   => some (.call "lean_array_set")
  | `Array.push                   => some (.call "lean_array_push")
  | `Array.pop                    => some (.call "lean_array_pop")
  | `Array.swap                   => some (.call "lean_array_swap")
  | `Array.uget                   => some (.call "lean_array_uget")
  | `Array.ugetBorrowed           => some (.call "lean_array_uget_borrowed")
  | `Array.getInternal            => some (.call "lean_array_fget")
  | `Array.getInternalBorrowed    => some (.call "lean_array_fget_borrowed")
  | `Array.uset                   => some (.call "lean_array_uset")
  | `Array.usize                  => some (.call "lean_array_usize")
  | `Array.toList                 => some (.call "lean_array_to_list")
  | `Array.mkArray                => some (.call "lean_mk_array")
  | `Array.mkArray0               => some (.lit "[]")
  -- Nat extras used by Float.ofScientific and array index lowering.
  | `Nat.log2                     => some (.call "lean_nat_log2")
  | `Nat.shiftLeft                => some (.call "lean_nat_shift_left")
  | `Nat.shiftRight               => some (.call "lean_nat_shift_right")
  | `Nat.land                     => some (.call "lean_nat_land")
  | `Nat.lor                      => some (.call "lean_nat_lor")
  | `Nat.xor                      => some (.call "lean_nat_xor")
  -- Int / numeric conversions.
  | `Int.ofNat                    => some (.call "lean_int_of_nat")
  | `Int.toNat                    => some (.call "lean_int_to_nat")
  | `Nat.toUInt8                  => some (.call "lean_uint8_of_nat")
  | `Nat.toUInt16                 => some (.call "lean_uint16_of_nat")
  | `Nat.toUInt32                 => some (.call "lean_uint32_of_nat2")
  | `Nat.toUInt64                 => some (.call "lean_uint64_of_nat")
  | `Nat.toUSize                  => some (.call "lean_usize_of_nat")
  | `UInt64.toFloat               => some (.call "lean_uint64_to_float")
  | `UInt32.toFloat               => some (.call "lean_uint32_to_float")
  -- IO / ST.Ref / streams / process. The World/void arg is dropped by the
  -- emitter (filtered params), so these take only their runtime args.
  | `IO.getStdout                 => some (.call "lean_get_stdout")
  | `IO.getStderr                 => some (.call "lean_get_stderr")
  | `IO.getStdin                  => some (.call "lean_get_stdin")
  | `IO.setStdout                 => some (.call "lean_get_set_stdout")
  | `IO.setStderr                 => some (.call "lean_get_set_stderr")
  | `IO.setStdin                  => some (.call "lean_get_set_stdin")
  | `IO.eprint                    => some (.call "lean_io_eprint")
  | `IO.eprintln                  => some (.call "lean_io_eprintln")
  | `IO.getEnv                    => some (.call "lean_io_getenv")
  | `IO.Process.exit              => some (.call "lean_io_exit")
  | `IO.Process.Prim.exit         => some (.call "lean_io_exit")
  | `ST.Prim.mkRef                => some (.call "lean_st_mk_ref")
  | `ST.Prim.Ref.get              => some (.call "lean_st_ref_get")
  | `ST.Prim.Ref.set              => some (.call "lean_st_ref_set")
  | `ST.Prim.Ref.swap             => some (.call "lean_st_ref_swap")
  | `ST.Prim.Ref.take             => some (.call "lean_st_ref_take")
  | `ST.Prim.Ref.ptrEq            => some (.call "lean_st_ref_ptr_eq")
  | `IO.FS.Handle.mk              => some (.call "lean_io_prim_handle_mk")
  | `IO.FS.Handle.putStr          => some (.call "lean_io_prim_handle_put_str")
  | `IO.FS.Handle.write           => some (.call "lean_io_prim_handle_write")
  | `IO.FS.Handle.read            => some (.call "lean_io_prim_handle_read")
  | `IO.FS.Handle.flush           => some (.call "lean_io_prim_handle_flush")
  | `IO.FS.Handle.isTty           => some (.call "lean_io_prim_handle_is_tty")
  -- misc reached by toString / repr / platform width.
  | `Array.mk                     => some (.call "lean_array_mk")
  | `String.ofList                => some (.call "lean_string_mk")
  | `USize.repr                   => some (.call "lean_string_of_usize")
  | `System.Platform.getNumBits   => some (.call "lean_system_platform_nbits")
  | _ => none

def ctorLit (i : CtorInfo) (ys : Array Arg) : EmitM String := do
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then
    -- nullary ctor / enum: mirror lean_box(cidx)
    return s!"{i.cidx}"
  -- mirror lean_alloc_ctor: object pointers and USize slots live in `fields`
  -- (word-indexed); packed scalars in a byte-addressed DataView `sdata`.
  -- Only the object args are passed positionally (emitCtorSetArgs); USize and
  -- scalar fields are filled by separate uset/sset.
  let args := (#[s!"{i.cidx}", s!"{i.size}", s!"{i.usize}", s!"{i.ssize}"] ++ ys.map argToJs).toList
  return s!"{← sym "lean_ctor"}({", ".intercalate args})"

/-- The runtime get/set suffix used by `lean_ctor_get_*` / `lean_ctor_set_*`
    for region S (sproj/sset). -/
def sscalarSuffix : IRType → String
  | .uint8   => "u8"
  | .uint16  => "u16"
  | .uint32  => "u32"
  | .uint64  => "u64"
  | .usize   => "usize"   -- width follows WORD_BITS (runtime), not a literal 64
  | .float   => "f64"
  | .float32 => "f32"
  | _        => "u8"

/-- The args a direct call to `c` passes: those at the positions of `c`'s live
    params, or every non-erased arg when `c` was not collected. -/
def liveArgs (masks : Std.HashMap Name (Array Bool)) (c : FunId) (ys : Array Arg) : Array Arg :=
  match masks[c]? with
  | some m => (ys.zip m).filterMap fun (y, keep) => if keep then some y else none
  | none => ys.filter fun y => match y with | .erased => false | _ => true

/-- A direct call of `c`. Explicit arms win, then an extern's runtime function,
    then a collected function; an init-backed value global is a mutable slot,
    referenced bare (no `()`), exactly as EmitC reads the C global directly. -/
def emitFap (ty : IRType) (c : FunId) (ys : Array Arg) : EmitM String := do
  let st ← get
  if st.initGlobals.contains c && ys.isEmpty then
    return coerce ty (← ref (funRef c))
  let args := argsToJs (liveArgs st.masks c ys)
  match knownFap c with
  | some (.lit js) => return js
  | some (.call s) => return s!"{← sym s}({args})"
  | none =>
    if let some s := st.externMap[c]? then return s!"{← sym s}({args})"
    if st.fdecls.contains c then return s!"{← ref (funRef c)}({args})"
    addError s!"{c}: no IR and no runtime function"
    return "undefined"

/-- Is a `vdecl` of this expression worth emitting when its variable is unused? -/
def isEffectful (st : EmitState) : IR.Expr → Bool
  | .fap c ys => !(st.initGlobals.contains c && ys.isEmpty) && !(match knownFap c with | some (.lit _) => true | _ => false)
  | .ap .. => true
  | _ => false

/-- Emit an expression. `ty` is the declared IR type of the binding, used to
    pick the JS representation of a numeric literal (scalar `u8`/`u16`/`u32`/
    `float` are plain JS numbers; `u64`/`usize` and object `Nat` literals are
    `bigint`) and to narrow `Obj`-typed results to scalar bindings. -/
def emitExpr (ty : IRType) : IR.Expr → EmitM String
  | .ctor i ys      => ctorLit i ys
  | .reset _ _      => pure "null"          -- GC: reuse token unused
  | .reuse _ i _ ys => ctorLit i ys         -- GC: identical to a fresh ctor
  | .proj i x       => do return coerce ty s!"{← sym "lean_ctor_get"}({varName x}, {i})"
  | .uproj i x      => do return s!"{← sym "lean_ctor_uget"}({varName x}, {i})"
  | .sproj _ offset x => do return s!"{← sym s!"lean_ctor_get_{sscalarSuffix ty}"}({varName x}, {offset})"
  | .fap c ys       => emitFap ty c ys
  | .pap c ys       => do
    let st ← get
    let args := argsToJs ys
    let closure ← sym "lean_closure"
    -- Record the worker's FULL arity so `lean_apply` can branch exact/under/over.
    match st.arityMap[c]? with
    | some n =>
      let fnRef ← ref (if st.cores.contains c then tcRef c else funRef c)
      return s!"{closure}({fnRef}, {n}, [{args}])"
    | none =>
      let arity := match st.masks[c]? with
        | some m => toString (m.filter id).size
        | none => "-1"
      match knownFap c, st.externMap[c]? with
      | some (.call s), _ | none, some s => return s!"{closure}({← sym s}, {arity}, [{args}])"
      | _, _ =>
        addError s!"{c}: partial application of a function with no IR and no runtime function"
        return "undefined"
  | .ap x ys        => do
    -- Non-tail application: force the result. `lean_apply` returns a thunk for
    -- its final saturating call, so drive it through the trampoline here (the
    -- tail-position `.ap` instead returns the `tc:2` thunk directly, letting
    -- the enclosing core's wrapper unroll the apply chain in constant stack).
    return coerce ty s!"{← sym "lean_trampoline"}({← sym "lean_apply"}({varName x}, [{argsToJs ys}]))"
  | .box _ x        => pure (varName x)     -- GC: identity
  | .unbox x        => pure (coerce ty (varName x))
  | .lit (.num v)   =>
    -- u8/u16/u32/float (and Bool) -> plain number; u64/usize and object Nat ->
    -- bigint, matching the runtime's UInt64/USize (bigint) representation.
    match ty with
    | .uint8 | .uint16 | .uint32 | .float | .float32 => pure s!"{v}"
    | _ => pure s!"{v}n"
  | .lit (.str v)   => pure (quoteString v)
  | .isShared _     => pure "1"
    -- Always report "shared" so the compiler's exclusivity branch takes the
    -- copying path instead of mutating in place; JS references are shared and
    -- there is no refcount, so in-place `set`/`reuse` would corrupt aliases.

/-- Emit a `vdecl`: a typed `const` when the variable is read, the bare
    expression when it is not but has an effect, nothing otherwise. -/
def emitVDecl (x : VarId) (ty : IRType) (e : IR.Expr) : EmitM Unit := do
  let st ← get
  if st.used.contains x.idx then
    line s!"const {varName x}: {tsType ty} = {← emitExpr ty e}"
  else if isEffectful st e then
    line (← emitExpr ty e)

def emitSet (x : VarId) (i : Nat) (y : Arg) : EmitM Unit := do
  line s!"{← sym "lean_ctor_set"}({varName x}, {i}, {argToJs y})"

def emitSetTag (x : VarId) (cidx : Nat) : EmitM Unit := do
  line s!"{← sym "lean_ctor_set_tag"}({varName x}, {cidx})"

def emitUSet (x : VarId) (i : Nat) (y : VarId) : EmitM Unit := do
  line s!"{← sym "lean_ctor_uset"}({varName x}, {i}, {varName y})"

def emitSSet (x : VarId) (offset : Nat) (y : VarId) (ty : IRType) : EmitM Unit := do
  line s!"{← sym s!"lean_ctor_set_{sscalarSuffix ty}"}({varName x}, {offset}, {varName y})"

def emitUnreachable : EmitM Unit := do
  line s!"return {← sym "lean_internal_panic_unreachable"}()"

/-- Bind a join point's read params to the args of a `jmp` that inlines it. -/
def emitJmpParams (xs : Array Param) (ys : Array Arg) : EmitM Unit := do
  let used := (← get).used
  for (p, a) in xs.zip ys do
    if used.contains p.x.idx then
      line s!"const {varName p.x}: {tsType p.ty} = {argToJs a}"

/-- A `switch` over a ctor tag or a scalar. A scalar already switched on by an
    enclosing `case` is narrowed to that case's literal type, so it is rebound
    to a fresh `number` before it is switched on again. -/
def emitCase (x : VarId) (xType : IRType) (alts : Array Alt) (emitAlt : FnBody → EmitM Unit) : EmitM Unit := do
  let st ← get
  let scrut ← if xType.isScalar then
      if st.switched.contains x.idx then
        line s!"const s_{x.idx}: {tsType xType} = {varName x}"
        pure s!"s_{x.idx}"
      else pure (varName x)
    else pure s!"{← sym "lean_tag"}({varName x})"
  modify fun st => { st with switched := st.switched.insert x.idx }
  line ("switch (" ++ scrut ++ ") {")
  withIndent do
    let mut sawDefault := false
    for alt in alts do
      match alt with
      | .ctor info b => do
        line ("case " ++ toString info.cidx ++ ": {")
        withIndent (emitAlt b)
        line "}"
      | .default b => do
        sawDefault := true
        line "default: {"
        withIndent (emitAlt b)
        line "}"
    unless sawDefault do
      line "default: {"
      withIndent (line "throw new Error(\"no matching case\")")
      line "}"
  line "}"
  modify fun st' => { st' with switched := st.switched }

/-- Join-point environment: maps a join-point index to its parameters and body,
    so a `jmp` can inline the body (keeping any `continue` lexically inside the
    surrounding loop). -/
abbrev JpEnv := Std.HashMap Nat (Array Param × FnBody)

/-! ## Tail-call detection (strategies A + B)

A tail call lowers to `let r := callee args; <dec/inc/del>*; ret r` possibly
preceded by other straight-line statements. `matchTailCall` looks through the
straight-line prefix and through the trailing refcount no-ops between the call
and the `ret`, returning the callee and its args. Self-tail-calls (callee ==
self) become a loop; cross-function tail calls to a thunk target become
trampoline thunks. -/

/-- Does this body (a chain of `dec/inc/del`) end in `ret (var x)`? -/
partial def retsVar (x : VarId) : FnBody → Bool
  | .ret (.var r) => r == x
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => retsVar x b
  | _ => false

/-- A matched tail call: a direct `.fap` to a named callee (loopable/thunkable
    if the callee has a `__tc` core), or a `.ap` applying a closure value in tail
    position (always emitted as a `tc:2` thunk the wrapper unrolls). -/
inductive TailCall where
  | fap (c : FunId) (args : Array Arg)
  | ap  (x : VarId) (args : Array Arg)

partial def matchTailCall : FnBody → Option TailCall
  | .vdecl x _ (.fap c args) k =>
      if retsVar x k then some (.fap c args) else none
  | .vdecl x _ (.ap fx args) k =>
      if retsVar x k then some (.ap fx args) else none
  | .vdecl _ _ _ b | .set _ _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .setTag _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b =>
      matchTailCall b
  | _ => none

/-- All tail-call callees reachable in a body (across case alts and jdecl
    bodies), used to build the inter-procedural tail-call edge set. -/
partial def tailCallTargets : FnBody → Array FunId
  | b => Id.run do
    let mut acc : Array FunId := #[]
    -- Only direct `.fap` callees join the thunk-target set; a tail `.ap` has no
    -- statically-known callee, so it must not add a name to `computeCoreTargets`
    -- (there is no `__tc` core to point a thunk at). `hasTailAp` handles those.
    match matchTailCall b with
    | some (.fap c _) => acc := acc.push c
    | _ => pure ()
    match b with
    | .case _ _ _ alts => for alt in alts do acc := acc ++ tailCallTargets alt.body
    | .jdecl _ _ v k => acc := acc ++ tailCallTargets v ++ tailCallTargets k
    | .ret _ | .jmp _ _ | .unreachable => pure ()
    | other => unless other.isTerminal do acc := acc ++ tailCallTargets other.body
    return acc

/-- Does the body anywhere self-tail-call (so the self-loop is needed)? -/
partial def hasSelfTailCall (self : FunId) (b : FnBody) : Bool :=
  (tailCallTargets b).any (· == self)

/-- Is there a tail-position `.ap` (closure application) anywhere in the body?
    Such a function needs a `__tc` core + wrapper so the apply-thunk it returns
    gets unrolled by `lean_trampoline`, flattening CPS / continuation loops. -/
partial def hasTailAp : FnBody → Bool
  | b => Id.run do
    match matchTailCall b with
    | some (.ap ..) => return true
    | _ => pure ()
    match b with
    | .case _ _ _ alts => return alts.any (fun alt => hasTailAp alt.body)
    | .jdecl _ _ v k => return hasTailAp v || hasTailAp k
    | .ret _ | .jmp _ _ | .unreachable => return false
    | other => return !other.isTerminal && hasTailAp other.body

/-- The set of callee names a decl's body tail-calls, including itself. -/
def declTailEdges (d : Decl) : Array FunId :=
  match d with
  | .fdecl (body := b) .. => tailCallTargets b
  | .extern .. => #[]

/-! ## Variables the emitted code reads

`no-unused-vars` holds on the generated module, so a binding is emitted only when
something reads it, and an unread param is declared with a `_` prefix. The set
is the least fixed point of "the emitted code of a read (or effectful) binding
reads its operands": a pure binding nobody reads is dropped together with its
operands' reads, and an inlined join point or a self-tail rebind passes an arg
only to params that are read. -/

structure UseCtx where
  st : EmitState
  /-- Loop mode: self-tail calls rebind params. -/
  loop : Bool
  self : FunId
  params : Array Param
  jps : Std.HashMap Nat (Array Param)

def useArg (used : Std.HashSet Nat) : Arg → Std.HashSet Nat
  | .var x => used.insert x.idx
  | .erased => used

def useArgs (used : Std.HashSet Nat) (ys : Array Arg) : Std.HashSet Nat :=
  ys.foldl useArg used

def exprUses (ctx : UseCtx) (used : Std.HashSet Nat) : IR.Expr → Std.HashSet Nat
  | .ctor _ ys | .reuse _ _ _ ys | .pap _ ys => useArgs used ys
  | .reset .. | .lit _ | .isShared _ => used
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x => used.insert x.idx
  | .fap c ys =>
    match knownFap c with
    | some (.lit _) => used
    | _ => useArgs used (liveArgs ctx.st.masks c ys)
  | .ap x ys => useArgs (used.insert x.idx) ys

partial def bodyUses (ctx : UseCtx) (used : Std.HashSet Nat) : FnBody → Std.HashSet Nat
  | .vdecl x _ e k =>
    let selfTail := ctx.loop && retsVar x k && (match e with | .fap c _ => c == ctx.self | _ => false)
    let used :=
      if selfTail then
        match e with
        | .fap _ ys =>
          (ctx.params.zip ys).foldl (fun u (p, y) => if isLive p && used.contains p.x.idx then useArg u y else u) used
        | _ => used
      else if used.contains x.idx || isEffectful ctx.st e || retsVar x k then exprUses ctx used e
      else used
    bodyUses ctx used k
  | .jdecl j xs v k =>
    let ctx' := { ctx with jps := ctx.jps.insert j.idx xs }
    bodyUses ctx' (bodyUses ctx' used v) k
  | .set x _ y k => bodyUses ctx (useArg (used.insert x.idx) y) k
  | .setTag x _ k => bodyUses ctx (used.insert x.idx) k
  | .uset x _ y k | .sset x _ _ y _ k => bodyUses ctx ((used.insert x.idx).insert y.idx) k
  | .inc _ _ _ _ k | .dec _ _ _ _ k | .del _ k => bodyUses ctx used k
  | .case _ x _ alts => alts.foldl (fun u alt => bodyUses ctx u alt.body) (used.insert x.idx)
  | .ret y => useArg used y
  | .jmp j ys =>
    match ctx.jps[j.idx]? with
    | some xs => (xs.zip ys).foldl (fun u (p, y) => if used.contains p.x.idx then useArg u y else u) used
    | none => useArgs used ys
  | .unreachable => used

partial def usedVars (ctx : UseCtx) (b : FnBody) : Std.HashSet Nat := Id.run do
  let mut used : Std.HashSet Nat := {}
  repeat
    let next := bodyUses ctx used b
    if next.size == used.size then break
    used := next
  return used


def paramDecl (used : Std.HashSet Nat) (p : Param) : String :=
  let n := if used.contains p.x.idx then varName p.x else "_" ++ varName p.x
  s!"{n}: {tsType p.ty}"

mutual

/-- `self` is the function being emitted; `scc` is the thunk-target set (names
    that have a `__tc` core). A tail call to `self` loops (`continue`); to any
    thunk target it returns a `{tc}` thunk; to anything else (extern, plain
    leaf) it is a normal returned call. -/
partial def emitFnBodyLoop (self : FunId) (scc : Std.HashSet Name)
    (params : Array Param) (jps : JpEnv) : FnBody → EmitM Unit
  | b => do
    match matchTailCall b with
    | some (.fap c _) =>
      if c == self || scc.contains c then
        emitPrefixThenTail self scc params jps b
      else
        emitNonTail self scc params jps b
    | some (.ap ..) => emitPrefixThenTail self scc params jps b
    | none => emitNonTail self scc params jps b

/-- Emit a body whose head is not a (loopable/thunkable) tail call. -/
partial def emitNonTail (self : FunId) (scc : Std.HashSet Name)
    (params : Array Param) (jps : JpEnv) : FnBody → EmitM Unit
  | .vdecl x ty e k => do
    emitVDecl x ty e
    emitFnBodyLoop self scc params jps k
  | .jdecl j xs v k =>
    emitFnBodyLoop self scc params (jps.insert j.idx (xs, v)) k
  | .set x i y k => do
    emitSet x i y
    emitFnBodyLoop self scc params jps k
  | .setTag x cidx k => do
    emitSetTag x cidx
    emitFnBodyLoop self scc params jps k
  | .uset x i y k => do
    emitUSet x i y
    emitFnBodyLoop self scc params jps k
  | .sset x _ offset y ty k => do
    emitSSet x offset y ty
    emitFnBodyLoop self scc params jps k
  | .inc _ _ _ _ k => emitFnBodyLoop self scc params jps k
  | .dec _ _ _ _ k => emitFnBodyLoop self scc params jps k
  | .del _ k       => emitFnBodyLoop self scc params jps k
  | .ret x => line s!"return {argToJs x}"
  | .jmp j ys => do
    match jps.get? j.idx with
    | some (xs, body) => do
      emitJmpParams xs ys
      emitFnBodyLoop self scc params jps body
    | none => addError s!"jump to an unknown join point {jpName j}"
  | .unreachable => emitUnreachable
  | .case _ x xType alts => emitCase x xType alts (emitFnBodyLoop self scc params jps)

/-- Emit the straight-line prefix of a matched loopable/thunkable tail call,
    then either rebind params + `continue` (self) or return a trampoline thunk
    (other SCC member). -/
partial def emitPrefixThenTail (self : FunId) (scc : Std.HashSet Name)
    (params : Array Param) (jps : JpEnv) : FnBody → EmitM Unit
  | .vdecl x ty (.fap c cargs) k => do
    if retsVar x k then
      if c == self then
        emitTailRebind params cargs
      else
        let st ← get
        let core ← ref (tcRef c)
        line ("return { tc: 1, f: " ++ core ++ ", a: [" ++ argsToJs (liveArgs st.masks c cargs) ++ "] }")
    else
      emitVDecl x ty (.fap c cargs)
      emitFnBodyLoop self scc params jps k
  | .vdecl x ty (.ap fx aargs) k => do
    if retsVar x k then
      -- Tail-position closure application: return a `tc:2` apply-thunk the
      -- wrapper's `lean_trampoline` unrolls, instead of forcing `lean_apply`
      -- here (which would stack a JS frame per CPS / continuation step).
      line ("return { tc: 2, clo: " ++ varName fx ++ ", a: [" ++ argsToJs aargs ++ "] }")
    else
      emitVDecl x ty (.ap fx aargs)
      emitFnBodyLoop self scc params jps k
  | .vdecl x ty e k => do
    emitVDecl x ty e
    emitPrefixThenTail self scc params jps k
  | .set x i y k => do
    emitSet x i y
    emitPrefixThenTail self scc params jps k
  | .setTag x cidx k => do
    emitSetTag x cidx
    emitPrefixThenTail self scc params jps k
  | .uset x i y k => do
    emitUSet x i y
    emitPrefixThenTail self scc params jps k
  | .sset x _ offset y ty k => do
    emitSSet x offset y ty
    emitPrefixThenTail self scc params jps k
  | .inc _ _ _ _ k => emitPrefixThenTail self scc params jps k
  | .dec _ _ _ _ k => emitPrefixThenTail self scc params jps k
  | .del _ k       => emitPrefixThenTail self scc params jps k
  | b => emitNonTail self scc params jps b

partial def emitTailRebind (params : Array Param) (args : Array Arg) : EmitM Unit := do
  -- Only the params that survive as JS function parameters and are read are
  -- rebound: the `void` World token and erased (type/proof) params are dropped
  -- from the function signature, and a param nobody reads keeps no value.
  let used := (← get).used
  let live := (params.zip args).filter (fun (p, _) => isLive p && used.contains p.x.idx)
  -- stage all new values into temporaries first (aliasing safety)
  for (p, a) in live do
    line s!"const t_{p.x.idx}: {tsType p.ty} = {argToJs a}"
  for (p, _) in live do
    line s!"{varName p.x} = t_{p.x.idx}"
  line "continue"

end

/-- Non-loop emitter (no tail call returns a thunk). Join points are inlined at
    each `jmp`, binding their params as `const`s. -/
partial def emitFnBody (jps : JpEnv) : FnBody → EmitM Unit
  | .vdecl x ty e b => do
    emitVDecl x ty e
    emitFnBody jps b
  | .jdecl j xs v b => emitFnBody (jps.insert j.idx (xs, v)) b
  | .set x i y b => do
    emitSet x i y
    emitFnBody jps b
  | .setTag x cidx b => do
    emitSetTag x cidx
    emitFnBody jps b
  | .uset x i y b => do
    emitUSet x i y
    emitFnBody jps b
  | .sset x _ offset y ty b => do
    emitSSet x offset y ty
    emitFnBody jps b
  | .inc _ _ _ _ b => emitFnBody jps b
  | .dec _ _ _ _ b => emitFnBody jps b
  | .del _ b       => emitFnBody jps b
  | .ret x => line s!"return {argToJs x}"
  | .jmp j ys => do
    match jps.get? j.idx with
    | some (xs, body) => do
      emitJmpParams xs ys
      emitFnBody jps body
    | none => addError s!"jump to an unknown join point {jpName j}"
  | .unreachable => emitUnreachable
  | .case _ x xType alts => emitCase x xType alts (emitFnBody jps)

/-! ## Tail-call trampoline targets (strategy A)

A matched tail call to a collected callee `c` returns a `{tc:1, f: tcRef c, a}`
thunk instead of stacking a JS frame; the callee's wrapper drives `lean_trampoline`
to unroll the chain. This covers self-recursion (self edge loops via `continue`),
mutual recursion (each member is a tail target of another), AND acyclic DAG tail
chains (f→g→h, distinct size-1 SCCs), all in constant JS stack. The thunk-target
set is just every function that is the target of some collected tail edge. -/

/-- Names that are the *target* of some collected decl's tail edge (cyclic OR
    acyclic). Every such function gets a `__tc` core so a caller's matched tail
    call can return a `{tc}` thunk naming `tcRef`, and the trampoline unrolls
    the whole chain with no JS stack growth. -/
def computeCoreTargets (decls : Array Decl) : Std.HashSet Name := Id.run do
  -- A thunk target must be emitted as a real function, i.e. a collected
  -- `.fdecl` (NOT an `.extern`, which lowers to a runtime call with no `__tc`
  -- core).
  let names : Std.HashSet Name := decls.foldl (fun s d =>
    match d with | .fdecl .. => s.insert d.name | .extern .. => s) {}
  let mut targets : Std.HashSet Name := {}
  for d in decls do
    for c in (declTailEdges d).filter names.contains do
      targets := targets.insert c
  return targets

/-- A function needs a trampolined core+wrapper iff it is a thunk target, or it
    makes any tail call to a thunk target (so its body returns `{tc}` thunks
    that the wrapper must unroll), or it self-tail-calls (loop). Anything else is
    a plain function with no tail edges in or out of the trampoline. -/
def needsCore (cores : Std.HashSet Name) (d : Decl) : Bool :=
  match d with
  | .fdecl (body := b) .. =>
    cores.contains d.name
      || hasSelfTailCall d.name b
      || (tailCallTargets b).any cores.contains
      || hasTailAp b
  | .extern .. => false

/-- Every name that is emitted with a `__tc` core + wrapper (i.e. `needsCore`).
    A `.pap` over such a worker must store the core (`tcRef`) in the closure, so
    `lean_apply` thunks to the core that the single outer `lean_trampoline`
    unrolls — pointing at the public wrapper instead would nest a fresh
    `lean_trampoline` per applied tail step and re-grow the JS stack. -/
def computeEmittedCores (decls : Array Decl) : Std.HashSet Name := Id.run do
  let targets := computeCoreTargets decls
  let mut acc : Std.HashSet Name := {}
  for d in decls do
    if needsCore targets d then acc := acc.insert d.name
  return acc

/-- One top-level item of the module: its identifier, its source, and the
    function identifiers it references. Items nothing reaches are not emitted. -/
structure Piece where
  name : String
  src : String
  refs : Std.HashSet String

/-- Run `act` into a fresh buffer, returning what it wrote and referenced. -/
def capture (act : EmitM Unit) : EmitM (String × Std.HashSet String) := do
  let st ← get
  set { st with out := "", refs := {} }
  act
  let st' ← get
  set { st' with out := st.out, refs := st.refs }
  return (st'.out, st'.refs)

def piece (name : String) (act : EmitM Unit) : EmitM Piece := do
  let (src, refs) ← capture act
  return { name, src, refs }

/-- Emit a top-level `Decl` as TS functions. `cores` is the set of names that
    have a `__tc` core (thunk targets); a tail call to a member returns a thunk
    and the wrapper drives the trampoline, so cyclic AND acyclic cross-function
    tail chains run in constant JS stack. -/
def emitDeclWith (cores : Std.HashSet Name) (d : Decl) : EmitM (Array Piece) := do
  match d with
  | .fdecl f xs retTy body _ =>
    -- An init-backed value global (`initialize x ← ...`) has a `⊥` IR body and is
    -- never called; emit it as a mutable slot the init thunk assigns, referenced
    -- bare at use sites (the `.fap c []` path checks `initGlobals`).
    if (← get).initGlobals.contains f then
      return #[← piece (funRef f) (line s!"let {funRef f}: Obj = null")]
    let core := needsCore cores d
    let st ← get
    let used := usedVars { st, loop := core && hasSelfTailCall f body, self := f, params := xs, jps := {} } body
    modify fun st => { st with used }
    let live := xs.filter isLive
    let retTs := tsType retTy
    if core then
      -- trampolined core: tail edges to any core target return thunks; self
      -- edges loop (`continue`); the wrapper unrolls returned thunks.
      let corePiece ← piece (tcRef f) do
        line ("function " ++ tcRef f ++ "(" ++ ", ".intercalate (live.toList.map (paramDecl used)) ++ "): " ++ retTs ++ " | L.Bounce {")
        withIndent do
          if hasSelfTailCall f body then
            line "for (;;) {"
            withIndent (emitFnBodyLoop f cores xs {} body)
            line "}"
          else
            emitFnBodyLoop f cores xs {} body
        line "}"
      -- the wrapper drives the trampoline
      let wrapperPiece ← piece (funRef f) do
        let names := ", ".intercalate (live.toList.map (varName ·.x))
        let decls := ", ".intercalate (live.toList.map fun p => s!"{varName p.x}: {tsType p.ty}")
        line ("function " ++ funRef f ++ "(" ++ decls ++ "): " ++ retTs ++ " {")
        withIndent do
          let call := s!"{← sym "lean_trampoline"}({← ref (tcRef f)}({names}))"
          line s!"return {coerce retTy call}"
        line "}"
      return #[corePiece, wrapperPiece]
    else
      return #[← piece (funRef f) do
        line ("function " ++ funRef f ++ "(" ++ ", ".intercalate (live.toList.map (paramDecl used)) ++ "): " ++ retTs ++ " {")
        withIndent (emitFnBody {} body)
        line "}"]
  | .extern .. => return #[]

/-! ## Transitive declaration collection (strategy A) -/

def collectExprDeps (e : IR.Expr) (acc : Array Name) : Array Name :=
  match e with
  | .fap c _ | .pap c _ => acc.push c
  | _ => acc

partial def collectBodyDeps (b : IR.FnBody) (acc : Array Name) : Array Name := Id.run do
  let mut acc := acc
  let mut b := b
  repeat
    match b with
    | .vdecl _ _ e b2 => acc := collectExprDeps e acc; b := b2
    | .jdecl _ _ v b2 => acc := collectBodyDeps v acc; b := b2
    | .case _ _ _ alts =>
        for alt in alts do acc := collectBodyDeps alt.body acc
        return acc
    | .jmp _ _ | .ret _ | .unreachable => return acc
    | other => b := other.body
  return acc

/-- Worklist DFS over `findEnvDecl`, returning all reachable decls in
    callee-before-caller order. `none` from `findEnvDecl` (builtins like
    Nat.rec) is the boundary; externs are included (their names map to the
    runtime). -/
partial def collectTransitive (env : Environment) (roots : Array Name) (subst : Std.HashMap Name Name := {}) : Array Decl := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array Name := roots
  repeat
    match stack.back? with
    | none => break
    | some n =>
      stack := stack.pop
      if visited.contains n then continue
      match (findEnvDecl env n).map (substDecl subst) with
      | none => visited := visited.insert n
      | some d =>
        visited := visited.insert n
        order := order.push n
        match d with
        | .fdecl (body := b) .. =>
            for dep in collectBodyDeps b #[] do
              unless visited.contains dep do stack := stack.push dep
        | .extern .. => pure ()
  -- order is roots-first (caller-before-callee); reverse for callee-first.
  let mut decls : Array Decl := #[]
  for n in order.reverse do
    match (findEnvDecl env n).map (substDecl subst) with
    | some d => decls := decls.push d
    | none   => pure ()
  return decls

/-! ## Program entry (analogue of EmitC `emitMainFnIfNeeded` / `emitMainFn`)

A runnable program defines `main`. We mirror EmitC's decisions: branch on IR
arity (the `void` World param is one of the params, so arity 1 = `IO X`, arity
2 = `List String → IO X`), and inspect the Lean-level `IO` result type for the
exit-code expression (`UInt32` → numeric code, else `Unit`/other → 0). The
generated tail calls `lean_run_main`, which threads the world and unwraps the
io_result exactly like the C `main`. -/

/-- IR arity of `main` counting all params (the `void` World token is a real IR
    param here). EmitC accepts arity 1 (`IO X`) or 2 (`List String → IO X`). -/
def mainHasArgs (d : Decl) : Bool := d.params.size ≥ 2

/-- Is `main`'s `IO` result type `UInt32`? Recovered from the Lean-level type
    `... → IO X` by stripping binders and taking the `X` in `IO X`, mirroring
    EmitC's `retTy.getForallBody.appArg!` then `constName? == some ``UInt32``. -/
def mainRetIsUInt32 (env : Environment) (mainName : Name) : Bool :=
  match env.find? mainName with
  | some ci =>
    match ci.type.getForallBody.appArg!.constName? with
    | some n => n == ``UInt32
    | none   => false
  | none => false

/-- Register init thunks for every reached decl carrying an `@[init]` /
    `initialize` init fn (analogue of `EmitC.emitDeclInit`). Each thunk runs the
    init action (the init fn is a separately-collected decl emitted as
    `funRef initFn`) and assigns its io_result value to the decl's global, then
    returns the io_result so `lean_run_init` can short-circuit on error. Builtin
    inits (`isIOUnitBuiltinInitFn`) are skipped — they configure the compiler
    environment, not the runtime program, exactly as EmitC guards them behind
    `if (builtin)`. -/
def emitInitRegistrations (env : Environment) (initNames : Array Name) : EmitM Unit := do
  -- `initNames` is in declaration order; `lean_run_init` runs thunks in
  -- registration order, matching Lean's per-module declaration-order init chain.
  for n in initNames do
    -- skip pure builtin (compiler-time) inits; only runtime program inits run
    if isIOUnitBuiltinInitFn env n then
      pure ()
    -- EmitC branch order: `isIOUnitInitFn` FIRST. A bare `@[init]` action (the
    -- decl IS the init fn, `getInitFnNameFor? = none`) runs for effect.
    else if isIOUnitInitFn env n then
      line s!"{← sym "lean_register_init"}(() => {← ref (funRef n)}())"
    -- A value global with a separate init fn: run it and bind the io_result value
    -- to the global slot (assignment, not a call).
    else
      match getInitFnNameFor? env n with
      | some initFn =>
        line s!"{← sym "lean_register_init"}(() => \{"
        withIndent do
          line s!"const r: Obj = {← ref (funRef initFn)}()"
          line s!"if ({← sym "lean_io_result_is_ok"}(r)) \{"
          withIndent (line s!"{← ref (funRef n)} = {← sym "lean_io_result_get_value"}(r)")
          line "}"
          line "return r"
        line "})"
      | none => pure ()

/-- Init decls to add to a program's collection beyond what `main` reaches: every
    regular (non-builtin) init action / init-fn-backed global declared in the same
    module as `mainName`. EmitC iterates ALL module decls for init; we scope to the
    program's module so stdlib `builtin_initialize`s are not pulled in. Returns the
    extra roots to collect (init actions + the init fns of value globals), the
    set of value-global names (emitted as mutable slots, referenced bare), and the
    init decls in declaration order. -/
def collectInitDecls (env : Environment) (mainName : Name)
    : Array Name × Std.HashSet Name × Array Name := Id.run do
  let some progMod := env.getModuleIdxFor? mainName | (#[], {}, #[])
  -- The regular `@[init]`/`initialize` attribute records one entry per init decl
  -- in the module: `(declName, initFn)` for a value global, `(declName, anon)` for
  -- a bare `@[init]` action. `getDecls` only lists current-compilation decls, so
  -- imported init metadata is read from the attribute's module entries (in
  -- declaration order, which drives the init-chain run order).
  let entries := regularInitAttr.ext.getModuleEntries env progMod
  let mut roots : Array Name := #[]
  let mut globals : Std.HashSet Name := {}
  let mut initNames : Array Name := #[]
  for (n, initFn) in entries do
    initNames := initNames.push n
    roots := roots.push n
    unless initFn == Name.anonymous do
      roots := roots.push initFn
      globals := globals.insert n
  return (roots, globals, initNames)

/-- A generated module: its body (after the imports), the number of functions,
    and the runtime functions it needs. -/
structure Rendered where
  body : String
  functions : Nat
  externs : Array String
  tsExterns : Array Decl := #[]
  subst : Std.HashMap Name Name := {}

/-- Render the functions reachable from `roots` (and, for a program, from `main`
    and its module's init decls) as a module body. The roots are exported when `exportRoots`. Fails
    with every unresolved name: an extern with no C symbol and no arm, or a call
    to a function with neither IR nor a runtime function. -/
def renderModule (env : Environment) (roots : Array Name) (main? : Option Name) (exportRoots : Bool := true) :
    Except String Rendered := Id.run do
  let (initRoots, initGlobals, initNames) := match main? with
    | some m => collectInitDecls env m
    | none => (#[], {}, #[])
  let subst := csimpToTs env
  let roots := roots.map fun r => subst.getD r r
  let decls := collectTransitive env (roots ++ main?.toArray ++ initRoots) subst
  let mut tsExterns : Array Decl := #[]
  let mut errors : Array String := #[]
  for r in roots ++ main?.toArray do
    if (findEnvDecl env r).isNone then errors := errors.push s!"{r}: no IR (not a compiled definition)"
  let mut externMap : Std.HashMap Name String := {}
  let mut required : Std.HashSet String := {}
  let mut arityMap : Std.HashMap Name Nat := {}
  let mut masks : Std.HashMap Name (Array Bool) := {}
  let mut fdecls : Std.HashSet Name := {}
  for d in decls do
    masks := masks.insert d.name (d.params.map isLive)
    match d with
    | .fdecl f xs .. =>
      fdecls := fdecls.insert f
      arityMap := arityMap.insert f (xs.filter isLive).size
    | .extern f .. =>
      if (tsExternTarget env f).isSome then
        fdecls := fdecls.insert f
        arityMap := arityMap.insert f (d.params.filter isLive).size
        tsExterns := tsExterns.push d
        continue
      match knownFap f, externSymbol env f with
      | some (.call s), _ => required := required.insert s
      | some (.lit _), _ => pure ()
      | none, some s =>
        externMap := externMap.insert f s
        required := required.insert s
      | none, none => errors := errors.push s!"{f}: extern with no C symbol (adhoc/inline/opaque)"
  let cores := computeCoreTargets decls
  let act : EmitM (Array Piece × Array Piece) := do
    let mut pieces := #[]
    for d in decls do
      pieces := pieces ++ (← emitDeclWith cores d)
    let mut entry := #[]
    if !initNames.isEmpty then
      entry := entry.push (← piece "" (emitInitRegistrations env initNames))
    if let some m := main? then
      if let some d := decls.find? (·.name == m) then
        let hasArgs := if mainHasArgs d then "true" else "false"
        let retU32 := if mainRetIsUInt32 env m then "true" else "false"
        entry := entry.push (← piece "" do line s!"{← sym "lean_run_main"}({← ref (funRef m)}, {hasArgs}, {retU32})")
    return (pieces, entry)
  let ((pieces, entry), st) := act.run
    { externMap, arityMap, masks, fdecls, initGlobals, cores := computeEmittedCores decls }
  errors := errors ++ st.errors
  if !errors.isEmpty then
    return .error ("unresolved names:\n" ++ "\n".intercalate (errors.toList.map ("  " ++ ·)))
  -- Keep the pieces reachable from the roots, the program entry and init chain.
  let rootRefs : Std.HashSet String := roots.foldl (fun s r => s.insert (funRef r)) {}
  let exported : Std.HashSet String := if exportRoots then rootRefs else {}
  let byName : Std.HashMap String Piece := pieces.foldl (fun m p => m.insert p.name p) {}
  let mut live : Std.HashSet String := {}
  let mut stack : Array String := rootRefs.toArray ++ entry.foldl (fun a p => a ++ p.refs.toArray) #[]
  repeat
    match stack.back? with
    | none => break
    | some n =>
      stack := stack.pop
      if live.contains n then continue
      live := live.insert n
      if let some p := byName[n]? then stack := stack ++ p.refs.toArray
  let mut body := ""
  let mut functions := 0
  for p in pieces do
    if live.contains p.name then
      functions := functions + 1
      body := body ++ (if exported.contains p.name then "export " ++ p.src else p.src) ++ "\n"
  for p in entry do
    body := body ++ p.src
  let externs := (required.fold (fun s x => s.insert x) st.syms).toArray.qsort (· < ·)
  return .ok { body, functions, externs, tsExterns, subst }

end LeanTs
