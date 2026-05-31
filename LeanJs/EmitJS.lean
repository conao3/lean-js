import Lean.Compiler.IR

/-! # lean-js: a Lean IR -> TypeScript backend (PoC), mirroring EmitC.

We obtain IR `Decl`s via `Lean.IR.findEnvDecl`, then walk `FnBody`/`Expr`
and emit TypeScript. Reference-counting nodes (inc/dec/del/reset/reuse) are
omitted because the JS engine has a tracing GC. -/

open Lean Lean.IR

namespace LeanJs

/-- Emission state: a buffer of output lines and an indent level. -/
structure EmitState where
  out    : String := ""
  indent : Nat    := 0

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

/-- TS function reference for an arbitrary FunId: dots become `_`. -/
def funRef (c : FunId) : String :=
  (toString c).replace "." "_"

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

/-- Map a Lean extern/builtin FunId to a TS runtime call.
    Most map to a named prelude function; a few Nat ops are inlined to
    keep total semantics (truncated sub, div/mod by zero -> 0/lhs). -/
def emitKnownFap (c : FunId) (ys : Array Arg) : Option String :=
  let a := ys.map argToJs
  let bin (op : String) : Option String :=
    if h : a.size = 2 then some s!"({a[0]} {op} {a[1]})" else none
  let call (fn : String) : Option String :=
    some s!"{fn}({String.intercalate ", " a.toList})"
  match c with
  -- Nat: inline the total-arithmetic ops.
  | `Nat.add => bin "+"
  | `Nat.mul => bin "*"
  | `Nat.sub =>
    if h : a.size = 2 then some s!"({a[0]} > {a[1]} ? {a[0]} - {a[1]} : 0n)" else none
  | `Nat.div =>
    if h : a.size = 2 then some s!"({a[1]} === 0n ? 0n : {a[0]} / {a[1]})" else none
  | `Nat.mod =>
    if h : a.size = 2 then some s!"({a[1]} === 0n ? {a[0]} : {a[0]} % {a[1]})" else none
  | `Nat.pow      => call "lean_nat_pow"
  | `Nat.gcd      => call "lean_nat_gcd"
  | `Nat.pred     => call "lean_nat_pred"
  | `Nat.decEq    => call "lean_nat_dec_eq"
  | `Nat.decLt    => call "lean_nat_dec_lt"
  | `Nat.decLe    => call "lean_nat_dec_le"
  | `Nat.beq      => call "lean_nat_dec_eq"
  | `Nat.ble      => call "lean_nat_dec_le"
  | `Nat.blt      => call "lean_nat_dec_lt"
  -- Int
  | `Int.neg      => call "lean_int_neg"
  | `Int.add      => bin "+"
  | `Int.sub      => bin "-"
  | `Int.mul      => bin "*"
  | `Int.div      => call "lean_int_div"
  | `Int.mod      => call "lean_int_mod"
  | `Int.ediv     => call "lean_int_ediv"
  | `Int.emod     => call "lean_int_emod"
  | `Int.decEq    => call "lean_int_dec_eq"
  | `Int.decLt    => call "lean_int_dec_lt"
  | `Int.decLe    => call "lean_int_dec_le"
  -- String
  | `String.length    => call "lean_string_length"
  | `String.append    => call "lean_string_append"
  | `String.push      => call "lean_string_push"
  | `String.decEq     => call "lean_string_dec_eq"
  | `String.data      => call "lean_string_data"
  | `String.toList    => call "lean_string_data"
  | `String.mk        => call "lean_string_mk"
  | `String.isEmpty   => call "lean_string_isempty"
  | `String.hash      => call "lean_string_hash"
  -- String: UTF-8 byte-position layer (Pos == byte offset).
  | `String.utf8ByteSize => call "lean_string_utf8_byte_size"
  | `String.get       => call "lean_string_utf8_get"
  | `String.get!      => call "lean_string_utf8_get_bang"
  | `String.get?      => call "lean_string_utf8_get_opt"
  | `String.next      => call "lean_string_utf8_next"
  | `String.prev      => call "lean_string_utf8_prev"
  | `String.atEnd     => call "lean_string_utf8_at_end"
  | `String.extract   => call "lean_string_utf8_extract"
  | `String.Pos.Raw.extract => call "lean_string_utf8_extract"
  | `String.Pos.Raw.get => call "lean_string_utf8_get"
  | `String.Pos.Raw.next => call "lean_string_utf8_next"
  | `String.Pos.Raw.prev => call "lean_string_utf8_prev"
  | `String.posOf     => call "lean_string_utf8_pos_of"
  | `String.contains  => call "lean_string_contains"
  -- UIntN / USize: map to the wrapping prelude ops (see prelude.ts).
  | `UInt8.add => call "lean_uint8_add" | `UInt8.sub => call "lean_uint8_sub"
  | `UInt8.mul => call "lean_uint8_mul" | `UInt8.div => call "lean_uint8_div"
  | `UInt8.mod => call "lean_uint8_mod" | `UInt8.land => call "lean_uint8_land"
  | `UInt8.lor => call "lean_uint8_lor" | `UInt8.xor => call "lean_uint8_xor"
  | `UInt8.complement => call "lean_uint8_complement"
  | `UInt8.shiftLeft => call "lean_uint8_shift_left" | `UInt8.shiftRight => call "lean_uint8_shift_right"
  | `UInt8.decEq => call "lean_uint8_dec_eq" | `UInt8.decLt => call "lean_uint8_dec_lt"
  | `UInt8.decLe => call "lean_uint8_dec_le" | `UInt8.toNat => call "lean_uint8_to_nat"
  | `UInt8.ofNat => call "lean_uint8_of_nat" | `UInt8.ofNatLF => call "lean_uint8_of_nat"
  | `UInt16.add => call "lean_uint16_add" | `UInt16.sub => call "lean_uint16_sub"
  | `UInt16.mul => call "lean_uint16_mul" | `UInt16.div => call "lean_uint16_div"
  | `UInt16.mod => call "lean_uint16_mod" | `UInt16.land => call "lean_uint16_land"
  | `UInt16.lor => call "lean_uint16_lor" | `UInt16.xor => call "lean_uint16_xor"
  | `UInt16.complement => call "lean_uint16_complement"
  | `UInt16.shiftLeft => call "lean_uint16_shift_left" | `UInt16.shiftRight => call "lean_uint16_shift_right"
  | `UInt16.decEq => call "lean_uint16_dec_eq" | `UInt16.decLt => call "lean_uint16_dec_lt"
  | `UInt16.decLe => call "lean_uint16_dec_le" | `UInt16.toNat => call "lean_uint16_to_nat"
  | `UInt16.ofNat => call "lean_uint16_of_nat" | `UInt16.ofNatLF => call "lean_uint16_of_nat"
  | `UInt32.add => call "lean_uint32_add" | `UInt32.sub => call "lean_uint32_sub"
  | `UInt32.mul => call "lean_uint32_mul" | `UInt32.div => call "lean_uint32_div"
  | `UInt32.mod => call "lean_uint32_mod" | `UInt32.land => call "lean_uint32_land"
  | `UInt32.lor => call "lean_uint32_lor" | `UInt32.xor => call "lean_uint32_xor"
  | `UInt32.complement => call "lean_uint32_complement"
  | `UInt32.shiftLeft => call "lean_uint32_shift_left" | `UInt32.shiftRight => call "lean_uint32_shift_right"
  | `UInt32.decEq => call "lean_uint32_dec_eq" | `UInt32.decLt => call "lean_uint32_dec_lt"
  | `UInt32.decLe => call "lean_uint32_dec_le" | `UInt32.toNat => call "lean_uint32_to_nat"
  | `UInt32.ofNat => call "lean_uint32_of_nat" | `UInt32.ofNatLF => call "lean_uint32_of_nat"
  | `UInt64.add => call "lean_uint64_add" | `UInt64.sub => call "lean_uint64_sub"
  | `UInt64.mul => call "lean_uint64_mul" | `UInt64.div => call "lean_uint64_div"
  | `UInt64.mod => call "lean_uint64_mod" | `UInt64.land => call "lean_uint64_land"
  | `UInt64.lor => call "lean_uint64_lor" | `UInt64.xor => call "lean_uint64_xor"
  | `UInt64.complement => call "lean_uint64_complement"
  | `UInt64.shiftLeft => call "lean_uint64_shift_left" | `UInt64.shiftRight => call "lean_uint64_shift_right"
  | `UInt64.decEq => call "lean_uint64_dec_eq" | `UInt64.decLt => call "lean_uint64_dec_lt"
  | `UInt64.decLe => call "lean_uint64_dec_le" | `UInt64.toNat => call "lean_uint64_to_nat"
  | `UInt64.ofNat => call "lean_uint64_of_nat" | `UInt64.ofNatLF => call "lean_uint64_of_nat"
  | `USize.add => call "lean_usize_add" | `USize.sub => call "lean_usize_sub"
  | `USize.mul => call "lean_usize_mul" | `USize.div => call "lean_usize_div"
  | `USize.mod => call "lean_usize_mod" | `USize.land => call "lean_usize_land"
  | `USize.lor => call "lean_usize_lor" | `USize.xor => call "lean_usize_xor"
  | `USize.complement => call "lean_usize_complement"
  | `USize.shiftLeft => call "lean_usize_shift_left" | `USize.shiftRight => call "lean_usize_shift_right"
  | `USize.decEq => call "lean_usize_dec_eq" | `USize.decLt => call "lean_usize_dec_lt"
  | `USize.decLe => call "lean_usize_dec_le" | `USize.toNat => call "lean_usize_to_nat"
  | `USize.ofNat => call "lean_usize_of_nat" | `USize.ofNatLF => call "lean_usize_of_nat"
  -- Float / Float32
  | `Float.add => call "lean_float_add" | `Float.sub => call "lean_float_sub"
  | `Float.mul => call "lean_float_mul" | `Float.div => call "lean_float_div"
  | `Float.neg => call "lean_float_negate"
  | `Float.beq => call "lean_float_beq" | `Float.decLt => call "lean_float_decLt"
  | `Float.decLe => call "lean_float_decLe"
  | `Float.isNaN => call "lean_float_isnan" | `Float.isFinite => call "lean_float_isfinite"
  | `Float.isInf => call "lean_float_isinf"
  | `Float.sqrt => call "lean_float_sqrt" | `Float.sin => call "lean_float_sin"
  | `Float.cos => call "lean_float_cos" | `Float.exp => call "lean_float_exp"
  | `Float.log => call "lean_float_log" | `Float.pow => call "lean_float_pow"
  | `Float.floor => call "lean_float_floor" | `Float.ceil => call "lean_float_ceil"
  | `Float.abs => call "lean_float_abs" | `Float.round => call "lean_float_round"
  | `Float.toUInt8 => call "lean_float_to_uint8" | `Float.toUInt16 => call "lean_float_to_uint16"
  | `Float.toUInt32 => call "lean_float_to_uint32" | `Float.toUInt64 => call "lean_float_to_uint64"
  | `Float.toUSize => call "lean_float_to_usize"
  | `Float.toFloat32 => call "lean_float_to_float32"
  | `Float.ofScientific => call "lean_float_of_scientific"
  | `Float32.add => call "lean_float32_add" | `Float32.sub => call "lean_float32_sub"
  | `Float32.mul => call "lean_float32_mul" | `Float32.div => call "lean_float32_div"
  | `Float32.neg => call "lean_float32_negate"
  | `Float32.beq => call "lean_float32_beq" | `Float32.decLt => call "lean_float32_decLt"
  | `Float32.decLe => call "lean_float32_decLe"
  | `Float32.toFloat => call "lean_float32_to_float"
  | `Float32.sqrt => call "lean_float32_sqrt" | `Float32.abs => call "lean_float32_abs"
  -- Char
  | `Char.ofNat       => call "lean_uint32_of_nat"
  | `Char.toNat       => call "lean_char_to_nat"
  -- Array
  | `Array.empty                  => some "[]"
  | `Array.mkEmpty                => some "[]"
  | `Array.emptyWithCapacity      => some "[]"
  | `Array.size                   => call "lean_array_get_size"
  | `Array.get!                   => call "lean_array_get"
  | `Array.getD                   => call "lean_array_get"
  | `Array.get                    => call "lean_array_fget"
  | `Array.set                    => call "lean_array_set"
  | `Array.set!                   => call "lean_array_set"
  | `Array.push                   => call "lean_array_push"
  | `Array.pop                    => call "lean_array_pop"
  | `Array.swap                   => call "lean_array_swap"
  | _ => none

def ctorLit (i : CtorInfo) (ys : Array Arg) : String :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then
    -- nullary ctor / enum: mirror lean_box(cidx)
    s!"{i.cidx}"
  else
    -- mirror lean_alloc_ctor: object pointers and USize slots live in `fields`
    -- (word-indexed); packed scalars in a byte-addressed DataView `sdata`.
    -- Only the object args are passed positionally (emitCtorSetArgs); USize and
    -- scalar fields are filled by separate uset/sset.
    let objs := String.intercalate ", " (ys.toList.map argToJs)
    let head := s!"lean_ctor({i.cidx}, {i.size}, {i.usize}, {i.ssize}"
    if objs.isEmpty then s!"{head})" else s!"{head}, {objs})"

/-- Byte width of a packed scalar IRType, and the runtime get/set suffix used
    by `lean_ctor_get_*` / `lean_ctor_set_*` for region S (sproj/sset). -/
def sscalarSuffix : IRType → String
  | .uint8   => "u8"
  | .uint16  => "u16"
  | .uint32  => "u32"
  | .uint64  => "u64"
  | .usize   => "u64"
  | .float   => "f64"
  | .float32 => "f32"
  | _        => "u8"

/-- Byte offset of a scalar field: `sizeof(void*)*n + offset` in C, but in the
    split layout region S starts at its own offset 0, so the word-prefix `n` is
    dropped and only the intra-region byte `offset` is used. -/
def sbyteOffset (_n : Nat) (offset : Nat) : String := toString offset

/-- Emit an expression. `ty` is the declared IR type of the binding, used to
    pick the JS representation of a numeric literal: scalar types (`u8`/`u16`/
    `u32`/`u64`/`usize`) are plain JS numbers, object `Nat` literals are
    `bigint`. -/
def emitExpr (ty : IRType := .object) : IR.Expr → String
  | .ctor i ys      => ctorLit i ys
  | .reset _ _      => "null"          -- GC: reuse token unused
  | .reuse _ i _ ys => ctorLit i ys    -- GC: identical to a fresh ctor
  | .proj i x       => s!"{varName x}.fields[{i}]"
  | .uproj i x      => s!"{varName x}.fields[{i}]"
  | .sproj n offset x => s!"lean_ctor_get_{sscalarSuffix ty}({varName x}, {sbyteOffset n offset})"
  | .fap c ys       =>
    match emitKnownFap c ys with
    | some s => s
    | none   =>
      let args := String.intercalate ", " (ys.toList.map argToJs)
      s!"{funRef c}({args})"
  | .pap c ys       =>
    let args := String.intercalate ", " (ys.toList.map argToJs)
    "{ fn: " ++ funRef c ++ ", args: [" ++ args ++ "] }"
  | .ap x ys        =>
    let args := String.intercalate ", " (ys.toList.map argToJs)
    s!"lean_apply({varName x}, [{args}])"
  | .box _ x        => varName x        -- GC: identity
  | .unbox x        => varName x        -- GC: identity
  | .lit (.num v)   =>
    -- scalar-typed literal (Bool/UInt/USize) -> plain number; obj Nat -> bigint
    if ty.isScalar then s!"{v}" else s!"{v}n"
  | .lit (.str v)   => quoteString v
  | .isShared _     => "1"
    -- Always report "shared" so the compiler's exclusivity branch takes the
    -- copying path instead of mutating in place; JS references are shared and
    -- there is no refcount, so in-place `set`/`reuse` would corrupt aliases.

/-! ## Self-tail-call detection (strategy B)

A self-tail-call lowers to `let r := self args; ret r` possibly preceded by
straight-line statements. `matchSelfTailCall` looks through the straight-line
prefix for that 2-node pattern. -/

partial def matchSelfTailCall (self : FunId) : FnBody → Option (Array Arg)
  | .vdecl x _ (.fap c args) (.ret (.var r)) =>
      if c == self && r == x then some args else none
  | .vdecl _ _ _ b | .set _ _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .setTag _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b =>
      matchSelfTailCall self b
  | _ => none

/-- Does the body anywhere contain a self-tail-call (so we need a loop)? -/
partial def hasSelfTailCall (self : FunId) : FnBody → Bool
  | b =>
    match matchSelfTailCall self b with
    | some _ => true
    | none =>
      match b with
      | .case _ _ _ alts => alts.any (fun alt => hasSelfTailCall self alt.body)
      | .jdecl _ _ v k => hasSelfTailCall self v || hasSelfTailCall self k
      | .ret _ | .jmp _ _ | .unreachable => false
      | other =>
        let k := other.body
        -- avoid infinite loop: `other.body` of a terminal returns itself
        if other.isTerminal then false else hasSelfTailCall self k

/-- Join-point environment for loop mode: maps a join-point index to its
    parameters and body, so a `jmp` can inline the body (keeping any `continue`
    lexically inside the surrounding `while`). -/
abbrev JpEnv := Std.HashMap Nat (Array Param × FnBody)

mutual

partial def emitFnBodyLoop (self : FunId) (params : Array Param) (jps : JpEnv) :
    FnBody → EmitM Unit
  | b => do
    match matchSelfTailCall self b with
    | some args => do
      emitPrefixThenTail self params jps b args
    | none =>
      match b with
      | .vdecl x ty e k => do
        line s!"const {varName x} = {emitExpr ty e};"
        emitFnBodyLoop self params jps k
      | .jdecl j xs v k =>
        -- register the join point for inlining at jmp sites
        emitFnBodyLoop self params (jps.insert j.idx (xs, v)) k
      | .set x i y k => do
        line s!"{varName x}.fields[{i}] = {argToJs y};"
        emitFnBodyLoop self params jps k
      | .setTag x cidx k => do
        line s!"{varName x}.tag = {cidx};"
        emitFnBodyLoop self params jps k
      | .uset x i y k => do
        line s!"{varName x}.fields[{i}] = {varName y};"
        emitFnBodyLoop self params jps k
      | .sset x i offset y ty k => do
        line s!"lean_ctor_set_{sscalarSuffix ty}({varName x}, {sbyteOffset i offset}, {varName y});"
        emitFnBodyLoop self params jps k
      | .inc _ _ _ _ k => emitFnBodyLoop self params jps k
      | .dec _ _ _ _ k => emitFnBodyLoop self params jps k
      | .del _ k       => emitFnBodyLoop self params jps k
      | .ret x => line s!"return {argToJs x};"
      | .jmp j ys => do
        match jps.get? j.idx with
        | some (xs, body) => do
          -- inline: bind JP params to args, then emit the JP body in-place
          for (p, a) in xs.zip ys do
            line s!"const {varName p.x} = {argToJs a};"
          emitFnBodyLoop self params jps body
        | none =>
          let args := String.intercalate ", " (ys.toList.map argToJs)
          line s!"return {jpName j}({args});"
      | .unreachable => line "throw new Error(\"unreachable\");"
      | .case _ x xType alts => do
        let scrut := if xType.isScalar then varName x else s!"lean_tag({varName x})"
        line ("switch (" ++ scrut ++ ") {")
        withIndent do
          let mut sawDefault := false
          for alt in alts do
            match alt with
            | .ctor info b => do
              line ("case " ++ toString info.cidx ++ ": {")
              withIndent (emitFnBodyLoop self params jps b)
              line "}"
            | .default b => do
              sawDefault := true
              line "default: {"
              withIndent (emitFnBodyLoop self params jps b)
              line "}"
          unless sawDefault do
            line "default: { throw new Error(\"no matching case\"); }"
        line "}"

/-- Emit the straight-line prefix of a matched self-tail-call, then the
    param rebind + continue. -/
partial def emitPrefixThenTail (self : FunId) (params : Array Param) (jps : JpEnv) :
    FnBody → Array Arg → EmitM Unit
  | .vdecl x ty (.fap c cargs) (.ret (.var r)), args => do
    if c == self && r == x then
      emitTailRebind params args
    else
      line s!"const {varName x} = {emitExpr ty (.fap c cargs)};"
      pure ()
  | .vdecl x ty e k, args => do
    line s!"const {varName x} = {emitExpr ty e};"
    emitPrefixThenTail self params jps k args
  | .set x i y k, args => do
    line s!"{varName x}.fields[{i}] = {argToJs y};"
    emitPrefixThenTail self params jps k args
  | .setTag x cidx k, args => do
    line s!"{varName x}.tag = {cidx};"
    emitPrefixThenTail self params jps k args
  | .uset x i y k, args => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitPrefixThenTail self params jps k args
  | .sset x i offset y ty k, args => do
    line s!"lean_ctor_set_{sscalarSuffix ty}({varName x}, {sbyteOffset i offset}, {varName y});"
    emitPrefixThenTail self params jps k args
  | .inc _ _ _ _ k, args => emitPrefixThenTail self params jps k args
  | .dec _ _ _ _ k, args => emitPrefixThenTail self params jps k args
  | .del _ k, args       => emitPrefixThenTail self params jps k args
  | _, args => emitTailRebind params args

partial def emitTailRebind (params : Array Param) (args : Array Arg) : EmitM Unit := do
  -- stage all new values into temporaries first (aliasing safety)
  for (p, a) in params.zip args do
    line s!"const __t_{p.x.idx} = {argToJs a};"
  for p in params do
    line s!"{varName p.x} = __t_{p.x.idx};"
  line "continue;"

end

/-- Non-loop emitter (no self-tail-call present). -/
partial def emitFnBody : FnBody → EmitM Unit
  | .vdecl x ty e b => do
    line s!"const {varName x} = {emitExpr ty e};"
    emitFnBody b
  | .jdecl j xs v b => do
    let params := String.intercalate ", " (xs.toList.map (fun p => varName p.x))
    line ("const " ++ jpName j ++ " = (" ++ params ++ ") => {")
    withIndent (emitFnBody v)
    line "};"
    emitFnBody b
  | .set x i y b => do
    line s!"{varName x}.fields[{i}] = {argToJs y};"
    emitFnBody b
  | .setTag x cidx b => do
    line s!"{varName x}.tag = {cidx};"
    emitFnBody b
  | .uset x i y b => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitFnBody b
  | .sset x i offset y ty b => do
    line s!"lean_ctor_set_{sscalarSuffix ty}({varName x}, {sbyteOffset i offset}, {varName y});"
    emitFnBody b
  | .inc _ _ _ _ b => emitFnBody b
  | .dec _ _ _ _ b => emitFnBody b
  | .del _ b       => emitFnBody b
  | .ret x => line s!"return {argToJs x};"
  | .jmp j ys =>
    let args := String.intercalate ", " (ys.toList.map argToJs)
    line s!"return {jpName j}({args});"
  | .unreachable => line "throw new Error(\"unreachable\");"
  | .case _ x xType alts => do
    let scrut := if xType.isScalar then varName x else s!"lean_tag({varName x})"
    line ("switch (" ++ scrut ++ ") {")
    withIndent do
      let mut sawDefault := false
      for alt in alts do
        match alt with
        | .ctor info b => do
          line ("case " ++ toString info.cidx ++ ": {")
          withIndent (emitFnBody b)
          line "}"
        | .default b => do
          sawDefault := true
          line "default: {"
          withIndent (emitFnBody b)
          line "}"
      unless sawDefault do
        line "default: { throw new Error(\"no matching case\"); }"
    line "}"

/-- Emit a top-level `Decl` as a TS function, using the loop emitter when the
    body self-tail-calls. -/
def emitDecl : Decl → EmitM Unit
  | .fdecl f xs _ body _ => do
    let params := xs.toList.filter (fun p => !p.ty.isErased && !p.ty.isVoid)
    let paramStr := String.intercalate ", " (params.map (fun p => varName p.x))
    line ("function " ++ funRef f ++ "(" ++ paramStr ++ ") {")
    withIndent do
      if hasSelfTailCall f body then
        line "while (true) {"
        withIndent (emitFnBodyLoop f xs {} body)
        line "}"
      else
        emitFnBody body
    line "}"
  | .extern f _ _ _ =>
    line s!"// extern {funRef f} -> runtime prelude"

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
    callee-before-caller order (so `function` declarations are defined before
    use; JS hoists function declarations anyway, but this keeps output tidy).
    `none` from `findEnvDecl` (builtins like Nat.rec) is the boundary; externs
    are included (their names map to the prelude). -/
partial def collectTransitive (env : Environment) (roots : Array Name) : Array Decl := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array Name := roots
  repeat
    match stack.back? with
    | none => break
    | some n =>
      stack := stack.pop
      if visited.contains n then continue
      match findEnvDecl env n with
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
    match findEnvDecl env n with
    | some d => decls := decls.push d
    | none   => pure ()
  return decls

/-- Run the emitter over the given decls, returning the produced TS source. -/
def render (decls : Array Decl) : String := Id.run do
  let act : EmitM Unit := do
    for d in decls do
      emitDecl d
      line ""
  let (_, st) := act.run {}
  return st.out

/-- Collect transitively from roots and render a self-contained module body. -/
def renderFromRoots (env : Environment) (roots : Array Name) : String :=
  render (collectTransitive env roots)

end LeanJs
