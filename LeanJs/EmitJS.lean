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
  /-- Extern Lean-name → resolved C symbol map (the link table); read by the
      `.fap` emission path so extern aliases route to their prelude symbol. -/
  externMap : Std.HashMap Name String := {}
  /-- Function name → full JS arity (count of non-erased/non-void params, the
      same params `funRef` declares). Read by the `.pap` emission path so a
      partial application records the worker's arity, letting `lean_apply` do the
      C runtime's three-way exact/under/over dispatch. A name absent from the map
      (extern, or a callee whose decl was not collected) gets no arity and falls
      back to concat-and-call. -/
  arityMap : Std.HashMap Name Nat := {}
  /-- 0-param globals backed by an `initialize ... ← ...` init fn (IR body `⊥`,
      `getInitFnNameFor? = some`). These are emitted as a mutable `let` slot (not
      a `function`), assigned by the init thunk, and referenced WITHOUT `()` at
      `.fap c []` use sites — mirroring EmitC, which emits a C global and assigns
      `lean_io_result_get_value(res)` to it. -/
  initGlobals : Std.HashSet Name := {}
  /-- Names that have a `__tc` core (thunk targets). A `.pap` over such a worker
      records the core (`tcRef`) as the closure's fn, so `lean_apply` returns a
      `__tc` thunk naming the core that the single outer `lean_trampoline` unrolls
      — instead of naming the public wrapper, whose own nested `lean_trampoline`
      would re-grow the JS stack once per tail-`.ap` step. -/
  cores : Std.HashSet Name := {}

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

/-- TS function reference for an arbitrary FunId. Dots become `_`, and any other
    character that is not a valid JS identifier char (`?`, `!`, `'`, Greek/
    subscript hygiene markers, etc. — all legal in Lean names) is escaped to a
    `_uNN_`/`_NNN_` form so the emitted name is always a valid JS identifier.
    Mirrors EmitC's name mangling intent (it has its own scheme); we only need a
    deterministic, collision-free, syntactically-valid encoding. -/
def funRef (c : FunId) : String := Id.run do
  let mut acc := ""
  for ch in (toString c).toList do
    if ch == '.' then acc := acc ++ "_"
    else if (ch.isAlphanum || ch == '_') && ch.toNat < 128 then acc := acc.push ch
    else
      -- escape any other char (incl. non-ASCII) by its code point, bracketed by
      -- `_` so it cannot merge with adjacent digits/letters.
      acc := acc ++ "_x" ++ toString ch.toNat ++ "_"
  return acc

/-- Trampoline core suffix: `funRef` of a thunk-returning core. -/
def tcRef (c : FunId) : String := funRef c ++ "__tc"

/-! ## Extern → prelude-symbol single source of truth (analogue of EmitC)

Rather than hand-keying a table on Lean *decl* names (every `@[extern]` alias —
`USize.ofNat`/`USize.ofNatLT`/`Nat.toUSize` all share the C symbol
`lean_usize_of_nat` — has to be re-listed, and a forgotten alias silently emits a
dangling `funRef` call that ReferenceErrors at runtime), we resolve the actual C
symbol via `Lean.getExternNameFor env `c name`, exactly like `EmitC.toCName`.
The prelude is keyed on that same C symbol, so all aliases route for free.

`externSymbol env c` returns the C symbol for an extern decl `c` (the `standard`
entry's literal string for backend `c`/`all`), or `none` for a non-extern decl
or an extern with no usable C entry (adhoc/inline/opaque). -/
def externSymbol (env : Environment) (c : Name) : Option String :=
  getExternNameFor env `c c

/-- Lean extern *names* that `emitKnownFap` handles with an explicit arm whose JS
    emission does NOT go through a plain `sym(args)` call to the resolved C
    symbol — either an inlined operator (`Nat.add` -> `+`), a literal (`Array.empty`
    -> `[]`), or a prelude name that differs from the C symbol (`Nat.toUInt32` ->
    `lean_uint32_of_nat2`). For these the resolved C symbol may not be in
    `preludeSymbols`, but emission is still correct because the explicit arm wins.
    They are therefore exempt from the fail-loud link check. -/
def emitKnownFapSpecialNames : Std.HashSet Name := Std.HashSet.ofList [
  -- inlined total arithmetic (operators, not calls)
  `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod,
  `Int.add, `Int.sub, `Int.mul,
  -- beq/ble/blt route to the dec_* prelude symbols (name differs from C symbol)
  `Nat.beq, `Nat.ble, `Nat.blt,
  -- name mismatches: C symbol differs from the prelude impl name
  `Nat.toUInt32, `Char.ofNat,
  `Int.ofNat,                     -- C lean_nat_to_int -> prelude lean_int_of_nat
  `Nat.shiftLeft, `Nat.shiftRight,-- C lean_nat_shiftl/r -> lean_nat_shift_left/right
  `Array.usize,                   -- C lean_array_size -> prelude lean_array_usize
  `Array.set, `Array.set!,        -- C lean_array_fset -> prelude lean_array_set (copy)
  -- Array empties lowered to the `[]` literal
  `Array.empty, `Array.mkEmpty, `Array.emptyWithCapacity, `Array.mkArray0,
  -- Float/Float32 libm transcendentals: the resolved C symbol is the BARE libm
  -- name (`tan`, `atan2`, `sinf`, ...), not in `preludeSymbols`; the explicit arm
  -- maps it to a `lean_float*_*` prelude impl, so emission is correct.
  `Float.tan, `Float.asin, `Float.acos, `Float.atan, `Float.atan2,
  `Float.sinh, `Float.cosh, `Float.tanh, `Float.asinh, `Float.acosh, `Float.atanh,
  `Float.exp2, `Float.log2, `Float.log10, `Float.cbrt,
  `Float32.sin, `Float32.cos, `Float32.tan,
  `Float32.asin, `Float32.acos, `Float32.atan, `Float32.atan2,
  `Float32.sinh, `Float32.cosh, `Float32.tanh, `Float32.asinh, `Float32.acosh, `Float32.atanh,
  `Float32.exp, `Float32.exp2, `Float32.log, `Float32.log2, `Float32.log10,
  `Float32.pow, `Float32.cbrt, `Float32.floor, `Float32.ceil, `Float32.round
]

/-- The set of C symbols the runtime prelude (`prelude.ts`) defines. This is the
    "link table": every reached extern's resolved C symbol MUST be in this set or
    extraction fails loudly (the analogue of a C linker resolving symbols),
    converting a runtime node ReferenceError into a build-time hard error.

    Kept as a checked-in list the prelude must satisfy. A few `standard` externs
    resolve to a C symbol whose JS impl lives under a *different* prelude name
    (name mismatches, e.g. `lean_nat_add` is inlined to `+`, never called); those
    are handled by `emitKnownFap` BEFORE the symbol path is consulted, so they do
    not need an entry here. This set lists exactly the symbols emitted as a plain
    `sym(args)` call. -/
def preludeSymbols : Std.HashSet String := Std.HashSet.ofList [
  -- Nat / Int bignum + bitwise
  "lean_nat_pow", "lean_nat_gcd", "lean_nat_log2",
  "lean_nat_shift_left", "lean_nat_shift_right",
  "lean_nat_land", "lean_nat_lor", "lean_nat_xor",
  "lean_int_neg", "lean_int_div", "lean_int_mod", "lean_int_ediv", "lean_int_emod",
  "lean_int_dec_eq", "lean_int_dec_lt", "lean_int_dec_le",
  "lean_int_of_nat", "lean_int_to_nat", "lean_nat_abs",
  "lean_nat_dec_eq", "lean_nat_dec_lt", "lean_nat_dec_le",
  -- UInt / USize
  "lean_uint8_of_nat", "lean_uint16_of_nat", "lean_uint64_of_nat",
  "lean_uint32_of_nat2", "lean_usize_of_nat",
  "lean_uint8_add", "lean_uint8_sub", "lean_uint8_mul", "lean_uint8_div", "lean_uint8_mod",
  "lean_uint8_land", "lean_uint8_lor", "lean_uint8_xor", "lean_uint8_complement",
  "lean_uint8_shift_left", "lean_uint8_shift_right",
  "lean_uint8_dec_eq", "lean_uint8_dec_lt", "lean_uint8_dec_le", "lean_uint8_to_nat",
  "lean_uint16_add", "lean_uint16_sub", "lean_uint16_mul", "lean_uint16_div", "lean_uint16_mod",
  "lean_uint16_land", "lean_uint16_lor", "lean_uint16_xor", "lean_uint16_complement",
  "lean_uint16_shift_left", "lean_uint16_shift_right",
  "lean_uint16_dec_eq", "lean_uint16_dec_lt", "lean_uint16_dec_le", "lean_uint16_to_nat",
  "lean_uint32_add", "lean_uint32_sub", "lean_uint32_mul", "lean_uint32_div", "lean_uint32_mod",
  "lean_uint32_land", "lean_uint32_lor", "lean_uint32_xor", "lean_uint32_complement",
  "lean_uint32_shift_left", "lean_uint32_shift_right",
  "lean_uint32_dec_eq", "lean_uint32_dec_lt", "lean_uint32_dec_le", "lean_uint32_to_nat",
  "lean_uint64_add", "lean_uint64_sub", "lean_uint64_mul", "lean_uint64_div", "lean_uint64_mod",
  "lean_uint64_land", "lean_uint64_lor", "lean_uint64_xor", "lean_uint64_complement",
  "lean_uint64_shift_left", "lean_uint64_shift_right",
  "lean_uint64_dec_eq", "lean_uint64_dec_lt", "lean_uint64_dec_le", "lean_uint64_to_nat",
  "lean_usize_add", "lean_usize_sub", "lean_usize_mul", "lean_usize_div", "lean_usize_mod",
  "lean_usize_land", "lean_usize_lor", "lean_usize_xor", "lean_usize_complement",
  "lean_usize_shift_left", "lean_usize_shift_right",
  "lean_usize_dec_eq", "lean_usize_dec_lt", "lean_usize_dec_le", "lean_usize_to_nat",
  "lean_uint64_to_usize",
  -- signed fixed-width ints
  "lean_int8_of_int", "lean_int8_of_nat", "lean_int8_to_int",
  "lean_int8_add", "lean_int8_sub", "lean_int8_mul", "lean_int8_div", "lean_int8_mod",
  "lean_int8_neg", "lean_int8_land", "lean_int8_lor", "lean_int8_xor", "lean_int8_complement",
  "lean_int8_shift_left", "lean_int8_shift_right",
  "lean_int8_dec_eq", "lean_int8_dec_lt", "lean_int8_dec_le",
  "lean_int16_of_int", "lean_int16_of_nat", "lean_int16_to_int",
  "lean_int16_add", "lean_int16_sub", "lean_int16_mul", "lean_int16_div", "lean_int16_mod",
  "lean_int16_neg", "lean_int16_land", "lean_int16_lor", "lean_int16_xor", "lean_int16_complement",
  "lean_int16_shift_left", "lean_int16_shift_right",
  "lean_int16_dec_eq", "lean_int16_dec_lt", "lean_int16_dec_le",
  "lean_int32_of_int", "lean_int32_of_nat", "lean_int32_to_int",
  "lean_int32_add", "lean_int32_sub", "lean_int32_mul", "lean_int32_div", "lean_int32_mod",
  "lean_int32_neg", "lean_int32_land", "lean_int32_lor", "lean_int32_xor", "lean_int32_complement",
  "lean_int32_shift_left", "lean_int32_shift_right",
  "lean_int32_dec_eq", "lean_int32_dec_lt", "lean_int32_dec_le",
  "lean_int64_of_int", "lean_int64_of_nat", "lean_int64_to_int_sint",
  "lean_int64_add", "lean_int64_sub", "lean_int64_mul", "lean_int64_div", "lean_int64_mod",
  "lean_int64_neg", "lean_int64_land", "lean_int64_lor", "lean_int64_xor", "lean_int64_complement",
  "lean_int64_shift_left", "lean_int64_shift_right",
  "lean_int64_dec_eq", "lean_int64_dec_lt", "lean_int64_dec_le",
  "lean_isize_of_int", "lean_isize_of_nat", "lean_isize_to_int_sint",
  "lean_isize_add", "lean_isize_sub", "lean_isize_mul", "lean_isize_div", "lean_isize_mod",
  "lean_isize_neg", "lean_isize_land", "lean_isize_lor", "lean_isize_xor", "lean_isize_complement",
  "lean_isize_shift_left", "lean_isize_shift_right",
  "lean_isize_dec_eq", "lean_isize_dec_lt", "lean_isize_dec_le",
  -- Float / Float32
  "lean_float_add", "lean_float_sub", "lean_float_mul", "lean_float_div", "lean_float_negate",
  "lean_float_beq", "lean_float_decLt", "lean_float_decLe",
  "lean_float_isnan", "lean_float_isfinite", "lean_float_isinf",
  "lean_float_sqrt", "lean_float_sin", "lean_float_cos", "lean_float_exp", "lean_float_log",
  "lean_float_pow", "lean_float_floor", "lean_float_ceil", "lean_float_abs", "lean_float_round",
  "lean_float_scaleb",
  "lean_float_tan", "lean_float_asin", "lean_float_acos", "lean_float_atan", "lean_float_atan2",
  "lean_float_sinh", "lean_float_cosh", "lean_float_tanh",
  "lean_float_asinh", "lean_float_acosh", "lean_float_atanh",
  "lean_float_exp2", "lean_float_log2", "lean_float_log10", "lean_float_cbrt",
  "lean_float_frexp", "lean_float_of_bits", "lean_float_to_bits",
  "lean_float_to_uint8", "lean_float_to_uint16", "lean_float_to_uint32",
  "lean_float_to_uint64", "lean_float_to_usize", "lean_float_to_float32",
  "lean_float_of_scientific", "lean_float_to_string",
  "lean_float32_add", "lean_float32_sub", "lean_float32_mul", "lean_float32_div",
  "lean_float32_negate", "lean_float32_beq", "lean_float32_decLt", "lean_float32_decLe",
  "lean_float32_to_float", "lean_float32_sqrt", "lean_float32_abs", "lean_float32_to_string",
  "lean_float32_floor", "lean_float32_ceil", "lean_float32_round", "lean_float32_neg",
  "lean_float32_isnan", "lean_float32_isfinite", "lean_float32_isinf",
  "lean_float32_sin", "lean_float32_cos", "lean_float32_tan",
  "lean_float32_asin", "lean_float32_acos", "lean_float32_atan", "lean_float32_atan2",
  "lean_float32_sinh", "lean_float32_cosh", "lean_float32_tanh",
  "lean_float32_asinh", "lean_float32_acosh", "lean_float32_atanh",
  "lean_float32_exp", "lean_float32_exp2", "lean_float32_log", "lean_float32_log2",
  "lean_float32_log10", "lean_float32_pow", "lean_float32_cbrt",
  "lean_float32_to_uint8", "lean_float32_to_uint16", "lean_float32_to_uint32",
  "lean_float32_to_uint64", "lean_float32_to_usize",
  "lean_float32_of_bits", "lean_float32_to_bits", "lean_float32_scaleb", "lean_float32_frexp",
  "lean_uint64_to_float", "lean_uint32_to_float", "lean_usize_to_float",
  "lean_uint8_to_float32", "lean_uint16_to_float32", "lean_uint32_to_float32",
  "lean_uint64_to_float32", "lean_usize_to_float32",
  -- Char
  "lean_uint32_of_nat", "lean_char_to_nat",
  -- String
  "lean_string_length", "lean_string_append", "lean_string_push", "lean_string_dec_eq",
  "lean_string_data", "lean_string_mk", "lean_string_isempty", "lean_string_hash",
  "lean_uint64_mix_hash",
  "lean_string_utf8_byte_size", "lean_string_utf8_get", "lean_string_utf8_get_bang",
  "lean_string_utf8_get_opt", "lean_string_utf8_next", "lean_string_utf8_prev",
  "lean_string_utf8_at_end", "lean_string_utf8_extract", "lean_string_utf8_pos_of",
  "lean_string_utf8_set",
  "lean_string_contains", "lean_string_of_usize",
  "lean_string_get_byte_fast", "lean_string_utf8_get_fast",
  "lean_string_isprefixof", "lean_string_any",
  "lean_string_to_utf8", "lean_string_from_utf8_unchecked", "lean_string_validate_utf8",
  -- ByteArray
  "lean_mk_empty_byte_array", "lean_byte_array_size", "lean_byte_array_push",
  "lean_byte_array_get", "lean_byte_array_fget", "lean_byte_array_uget",
  "lean_byte_array_set", "lean_byte_array_fset", "lean_byte_array_uset",
  "lean_byte_array_copy_slice", "lean_sarray_size",
  -- Array
  "lean_array_get_size", "lean_array_get", "lean_array_get_borrowed",
  "lean_array_fget", "lean_array_fget_borrowed", "lean_array_set",
  "lean_array_push", "lean_array_pop", "lean_array_swap", "lean_array_uget",
  "lean_array_uget_borrowed",
  "lean_array_uset", "lean_array_usize", "lean_array_to_list", "lean_mk_array", "lean_array_mk",
  -- FloatArray (packed doubles -> Float64Array)
  "lean_float_array_mk", "lean_float_array_data", "lean_copy_float_array",
  "lean_mk_empty_float_array", "lean_float_array_size", "lean_float_array_push",
  "lean_float_array_uget", "lean_float_array_fget", "lean_float_array_get",
  "lean_float_array_uset", "lean_float_array_fset", "lean_float_array_set",
  -- dbgTrace / dbgTraceIfShared / dbgSleep (force the thunk internally, like
  -- lean_string_any; no explicit arm needed since the prelude impl matches the
  -- (msg/_, thunk) call shape and forces via lean_trampoline+lean_apply).
  "lean_dbg_trace", "lean_dbg_trace_if_shared", "lean_dbg_sleep",
  -- pointer utilities: the SAFE surface (withPtrAddr/withPtrEq) is proven
  -- address-independent, so a constant address / non-exclusive answer is faithful.
  "lean_ptr_addr", "lean_is_exclusive_obj",
  -- platform / panic
  "lean_system_platform_nbits", "lean_panic_fn",
  -- IO / ST / FS
  "lean_get_stdout", "lean_get_stderr", "lean_get_stdin",
  "lean_get_set_stdout", "lean_get_set_stderr", "lean_get_set_stdin",
  "lean_io_eprint", "lean_io_eprintln", "lean_io_getenv", "lean_io_exit",
  "lean_st_mk_ref", "lean_st_ref_get", "lean_st_ref_set", "lean_st_ref_swap",
  "lean_st_ref_take", "lean_st_ref_ptr_eq",
  "lean_io_prim_handle_mk", "lean_io_prim_handle_put_str", "lean_io_prim_handle_write",
  "lean_io_prim_handle_read", "lean_io_prim_handle_flush", "lean_io_prim_handle_is_tty",
  "lean_io_prim_handle_get_line"
]

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
def emitKnownFap (externMap : Std.HashMap Name String) (c : FunId) (ys : Array Arg) : Option String :=
  -- Drop erased (type/instance/proof) args: EmitC passes only runtime-relevant
  -- args to externs, so the prelude functions expect them packed left-to-right.
  let a := (ys.filter (fun y => match y with | .erased => false | _ => true)).map argToJs
  let bin (op : String) : Option String :=
    if h : a.size = 2 then some s!"({a[0]} {op} {a[1]})" else none
  let call (fn : String) : Option String :=
    some s!"{fn}({String.intercalate ", " a.toList})"
  -- SINGLE SOURCE OF TRUTH fallback: if `c` is an extern whose resolved C symbol
  -- the prelude defines, emit a plain call to that symbol. This covers every
  -- `@[extern]` alias for free (ofNat/ofNatLT/... all -> lean_usize_of_nat) the
  -- way EmitC does, so a forgotten alias can no longer dangle. The explicit arms
  -- below take precedence for the genuinely-special cases (inlined arithmetic,
  -- `Array.empty -> []`, and name mismatches where the JS impl name differs from
  -- the C symbol).
  let viaSymbol : Option String :=
    match externMap[c]? with
    | some sym => call sym
    | none     => none
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
  -- Signed fixed-width ints (bigint repr; two's-complement wrap). 64-bit/ISize
  -- toInt uses the *_sint extern name; 8/16/32 use plain *_to_int.
  | `Int8.add => call "lean_int8_add" | `Int8.sub => call "lean_int8_sub"
  | `Int8.mul => call "lean_int8_mul" | `Int8.div => call "lean_int8_div"
  | `Int8.mod => call "lean_int8_mod" | `Int8.neg => call "lean_int8_neg"
  | `Int8.land => call "lean_int8_land" | `Int8.lor => call "lean_int8_lor"
  | `Int8.xor => call "lean_int8_xor" | `Int8.complement => call "lean_int8_complement"
  | `Int8.shiftLeft => call "lean_int8_shift_left" | `Int8.shiftRight => call "lean_int8_shift_right"
  | `Int8.decEq => call "lean_int8_dec_eq" | `Int8.decLt => call "lean_int8_dec_lt"
  | `Int8.decLe => call "lean_int8_dec_le"
  | `Int8.ofInt => call "lean_int8_of_int" | `Int8.ofNat => call "lean_int8_of_nat"
  | `Int8.toInt => call "lean_int8_to_int"
  | `Int16.add => call "lean_int16_add" | `Int16.sub => call "lean_int16_sub"
  | `Int16.mul => call "lean_int16_mul" | `Int16.div => call "lean_int16_div"
  | `Int16.mod => call "lean_int16_mod" | `Int16.neg => call "lean_int16_neg"
  | `Int16.land => call "lean_int16_land" | `Int16.lor => call "lean_int16_lor"
  | `Int16.xor => call "lean_int16_xor" | `Int16.complement => call "lean_int16_complement"
  | `Int16.shiftLeft => call "lean_int16_shift_left" | `Int16.shiftRight => call "lean_int16_shift_right"
  | `Int16.decEq => call "lean_int16_dec_eq" | `Int16.decLt => call "lean_int16_dec_lt"
  | `Int16.decLe => call "lean_int16_dec_le"
  | `Int16.ofInt => call "lean_int16_of_int" | `Int16.ofNat => call "lean_int16_of_nat"
  | `Int16.toInt => call "lean_int16_to_int"
  | `Int32.add => call "lean_int32_add" | `Int32.sub => call "lean_int32_sub"
  | `Int32.mul => call "lean_int32_mul" | `Int32.div => call "lean_int32_div"
  | `Int32.mod => call "lean_int32_mod" | `Int32.neg => call "lean_int32_neg"
  | `Int32.land => call "lean_int32_land" | `Int32.lor => call "lean_int32_lor"
  | `Int32.xor => call "lean_int32_xor" | `Int32.complement => call "lean_int32_complement"
  | `Int32.shiftLeft => call "lean_int32_shift_left" | `Int32.shiftRight => call "lean_int32_shift_right"
  | `Int32.decEq => call "lean_int32_dec_eq" | `Int32.decLt => call "lean_int32_dec_lt"
  | `Int32.decLe => call "lean_int32_dec_le"
  | `Int32.ofInt => call "lean_int32_of_int" | `Int32.ofNat => call "lean_int32_of_nat"
  | `Int32.toInt => call "lean_int32_to_int"
  | `Int64.add => call "lean_int64_add" | `Int64.sub => call "lean_int64_sub"
  | `Int64.mul => call "lean_int64_mul" | `Int64.div => call "lean_int64_div"
  | `Int64.mod => call "lean_int64_mod" | `Int64.neg => call "lean_int64_neg"
  | `Int64.land => call "lean_int64_land" | `Int64.lor => call "lean_int64_lor"
  | `Int64.xor => call "lean_int64_xor" | `Int64.complement => call "lean_int64_complement"
  | `Int64.shiftLeft => call "lean_int64_shift_left" | `Int64.shiftRight => call "lean_int64_shift_right"
  | `Int64.decEq => call "lean_int64_dec_eq" | `Int64.decLt => call "lean_int64_dec_lt"
  | `Int64.decLe => call "lean_int64_dec_le"
  | `Int64.ofInt => call "lean_int64_of_int" | `Int64.ofNat => call "lean_int64_of_nat"
  | `Int64.toInt => call "lean_int64_to_int_sint"
  | `ISize.add => call "lean_isize_add" | `ISize.sub => call "lean_isize_sub"
  | `ISize.mul => call "lean_isize_mul" | `ISize.div => call "lean_isize_div"
  | `ISize.mod => call "lean_isize_mod" | `ISize.neg => call "lean_isize_neg"
  | `ISize.land => call "lean_isize_land" | `ISize.lor => call "lean_isize_lor"
  | `ISize.xor => call "lean_isize_xor" | `ISize.complement => call "lean_isize_complement"
  | `ISize.shiftLeft => call "lean_isize_shift_left" | `ISize.shiftRight => call "lean_isize_shift_right"
  | `ISize.decEq => call "lean_isize_dec_eq" | `ISize.decLt => call "lean_isize_dec_lt"
  | `ISize.decLe => call "lean_isize_dec_le"
  | `ISize.ofInt => call "lean_isize_of_int" | `ISize.ofNat => call "lean_isize_of_nat"
  | `ISize.toInt => call "lean_isize_to_int_sint"
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
  | `Float.tan => call "lean_float_tan"
  | `Float.asin => call "lean_float_asin" | `Float.acos => call "lean_float_acos"
  | `Float.atan => call "lean_float_atan" | `Float.atan2 => call "lean_float_atan2"
  | `Float.sinh => call "lean_float_sinh" | `Float.cosh => call "lean_float_cosh"
  | `Float.tanh => call "lean_float_tanh"
  | `Float.asinh => call "lean_float_asinh" | `Float.acosh => call "lean_float_acosh"
  | `Float.atanh => call "lean_float_atanh"
  | `Float.exp2 => call "lean_float_exp2" | `Float.log2 => call "lean_float_log2"
  | `Float.log10 => call "lean_float_log10" | `Float.cbrt => call "lean_float_cbrt"
  | `Float.frExp => call "lean_float_frexp"
  | `Float.ofBits => call "lean_float_of_bits" | `Float.toBits => call "lean_float_to_bits"
  | `Float.floor => call "lean_float_floor" | `Float.ceil => call "lean_float_ceil"
  | `Float.abs => call "lean_float_abs" | `Float.round => call "lean_float_round"
  | `Float.scaleb => call "lean_float_scaleb"
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
  | `Float32.sin => call "lean_float32_sin" | `Float32.cos => call "lean_float32_cos"
  | `Float32.tan => call "lean_float32_tan"
  | `Float32.asin => call "lean_float32_asin" | `Float32.acos => call "lean_float32_acos"
  | `Float32.atan => call "lean_float32_atan" | `Float32.atan2 => call "lean_float32_atan2"
  | `Float32.sinh => call "lean_float32_sinh" | `Float32.cosh => call "lean_float32_cosh"
  | `Float32.tanh => call "lean_float32_tanh"
  | `Float32.asinh => call "lean_float32_asinh" | `Float32.acosh => call "lean_float32_acosh"
  | `Float32.atanh => call "lean_float32_atanh"
  | `Float32.exp => call "lean_float32_exp" | `Float32.exp2 => call "lean_float32_exp2"
  | `Float32.log => call "lean_float32_log" | `Float32.log2 => call "lean_float32_log2"
  | `Float32.log10 => call "lean_float32_log10" | `Float32.pow => call "lean_float32_pow"
  | `Float32.cbrt => call "lean_float32_cbrt"
  | `Float32.floor => call "lean_float32_floor" | `Float32.ceil => call "lean_float32_ceil"
  | `Float32.round => call "lean_float32_round"
  | `Float32.isNaN => call "lean_float32_isnan" | `Float32.isFinite => call "lean_float32_isfinite"
  | `Float32.isInf => call "lean_float32_isinf"
  | `Float32.ofBits => call "lean_float32_of_bits" | `Float32.toBits => call "lean_float32_to_bits"
  | `Float32.scaleb => call "lean_float32_scaleb" | `Float32.frExp => call "lean_float32_frexp"
  | `Float32.toUInt8 => call "lean_float32_to_uint8" | `Float32.toUInt16 => call "lean_float32_to_uint16"
  | `Float32.toUInt32 => call "lean_float32_to_uint32" | `Float32.toUInt64 => call "lean_float32_to_uint64"
  | `Float32.toUSize => call "lean_float32_to_usize"
  | `USize.toFloat => call "lean_usize_to_float"
  | `UInt8.toFloat32 => call "lean_uint8_to_float32" | `UInt16.toFloat32 => call "lean_uint16_to_float32"
  | `UInt32.toFloat32 => call "lean_uint32_to_float32" | `UInt64.toFloat32 => call "lean_uint64_to_float32"
  | `USize.toFloat32 => call "lean_usize_to_float32"
  | `Float.toString => call "lean_float_to_string"
  | `Float32.toString => call "lean_float32_to_string"
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
  | `Array.uget                   => call "lean_array_uget"
  | `Array.ugetBorrowed           => call "lean_array_uget_borrowed"
  | `Array.getInternal            => call "lean_array_uget"
  | `Array.getInternalBorrowed    => call "lean_array_fget_borrowed"
  | `Array.uset                   => call "lean_array_uset"
  | `Array.usize                  => call "lean_array_usize"
  | `Array.toList                 => call "lean_array_to_list"
  | `Array.mkArray                => call "lean_mk_array"
  | `Array.mkArray0               => some "[]"
  -- Nat extras used by Float.ofScientific and array index lowering.
  | `Nat.log2                     => call "lean_nat_log2"
  | `Nat.shiftLeft                => call "lean_nat_shift_left"
  | `Nat.shiftRight               => call "lean_nat_shift_right"
  | `Nat.land                     => call "lean_nat_land"
  | `Nat.lor                      => call "lean_nat_lor"
  | `Nat.xor                      => call "lean_nat_xor"
  -- Int / numeric conversions.
  | `Int.ofNat                    => call "lean_int_of_nat"
  | `Int.toNat                    => call "lean_int_to_nat"
  | `Nat.toUInt8                  => call "lean_uint8_of_nat"
  | `Nat.toUInt16                 => call "lean_uint16_of_nat"
  | `Nat.toUInt32                 => call "lean_uint32_of_nat2"
  | `Nat.toUInt64                 => call "lean_uint64_of_nat"
  | `Nat.toUSize                  => call "lean_usize_of_nat"
  | `UInt64.toFloat               => call "lean_uint64_to_float"
  | `UInt32.toFloat               => call "lean_uint32_to_float"
  -- IO / ST.Ref / streams / process. The World/void arg is dropped by the
  -- emitter (filtered params), so these take only their runtime args.
  | `IO.getStdout                 => call "lean_get_stdout"
  | `IO.getStderr                 => call "lean_get_stderr"
  | `IO.getStdin                  => call "lean_get_stdin"
  | `IO.setStdout                 => call "lean_get_set_stdout"
  | `IO.setStderr                 => call "lean_get_set_stderr"
  | `IO.setStdin                  => call "lean_get_set_stdin"
  | `IO.eprint                    => call "lean_io_eprint"
  | `IO.eprintln                  => call "lean_io_eprintln"
  | `IO.getEnv                    => call "lean_io_getenv"
  | `IO.Process.exit              => call "lean_io_exit"
  | `IO.Process.Prim.exit         => call "lean_io_exit"
  | `ST.Prim.mkRef                => call "lean_st_mk_ref"
  | `ST.Prim.Ref.get              => call "lean_st_ref_get"
  | `ST.Prim.Ref.set              => call "lean_st_ref_set"
  | `ST.Prim.Ref.swap             => call "lean_st_ref_swap"
  | `ST.Prim.Ref.take             => call "lean_st_ref_take"
  | `ST.Prim.Ref.ptrEq            => call "lean_st_ref_ptr_eq"
  | `IO.FS.Handle.mk              => call "lean_io_prim_handle_mk"
  | `IO.FS.Handle.putStr          => call "lean_io_prim_handle_put_str"
  | `IO.FS.Handle.write           => call "lean_io_prim_handle_write"
  | `IO.FS.Handle.read            => call "lean_io_prim_handle_read"
  | `IO.FS.Handle.flush           => call "lean_io_prim_handle_flush"
  | `IO.FS.Handle.isTty           => call "lean_io_prim_handle_is_tty"
  -- misc reached by toString / repr / platform width.
  | `Array.mk                     => call "lean_array_mk"
  | `String.ofList                => call "lean_string_mk"
  | `USize.repr                   => call "lean_string_of_usize"
  | `System.Platform.getNumBits   => call "lean_system_platform_nbits"
  | _ => viaSymbol

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
  | .usize   => "usize"   -- width follows WORD_BITS (prelude), not a literal 64
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
def emitExpr (externMap : Std.HashMap Name String) (arityMap : Std.HashMap Name Nat := {})
    (initGlobals : Std.HashSet Name := {}) (cores : Std.HashSet Name := {})
    (ty : IRType := .object) : IR.Expr → String
  | .ctor i ys      => ctorLit i ys
  | .reset _ _      => "null"          -- GC: reuse token unused
  | .reuse _ i _ ys => ctorLit i ys    -- GC: identical to a fresh ctor
  | .proj i x       => s!"{varName x}.fields[{i}]"
  | .uproj i x      => s!"{varName x}.fields[{i}]"
  | .sproj n offset x => s!"lean_ctor_get_{sscalarSuffix ty}({varName x}, {sbyteOffset n offset})"
  | .fap c ys       =>
    -- An init-backed value global is a mutable slot, not a function: reference it
    -- bare (no `()`), exactly as EmitC reads the C global directly.
    if initGlobals.contains c && ys.isEmpty then funRef c
    else
    match emitKnownFap externMap c ys with
    | some s => s
    | none   =>
      -- Only a real (collected `.fdecl`) Lean function reaches here: an extern
      -- without a prelude symbol is a hard extraction error caught by
      -- `validateExterns` before emission, so this never emits a dangling extern.
      let args := String.intercalate ", " (ys.toList.map argToJs)
      s!"{funRef c}({args})"
  | .pap c ys       =>
    let args := String.intercalate ", " (ys.toList.map argToJs)
    -- Record the worker's FULL arity so `lean_apply` can branch exact/under/over.
    -- An uncollected callee or extern has no arity entry; emit a closure with no
    -- arity (concat-and-call fallback), which is correct for the exact case only.
    let fnRef := if cores.contains c then tcRef c else funRef c
    match arityMap[c]? with
    | some n => s!"lean_closure({fnRef}, {n}, [{args}])"
    | none   => "{ fn: " ++ fnRef ++ ", args: [" ++ args ++ "] }"
  | .ap x ys        =>
    -- Non-tail application: force the result. `lean_apply` returns a thunk for
    -- its final saturating call, so drive it through the trampoline here (the
    -- tail-position `.ap` instead returns the `__tc:2` thunk directly, letting
    -- the enclosing core's wrapper unroll the apply chain in constant stack).
    let args := String.intercalate ", " (ys.toList.map argToJs)
    s!"lean_trampoline(lean_apply({varName x}, [{args}]))"
  | .box _ x        => varName x        -- GC: identity
  | .unbox x        => varName x        -- GC: identity
  | .lit (.num v)   =>
    -- u8/u16/u32/float (and Bool) -> plain number; u64/usize and object Nat ->
    -- bigint, matching the prelude's UInt64/USize (bigint) representation.
    match ty with
    | .uint8 | .uint16 | .uint32 | .float | .float32 => s!"{v}"
    | _ => s!"{v}n"
  | .lit (.str v)   => quoteString v
  | .isShared _     => "1"
    -- Always report "shared" so the compiler's exclusivity branch takes the
    -- copying path instead of mutating in place; JS references are shared and
    -- there is no refcount, so in-place `set`/`reuse` would corrupt aliases.

/-! ## Tail-call detection (strategies A + B)

A tail call lowers to `let r := callee args; <dec/inc/del>*; ret r` possibly
preceded by other straight-line statements. `matchTailCall` looks through the
straight-line prefix and through the trailing refcount no-ops between the call
and the `ret`, returning the callee and its args. Self-tail-calls (callee ==
self) become a `while` loop; cross-function tail calls between members of a
tail-call SCC become trampoline thunks. -/

/-- Does this body (a chain of `dec/inc/del`) end in `ret (var x)`? -/
partial def retsVar (x : VarId) : FnBody → Bool
  | .ret (.var r) => r == x
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => retsVar x b
  | _ => false

/-- A matched tail call: a direct `.fap` to a named callee (loopable/thunkable
    if the callee has a `__tc` core), or a `.ap` applying a closure value in tail
    position (always emitted as a `__tc:2` thunk the wrapper unrolls). -/
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

/-- Join-point environment for loop mode: maps a join-point index to its
    parameters and body, so a `jmp` can inline the body (keeping any `continue`
    lexically inside the surrounding `while`). -/
abbrev JpEnv := Std.HashMap Nat (Array Param × FnBody)

mutual

/-- `self` is the function being emitted; `scc` is the thunk-target set (names
    that have a `__tc` core). A tail call to `self` loops (`continue`); to any
    thunk target it returns a `{__tc}` thunk; to anything else (extern, plain
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
    let st ← get
    line s!"const {varName x} = {emitExpr st.externMap st.arityMap st.initGlobals st.cores ty e};"
    emitFnBodyLoop self scc params jps k
  | .jdecl j xs v k =>
    emitFnBodyLoop self scc params (jps.insert j.idx (xs, v)) k
  | .set x i y k => do
    line s!"{varName x}.fields[{i}] = {argToJs y};"
    emitFnBodyLoop self scc params jps k
  | .setTag x cidx k => do
    line s!"{varName x}.tag = {cidx};"
    emitFnBodyLoop self scc params jps k
  | .uset x i y k => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitFnBodyLoop self scc params jps k
  | .sset x i offset y ty k => do
    line s!"lean_ctor_set_{sscalarSuffix ty}({varName x}, {sbyteOffset i offset}, {varName y});"
    emitFnBodyLoop self scc params jps k
  | .inc _ _ _ _ k => emitFnBodyLoop self scc params jps k
  | .dec _ _ _ _ k => emitFnBodyLoop self scc params jps k
  | .del _ k       => emitFnBodyLoop self scc params jps k
  | .ret x => line s!"return {argToJs x};"
  | .jmp j ys => do
    match jps.get? j.idx with
    | some (xs, body) => do
      for (p, a) in xs.zip ys do
        line s!"const {varName p.x} = {argToJs a};"
      emitFnBodyLoop self scc params jps body
    | none =>
      let args := String.intercalate ", " (ys.toList.map argToJs)
      line s!"return {jpName j}({args});"
  | .unreachable => line "lean_internal_panic_unreachable();"
  | .case _ x xType alts => do
    let scrut := if xType.isScalar then varName x else s!"lean_tag({varName x})"
    line ("switch (" ++ scrut ++ ") {")
    withIndent do
      let mut sawDefault := false
      for alt in alts do
        match alt with
        | .ctor info b => do
          line ("case " ++ toString info.cidx ++ ": {")
          withIndent (emitFnBodyLoop self scc params jps b)
          line "}"
        | .default b => do
          sawDefault := true
          line "default: {"
          withIndent (emitFnBodyLoop self scc params jps b)
          line "}"
      unless sawDefault do
        line "default: { throw new Error(\"no matching case\"); }"
    line "}"

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
        let args := String.intercalate ", " (cargs.toList.map argToJs)
        line ("return { __tc: 1, f: " ++ tcRef c ++ ", a: [" ++ args ++ "] };")
    else
      let st ← get
      line s!"const {varName x} = {emitExpr st.externMap st.arityMap st.initGlobals st.cores ty (.fap c cargs)};"
      emitFnBodyLoop self scc params jps k
  | .vdecl x ty (.ap fx aargs) k => do
    if retsVar x k then
      -- Tail-position closure application: return a `__tc:2` apply-thunk the
      -- wrapper's `lean_trampoline` unrolls, instead of forcing `lean_apply`
      -- here (which would stack a JS frame per CPS / continuation step).
      let args := String.intercalate ", " (aargs.toList.map argToJs)
      line ("return { __tc: 2, clo: " ++ varName fx ++ ", a: [" ++ args ++ "] };")
    else
      let st ← get
      line s!"const {varName x} = {emitExpr st.externMap st.arityMap st.initGlobals st.cores ty (.ap fx aargs)};"
      emitFnBodyLoop self scc params jps k
  | .vdecl x ty e k => do
    let st ← get
    line s!"const {varName x} = {emitExpr st.externMap st.arityMap st.initGlobals st.cores ty e};"
    emitPrefixThenTail self scc params jps k
  | .set x i y k => do
    line s!"{varName x}.fields[{i}] = {argToJs y};"
    emitPrefixThenTail self scc params jps k
  | .setTag x cidx k => do
    line s!"{varName x}.tag = {cidx};"
    emitPrefixThenTail self scc params jps k
  | .uset x i y k => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitPrefixThenTail self scc params jps k
  | .sset x i offset y ty k => do
    line s!"lean_ctor_set_{sscalarSuffix ty}({varName x}, {sbyteOffset i offset}, {varName y});"
    emitPrefixThenTail self scc params jps k
  | .inc _ _ _ _ k => emitPrefixThenTail self scc params jps k
  | .dec _ _ _ _ k => emitPrefixThenTail self scc params jps k
  | .del _ k       => emitPrefixThenTail self scc params jps k
  | b => emitNonTail self scc params jps b

partial def emitTailRebind (params : Array Param) (args : Array Arg) : EmitM Unit := do
  -- Only the params that survive as JS function parameters are rebound: the
  -- `void` World token and erased (type/proof) params are dropped from the
  -- function signature (emitDeclWith), so assigning to them would reference an
  -- undeclared variable (`x_3 = __t_3` for a void World param). Filter in
  -- lockstep with the positionally-aligned args.
  let live := (params.zip args).filter (fun (p, _) => !p.ty.isVoid && !p.ty.isErased)
  -- stage all new values into temporaries first (aliasing safety)
  for (p, a) in live do
    line s!"const __t_{p.x.idx} = {argToJs a};"
  for (p, _) in live do
    line s!"{varName p.x} = __t_{p.x.idx};"
  line "continue;"

end

/-- Non-loop emitter (no self-tail-call present). -/
partial def emitFnBody : FnBody → EmitM Unit
  | .vdecl x ty e b => do
    let st ← get
    line s!"const {varName x} = {emitExpr st.externMap st.arityMap st.initGlobals st.cores ty e};"
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
  | .unreachable => line "lean_internal_panic_unreachable();"
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

/-! ## Tail-call trampoline targets (strategy A)

A matched tail call to a collected callee `c` returns a `{__tc:1, f: tcRef c, a}`
thunk instead of stacking a JS frame; the callee's wrapper drives `lean_trampoline`
to unroll the chain. This covers self-recursion (self edge loops via `continue`),
mutual recursion (each member is a tail target of another), AND acyclic DAG tail
chains (f→g→h, distinct size-1 SCCs), all in constant JS stack. The thunk-target
set is just every function that is the target of some collected tail edge. -/

/-- Names that are the *target* of some collected decl's tail edge (cyclic OR
    acyclic). Every such function gets a `__tc` core so a caller's matched tail
    call can return a `{__tc}` thunk naming `tcRef`, and the trampoline unrolls
    the whole chain with no JS stack growth. This subsumes the SCC machinery:
    mutual-recursion members are each a target of another, and a self-recursive
    function is its own target. Acyclic DAG chains (f→g→h, distinct size-1 SCCs)
    are now covered too — each chain link is a target. -/
def computeCoreTargets (decls : Array Decl) : Std.HashSet Name := Id.run do
  -- A thunk target must be emitted as a real `funRef` function, i.e. a collected
  -- `.fdecl` (NOT an `.extern`, which lowers to an inline op or a prelude call
  -- with no `__tc` core). Restricting the candidate names to fdecls prevents
  -- thunking a tail-positioned `Nat.add`/extern (which has no `__tc` core).
  let names : Std.HashSet Name := decls.foldl (fun s d =>
    match d with | .fdecl .. => s.insert d.name | .extern .. => s) {}
  let mut targets : Std.HashSet Name := {}
  for d in decls do
    for c in (declTailEdges d).filter names.contains do
      targets := targets.insert c
  return targets

/-- A function needs a trampolined core+wrapper iff it is a thunk target, or it
    makes any tail call to a thunk target (so its body returns `{__tc}` thunks
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
    `lean_trampoline` per applied tail step and re-grow the JS stack. This is a
    superset of `computeCoreTargets`: a worker reached only through `.pap` (never
    a direct tail edge) is not a thunk target yet still gets a core (e.g. via
    `hasTailAp`/`hasSelfTailCall`). -/
def computeEmittedCores (decls : Array Decl) : Std.HashSet Name := Id.run do
  let targets := computeCoreTargets decls
  let mut acc : Std.HashSet Name := {}
  for d in decls do
    if needsCore targets d then acc := acc.insert d.name
  return acc

/-- Emit a top-level `Decl` as a TS function. `cores` is the set of names that
    have a `__tc` core (thunk targets); a tail call to a member returns a thunk
    and the wrapper drives the trampoline, so cyclic AND acyclic cross-function
    tail chains run in constant JS stack. -/
def emitDeclWith (cores : Std.HashSet Name) : Decl → EmitM Unit
  | d@(.fdecl f xs _ body _) => do
    -- An init-backed value global (`initialize x ← ...`) has a `⊥` IR body and is
    -- never called; emit it as a mutable slot the init thunk assigns, referenced
    -- bare at use sites (the `.fap c []` path checks `initGlobals`).
    if (← get).initGlobals.contains f then
      line s!"let {funRef f} = null;"
      return
    let params := xs.toList.filter (fun p => !p.ty.isErased && !p.ty.isVoid)
    let paramStr := String.intercalate ", " (params.map (fun p => varName p.x))
    if needsCore cores d then
      -- trampolined core: tail edges to any core target return thunks; self
      -- edges loop (`continue`); the wrapper unrolls returned thunks.
      line ("function " ++ tcRef f ++ "(" ++ paramStr ++ ") {")
      withIndent do
        line "while (true) {"
        withIndent (emitFnBodyLoop f cores xs {} body)
        line "}"
      line "}"
      -- public wrapper drives the trampoline
      line ("function " ++ funRef f ++ "(" ++ paramStr ++ ") {")
      withIndent do
        line s!"return lean_trampoline({tcRef f}({paramStr}));"
      line "}"
    else
      line ("function " ++ funRef f ++ "(" ++ paramStr ++ ") {")
      withIndent (emitFnBody body)
      line "}"
  | .extern f _ _ _ =>
    line s!"// extern {funRef f} -> runtime prelude"

/-- Backwards-compatible single-decl emitter (no SCC trampolining). -/
def emitDecl : Decl → EmitM Unit := emitDeclWith {}

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

/-! ## Extern resolution + fail-loud link check

For every reached `.extern` decl, resolve its C symbol via `externSymbol`
(`getExternNameFor … `c`). Build the `Name → symbol` link table, and assert each
symbol is one the prelude defines (`preludeSymbols`). Anything unresolved — an
extern with no C entry (adhoc/inline/opaque), or a `standard` symbol the prelude
lacks — is accumulated and reported as a hard extraction error, exactly like a C
linker failing to resolve a symbol. This turns a latent runtime ReferenceError
(a forgotten `@[extern]` alias emitting a dangling `funRef` call) into a
build-time failure. -/

/-- Build the extern link table and the list of unresolved externs. An extern is
    "resolved" iff `externSymbol` yields a C symbol AND that symbol is in
    `preludeSymbols`, OR the decl is special-cased by `emitKnownFap` (we cannot
    cheaply re-run that pure matcher here, so we instead let resolved-but-unknown
    symbols through only when they are in `preludeSymbols`; `emitKnownFap`'s
    explicit arms take precedence at emit time regardless, so a name that is both
    special-cased and has an unknown symbol still emits correctly — see note). -/
def buildExternMap (env : Environment) (decls : Array Decl)
    : Std.HashMap Name String × Array (Name × String) := Id.run do
  let mut map : Std.HashMap Name String := {}
  let mut unresolved : Array (Name × String) := #[]
  for d in decls do
    match d with
    | .extern f _ _ _ =>
      match externSymbol env f with
      | some sym =>
        if preludeSymbols.contains sym then
          map := map.insert f sym
        else
          -- A `standard` extern whose C symbol the prelude does not provide. This
          -- is fine ONLY if `emitKnownFap` special-cases the Lean name (e.g.
          -- `lean_nat_add` -> inlined `+`); otherwise it would dangle. We record
          -- it as unresolved unless a known special-case name covers it.
          unless emitKnownFapSpecialNames.contains f do
            unresolved := unresolved.push (f, sym)
      | none =>
        -- adhoc/inline/opaque extern: no plain C symbol. Allowed only if a
        -- special-case arm handles it; else hard error.
        unless emitKnownFapSpecialNames.contains f do
          unresolved := unresolved.push (f, "<no C symbol: adhoc/inline/opaque>")
    | .fdecl .. => pure ()
  return (map, unresolved)

/-- Map each collected `.fdecl` to its full JS arity: the count of params that
    survive into the emitted signature (non-erased, non-void), exactly the params
    `funRef`/`emitDeclWith` declares. Read by the `.pap` path so a partial
    application records the worker's arity for `lean_apply`'s three-way dispatch. -/
def buildArityMap (decls : Array Decl) : Std.HashMap Name Nat := Id.run do
  let mut m : Std.HashMap Name Nat := {}
  for d in decls do
    match d with
    | .fdecl (xs := xs) .. =>
      let n := (xs.filter (fun p => !p.ty.isErased && !p.ty.isVoid)).size
      m := m.insert d.name n
    | .extern .. => pure ()
  return m

/-- Run the emitter over the given decls, returning the produced TS source, or a
    link-error string naming every unresolved extern. Computes tail-call SCCs
    first so mutually tail-recursive groups trampoline. -/
def renderChecked (env : Environment) (decls : Array Decl) : Except String String := Id.run do
  let (externMap, unresolved) := buildExternMap env decls
  if !unresolved.isEmpty then
    let lines := unresolved.toList.map (fun (n, s) => s!"  {n} -> {s}")
    return .error
      ("unmapped externs (no prelude symbol; would emit a dangling call):\n"
        ++ String.intercalate "\n" lines)
  let arityMap := buildArityMap decls
  let cores := computeCoreTargets decls
  let emittedCores := computeEmittedCores decls
  let act : EmitM Unit := do
    for d in decls do
      emitDeclWith cores d
      line ""
  let (_, st) := act.run { externMap, arityMap, cores := emittedCores }
  return .ok st.out

/-- Backwards-compatible pure renderer (no link check): used by callers that
    have already validated, or for tests. -/
def render (decls : Array Decl) : String := Id.run do
  let arityMap := buildArityMap decls
  let cores := computeCoreTargets decls
  let emittedCores := computeEmittedCores decls
  let act : EmitM Unit := do
    for d in decls do
      emitDeclWith cores d
      line ""
  let (_, st) := act.run { arityMap, cores := emittedCores }
  return st.out

/-- Collect transitively from roots and render a self-contained module body. -/
def renderFromRoots (env : Environment) (roots : Array Name) : String :=
  render (collectTransitive env roots)

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

/-- Emit the program entry that runs `main` and decodes the io_result. -/
def emitMainEntry (env : Environment) (d : Decl) : EmitM Unit := do
  let hasArgs := if mainHasArgs d then "true" else "false"
  let retU32  := if mainRetIsUInt32 env d.name then "true" else "false"
  line ""
  line s!"lean_run_main({funRef d.name}, {hasArgs}, {retU32});"

/-- Register init thunks for every reached decl carrying an `@[init]` /
    `builtin_initialize` init fn (analogue of `EmitC.emitDeclInit`). Each thunk
    runs the init action (the init fn is a separately-collected decl emitted as
    `funRef initFn`) and assigns its io_result value to the decl's global, then
    returns the io_result so `lean_run_init` can short-circuit on error. Builtin
    inits (`isIOUnitBuiltinInitFn`) are skipped — they configure the compiler
    environment, not the runtime program, exactly as EmitC guards them behind
    `if (builtin)`. EmitC runs decl inits in reverse decl order; `decls` is
    callee-first so the reverse is caller-first. -/
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
      line ("lean_register_init(() => " ++ funRef n ++ "());")
    -- A value global with a separate init fn: run it and bind the io_result value
    -- to the global slot (assignment, not a call).
    else
      match getInitFnNameFor? env n with
      | some initFn =>
        line ("lean_register_init(() => { const __r = " ++ funRef initFn
          ++ "(); if (lean_io_result_is_ok(__r)) { " ++ funRef n
          ++ " = lean_io_result_get_value(__r); } return __r; });")
      | none => pure ()

/-- Init decls to add to a program's collection beyond what `main` reaches: every
    regular (non-builtin) init action / init-fn-backed global declared in the same
    module as `mainName`. EmitC iterates ALL module decls for init; we scope to the
    program's module so stdlib `builtin_initialize`s are not pulled in. Returns the
    extra roots to collect (init actions + the init fns of value globals) and the
    set of value-global names (emitted as mutable slots, referenced bare). -/
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
    if initFn == Name.anonymous then
      -- bare `@[init]` action: the decl itself is the init fn; collect its body.
      roots := roots.push n
    else
      -- value global: collect the global decl AND its separate init fn.
      roots := roots.push n
      roots := roots.push initFn
      globals := globals.insert n
  return (roots, globals, initNames)

/-- Render a runnable program from a `main` root: the transitive function
    declarations plus the entry that invokes `main`. Fails loud on an unmapped
    extern (link check) before emitting, like `renderChecked`. -/
def renderProgramChecked (env : Environment) (mainName : Name) : Except String String := Id.run do
  -- Seed collection with `main` AND the module's init actions / value-global init
  -- fns, which `main` does not transitively reach but must still run before it.
  let (initRoots, initGlobals, initNames) := collectInitDecls env mainName
  let decls := collectTransitive env (#[mainName] ++ initRoots)
  let (externMap, unresolved) := buildExternMap env decls
  if !unresolved.isEmpty then
    let lines := unresolved.toList.map (fun (n, s) => s!"  {n} -> {s}")
    return .error
      ("unmapped externs (no prelude symbol; would emit a dangling call):\n"
        ++ String.intercalate "\n" lines)
  let arityMap := buildArityMap decls
  let cores := computeCoreTargets decls
  let emittedCores := computeEmittedCores decls
  let act : EmitM Unit := do
    for d in decls do
      emitDeclWith cores d
      line ""
    -- Module-init chain (analogue of EmitC.emitInitFn / emitDeclInit). Register a
    -- thunk per reached `@[init]` action / value-global init fn; `lean_run_init`
    -- runs them (in registration order) before `main`. `decls` is callee-first;
    -- EmitC runs decl inits in declaration order, so we iterate the reverse.
    emitInitRegistrations env initNames
    match decls.find? (fun d => d.name == mainName) with
    | some d => emitMainEntry env d
    | none   => pure ()
  let (_, st) := act.run { externMap, arityMap, initGlobals, cores := emittedCores }
  return .ok st.out

end LeanJs
