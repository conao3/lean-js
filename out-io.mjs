// ===================== lean-js runtime prelude =====================
// Representation choices:
//   Nat  -> bigint (>= 0n)        Int   -> bigint
//   UInt8/16/32 -> number         UInt64/USize -> bigint
//   Float/Float32 -> number       Bool -> scalar 0/1   Char -> number (code point)
//   String -> JS string; String.Pos is a UTF-8 byte offset
//   Array<T> -> T[]               List<T> -> tagged ctor objects {tag, fields}
// Bool is lowered to a scalar (false=0, true=1) matched by the emitted
// `switch`, so decEq/decLt/decLe and other Bool-returning externs return the
// number 0 or 1 (NOT a JS boolean: `switch (true)` would not hit `case 1`).
const L_bool = (b) => (b ? 1 : 0);

// Constructor tag of a value. Nullary ctors of a multi-ctor inductive (e.g.
// List.nil, Bool.false) are lowered to the bare number cidx (like lean_box);
// ctors with fields are objects { tag, fields }. lean_obj_tag handles both.
const lean_tag = (x) => (typeof x === 'number' ? x : x.tag);

// ---- constructor objects: three regions mirroring lean_alloc_ctor ----
// A heap ctor is one block with header + object/usize word slots + packed
// scalar bytes (Lean.Compiler.IR.Basic CtorInfo {size, usize, ssize}):
//   fields : word slots. fields[0..size) are object pointers (proj/set),
//            fields[size..size+usize) are USize values (uproj/uset). Both use
//            the IR word index directly, exactly as lean_ctor_get / _get_usize.
//   sdata  : a DataView of `ssize` packed scalar bytes (sproj/sset), addressed
//            by byte offset (the IR's word-prefix `n` is dropped; sdata starts
//            at its own offset 0). Little-endian to match native x86_64.
// A fully-scalar ctor (size==usize==ssize==0) is a bare number cidx (lean_box).
const lean_alloc_ctor = (tag, size, usize, ssize) => ({
  tag,
  fields: new Array(size + usize).fill(undefined),
  sdata: ssize > 0 ? new DataView(new ArrayBuffer(ssize)) : null,
});
// Allocate a ctor and fill its object region positionally (mirrors emitCtor +
// emitCtorSetArgs); usize/scalar fields are filled later by uset/sset.
const lean_ctor = (tag, size, usize, ssize, ...objs) => {
  const c = lean_alloc_ctor(tag, size, usize, ssize);
  for (let i = 0; i < objs.length; i++) c.fields[i] = objs[i];
  return c;
};

// Packed-scalar get/set into region S (sproj/sset), byte offset addressed,
// width chosen by IR type. u8/u16/u32 -> number; u64/usize -> bigint; floats
// -> number. Little-endian to match the native ABI.
// u8/u16/u32 are plain JS numbers (matching scalar literal emission and
// `switch` on Bool); u64/usize are bigint; floats are numbers.
const lean_ctor_get_u8  = (x, o) => x.sdata.getUint8(o);
const lean_ctor_get_u16 = (x, o) => x.sdata.getUint16(o, true);
const lean_ctor_get_u32 = (x, o) => x.sdata.getUint32(o, true);
const lean_ctor_get_u64 = (x, o) => x.sdata.getBigUint64(o, true);
const lean_ctor_get_f64 = (x, o) => x.sdata.getFloat64(o, true);
const lean_ctor_get_f32 = (x, o) => x.sdata.getFloat32(o, true);
const lean_ctor_set_u8  = (x, o, v) => x.sdata.setUint8(o, Number(v) & 0xff);
const lean_ctor_set_u16 = (x, o, v) => x.sdata.setUint16(o, Number(v) & 0xffff, true);
const lean_ctor_set_u32 = (x, o, v) => x.sdata.setUint32(o, Number(v) >>> 0, true);
const lean_ctor_set_u64 = (x, o, v) => x.sdata.setBigUint64(o, BigInt.asUintN(64, v), true);
const lean_ctor_set_f64 = (x, o, v) => x.sdata.setFloat64(o, v, true);
const lean_ctor_set_f32 = (x, o, v) => x.sdata.setFloat32(o, Math.fround(v), true);
// Packed USize scalar: width follows WORD_BITS (the pointer width), not a literal
// 64 — a 32-bit profile reads/writes 4 bytes. (In practice usize fields use the
// word-indexed uproj/uset path, not sproj/sset, so this is a defensive fallback.)
const lean_ctor_get_usize = (x, o) =>
  WORD_BITS === 64 ? x.sdata.getBigUint64(o, true) : BigInt(x.sdata.getUint32(o, true));
const lean_ctor_set_usize = (x, o, v) =>
  WORD_BITS === 64
    ? x.sdata.setBigUint64(o, BigInt.asUintN(64, BigInt(v)), true)
    : x.sdata.setUint32(o, Number(BigInt.asUintN(32, BigInt(v))) >>> 0, true);

// ---- trampoline driver for mutual / cross-function tail calls ----
// A trampolined core returns a thunk { __tc:1, f, a:[args] } at an SCC-internal
// tail edge instead of recursing; the driver unrolls thunks so no JS stack
// frame is consumed per tail step. Ordinary return values (ctors, bigints,
// numbers, strings, arrays, closures) never carry `__tc`, so they pass through.
function lean_trampoline(t) {
  while (t && typeof t === 'object') {
    if (t.__tc === 1) { t = t.f(...t.a); continue; }
    // `__tc:2` is a tail-position closure application (emitted for a tail `.ap`):
    // bounce it through lean_apply, which itself returns a `__tc:1`/`__tc:2` thunk
    // for its final saturating step, so the apply chain unrolls in constant stack.
    if (t.__tc === 2) { t = lean_apply(t.clo, t.a); continue; }
    break;
  }
  return t;
}

// ---- closure application (pap/ap model) ----
// A closure value records the worker's FULL arity so apply can do the C runtime's
// three-way dispatch (Lean's lean_apply_n): exact, under (accumulate into a new
// closure), and over (saturate, then re-apply the result to the leftover args).
// pap c ys -> lean_closure(<funRef c>, ARITY, [ys...]) where ARITY is c's full
// IR arity (the param count emitted for funRef c), so apply can branch on
// (arity - args.length) vs the number of args supplied.
function lean_closure(fn, arity, args) {
  return { fn, arity, args };
}

// Returns a `__tc:1` thunk for the FINAL saturating worker call instead of
// calling it directly, so when reached through the trampoline (a tail `.ap`'s
// `__tc:2` thunk, or the wrapped non-tail site below) the driver makes the call
// in constant stack — flattening CPS / continuation tail loops. Intermediate
// over-application steps must force the result NOW to know how to re-apply the
// leftover args; that forcing is bounded by the static curry depth, not by the
// loop iteration count, so it does not grow the stack per iteration.
function lean_apply(clo, more) {
  // Bare JS function: treat as a fully-applied call (IR wraps fn values in pap,
  // but FS.Stream fields and other prelude closures are bare functions).
  if (typeof clo === 'function') return { __tc: 1, f: clo, a: more };
  // A closure without a recorded arity (legacy/erased) falls back to a single
  // concat-and-call; arity-bearing closures use the full three-way dispatch.
  if (typeof clo.arity !== 'number') return { __tc: 1, f: clo.fn, a: clo.args.concat(more) };
  let cur = clo;
  let i = 0;
  while (i < more.length) {
    const need = cur.arity - cur.args.length;
    const avail = more.length - i;
    if (avail < need) {
      return lean_closure(cur.fn, cur.arity, cur.args.concat(more.slice(i)));
    }
    const callArgs = cur.args.concat(more.slice(i, i + need));
    i += need;
    if (i === more.length) return { __tc: 1, f: cur.fn, a: callArgs };
    const res = lean_trampoline({ __tc: 1, f: cur.fn, a: callArgs });
    if (typeof res === 'function') return { __tc: 1, f: res, a: more.slice(i) };
    if (typeof res.arity !== 'number') return { __tc: 1, f: res.fn, a: res.args.concat(more.slice(i)) };
    cur = res;
  }
  return cur;
}

// ---- panic (matches runtime/object.cpp lean_panic_fn) ----
// `panicCore`/`panic`/`panic!`/`unreachable!` compile to a call to
// `lean_panic_fn(default_val, msg)`: it prints the message to stderr (unless
// suppressed), then RETURNS the Inhabited default — it does NOT abort or exit by
// default, so the program stays logically total and continues. Mutable flags
// mirror the C globals; init wraps suppression around the closed-term phase.
let _leanPanicMessages = true;
let _leanExitOnPanic = false;
const lean_set_panic_messages = (b) => { _leanPanicMessages = b ? 1 : 0; };
const lean_set_exit_on_panic = (b) => { _leanExitOnPanic = b ? 1 : 0; };
const lean_panic_fn = (defaultVal, msg) => {
  if (_leanPanicMessages) process.stderr.write(String(msg) + '\n');
  if (_leanExitOnPanic) process.exit(1);
  return defaultVal;
};
// FnBody.unreachable -> lean_internal_panic_unreachable: FATAL. Dead match arms
// are never meant to run; print and terminate (never fall through).
const lean_internal_panic = (msg) => {
  process.stderr.write('INTERNAL PANIC: ' + String(msg) + '\n');
  process.exit(1);
};
const lean_internal_panic_unreachable = () => lean_internal_panic('unreachable code has been reached');

// ---- Nat (bigint, total: /0 and %0 -> 0/lhs; sub is truncated monus) ----
const lean_nat_pow = (a, b) => a ** b;
const lean_nat_pred = (a) => (a > 0n ? a - 1n : 0n);
const lean_nat_gcd = (a, b) => { while (b) { [a, b] = [b, a % b]; } return a; };
const lean_nat_dec_eq = (a, b) => L_bool(a === b);
const lean_nat_dec_lt = (a, b) => L_bool(a < b);
const lean_nat_dec_le = (a, b) => L_bool(a <= b);

// ---- Int (bigint). div/mod = T-rounding; ediv/emod = Euclidean. ----
const lean_int_neg = (a) => -a;
const lean_int_div = (a, b) => (b === 0n ? 0n : a / b);
const lean_int_mod = (a, b) => (b === 0n ? a : a % b);
const lean_int_emod = (a, b) => {
  if (b === 0n) return a;
  const r = a % b;
  return r < 0n ? r + (b < 0n ? -b : b) : r;
};
const lean_int_ediv = (a, b) => {
  if (b === 0n) return 0n;
  const q = a / b, r = a % b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
};
const lean_int_dec_eq = (a, b) => L_bool(a === b);
const lean_int_dec_lt = (a, b) => L_bool(a < b);
const lean_int_dec_le = (a, b) => L_bool(a <= b);

// ---- UIntN / USize: wrap-around modular arithmetic over 2^N ----
// Representation convention (matches scalar literal emission and `switch`):
//   UInt8/16/32 -> plain JS number ; UInt64/USize -> bigint.
// All binary ops wrap mod 2^N. div = unsigned floor (/0 -> 0); mod = unsigned
// remainder (%0 -> dividend). Shift amount reduced mod N. Comparisons unsigned
// and return the scalar 0/1 the emitted `switch` expects.
const _mkUIntNum = (bits) => {
  const mod = 2 ** bits;
  // normalize any JS number into [0, 2^bits) (bits in {8,16,32})
  const m = (x) => { let r = Number(x) % mod; if (r < 0) r += mod; return r; };
  return {
    ofNat: (n) => m(Number(BigInt.asUintN(bits, n))),
    add: (a, b) => m(a + b),
    sub: (a, b) => m(a - b),
    mul: (a, b) => m(Number((BigInt(m(a)) * BigInt(m(b))) % BigInt(mod))),
    div: (a, b) => (b === 0 ? 0 : m(Math.trunc(m(a) / m(b)))),
    mod: (a, b) => (b === 0 ? m(a) : m(m(a) % m(b))),
    land: (a, b) => m(Number(BigInt(m(a)) & BigInt(m(b)))),
    lor: (a, b) => m(Number(BigInt(m(a)) | BigInt(m(b)))),
    xor: (a, b) => m(Number(BigInt(m(a)) ^ BigInt(m(b)))),
    complement: (a) => m(mod - 1 - m(a)),
    neg: (a) => m(-m(a)),
    shiftLeft: (a, b) => m(Number(BigInt(m(a)) << BigInt(b % bits))),
    shiftRight: (a, b) => m(Number(BigInt(m(a)) >> BigInt(b % bits))),
    decEq: (a, b) => L_bool(m(a) === m(b)),
    decLt: (a, b) => L_bool(m(a) < m(b)),
    decLe: (a, b) => L_bool(m(a) <= m(b)),
    toNat: (a) => BigInt(m(a)),
  };
};
const _mkUIntBig = (bits) => {
  const N = BigInt(bits);
  const m = (x) => BigInt.asUintN(bits, x);
  return {
    ofNat: (n) => m(n),
    add: (a, b) => m(a + b),
    sub: (a, b) => m(a - b),
    mul: (a, b) => m(a * b),
    div: (a, b) => (b === 0n ? 0n : m(a / b)),
    mod: (a, b) => (b === 0n ? m(a) : m(a % b)),
    land: (a, b) => m(a & b),
    lor: (a, b) => m(a | b),
    xor: (a, b) => m(a ^ b),
    complement: (a) => m(~a),
    neg: (a) => m(-a),
    shiftLeft: (a, b) => m(a << (b % N)),
    shiftRight: (a, b) => m(a) >> (b % N),
    decEq: (a, b) => L_bool(m(a) === m(b)),
    decLt: (a, b) => L_bool(m(a) < m(b)),
    decLe: (a, b) => L_bool(m(a) <= m(b)),
    toNat: (a) => m(a),
  };
};
// USize / pointer width. The C runtime's size_t == sizeof(void*) (8 on 64-bit,
// 4 on 32-bit), and usize ctor slots / the packed-usize accessor width are
// derived from it. lean-js targets a 64-bit-like host (BigInt for 64-bit), so
// WORD_BITS defaults to 64; route every usize-width decision through this single
// constant so a 32-bit profile is a one-line change.
const WORD_BITS = 64;
const _u8 = _mkUIntNum(8), _u16 = _mkUIntNum(16), _u32 = _mkUIntNum(32);
const _u64 = _mkUIntBig(64), _usz = _mkUIntBig(WORD_BITS);

const lean_uint8_of_nat = _u8.ofNat, lean_uint8_add = _u8.add, lean_uint8_sub = _u8.sub, lean_uint8_mul = _u8.mul, lean_uint8_div = _u8.div, lean_uint8_mod = _u8.mod, lean_uint8_land = _u8.land, lean_uint8_lor = _u8.lor, lean_uint8_xor = _u8.xor, lean_uint8_complement = _u8.complement, lean_uint8_neg = _u8.neg, lean_uint8_shift_left = _u8.shiftLeft, lean_uint8_shift_right = _u8.shiftRight, lean_uint8_dec_eq = _u8.decEq, lean_uint8_dec_lt = _u8.decLt, lean_uint8_dec_le = _u8.decLe, lean_uint8_to_nat = _u8.toNat;
const lean_uint16_of_nat = _u16.ofNat, lean_uint16_add = _u16.add, lean_uint16_sub = _u16.sub, lean_uint16_mul = _u16.mul, lean_uint16_div = _u16.div, lean_uint16_mod = _u16.mod, lean_uint16_land = _u16.land, lean_uint16_lor = _u16.lor, lean_uint16_xor = _u16.xor, lean_uint16_complement = _u16.complement, lean_uint16_neg = _u16.neg, lean_uint16_shift_left = _u16.shiftLeft, lean_uint16_shift_right = _u16.shiftRight, lean_uint16_dec_eq = _u16.decEq, lean_uint16_dec_lt = _u16.decLt, lean_uint16_dec_le = _u16.decLe, lean_uint16_to_nat = _u16.toNat;
const lean_uint32_add = _u32.add, lean_uint32_sub = _u32.sub, lean_uint32_mul = _u32.mul, lean_uint32_div = _u32.div, lean_uint32_mod = _u32.mod, lean_uint32_land = _u32.land, lean_uint32_lor = _u32.lor, lean_uint32_xor = _u32.xor, lean_uint32_complement = _u32.complement, lean_uint32_neg = _u32.neg, lean_uint32_shift_left = _u32.shiftLeft, lean_uint32_shift_right = _u32.shiftRight, lean_uint32_dec_eq = _u32.decEq, lean_uint32_dec_lt = _u32.decLt, lean_uint32_dec_le = _u32.decLe, lean_uint32_to_nat = _u32.toNat;
const lean_uint64_of_nat = _u64.ofNat, lean_uint64_add = _u64.add, lean_uint64_sub = _u64.sub, lean_uint64_mul = _u64.mul, lean_uint64_div = _u64.div, lean_uint64_mod = _u64.mod, lean_uint64_land = _u64.land, lean_uint64_lor = _u64.lor, lean_uint64_xor = _u64.xor, lean_uint64_complement = _u64.complement, lean_uint64_neg = _u64.neg, lean_uint64_shift_left = _u64.shiftLeft, lean_uint64_shift_right = _u64.shiftRight, lean_uint64_dec_eq = _u64.decEq, lean_uint64_dec_lt = _u64.decLt, lean_uint64_dec_le = _u64.decLe, lean_uint64_to_nat = _u64.toNat;
const lean_usize_of_nat = _usz.ofNat, lean_usize_add = _usz.add, lean_usize_sub = _usz.sub, lean_usize_mul = _usz.mul, lean_usize_div = _usz.div, lean_usize_mod = _usz.mod, lean_usize_land = _usz.land, lean_usize_lor = _usz.lor, lean_usize_xor = _usz.xor, lean_usize_complement = _usz.complement, lean_usize_neg = _usz.neg, lean_usize_shift_left = _usz.shiftLeft, lean_usize_shift_right = _usz.shiftRight, lean_usize_dec_eq = _usz.decEq, lean_usize_dec_lt = _usz.decLt, lean_usize_dec_le = _usz.decLe, lean_usize_to_nat = _usz.toNat;
// UInt64 -> USize truncates to the platform word width; on the 64-bit profile
// this is an identity re-mask, on a 32-bit profile it drops the high 32 bits.
const lean_uint64_to_usize = (x) => BigInt.asUintN(WORD_BITS, x);

// ---- Signed fixed-width ints Int8/16/32/64/ISize (BigInt + asIntN) ----
// Uniform bigint representation across all widths (avoids number/bigint mixing).
// Two's-complement wrap on construction and every op. div truncates toward zero
// and (MIN/-1) wraps to MIN (no trap); mod takes the sign of the dividend;
// div-by-zero -> 0, mod-by-zero -> lhs (total, like Int). shiftRight is
// arithmetic (sign-extending); shift amount is masked by width. complement = ~.
const _mkSInt = (bits) => {
  const B = BigInt(bits);
  const w = (x) => BigInt.asIntN(bits, x);
  const sh = (b) => ((b % B) + B) % B;
  return {
    // toInt reinterprets the raw stored bit pattern as a signed two's-complement
    // Int. A packed signed field is stored/read through the UNSIGNED DataView
    // path (sproj/sset only know uintN at Lean 4.29.1 — no signed IRType), so a
    // negative Int8 like -5 arrives here as the unsigned byte 251 (a JS number);
    // BigInt.asIntN recovers -5. Already-signed bigint inputs are idempotent in
    // range, so the same boundary works for normal Int8 arithmetic values too.
    ofInt: w, ofNat: w, toInt: (x) => w(BigInt(x)),
    add: (a, b) => w(a + b), sub: (a, b) => w(a - b), mul: (a, b) => w(a * b),
    neg: (a) => w(-a),
    div: (a, b) => (b === 0n ? 0n : w(a / b)),
    mod: (a, b) => (b === 0n ? a : w(a % b)),
    land: (a, b) => w(a & b), lor: (a, b) => w(a | b), xor: (a, b) => w(a ^ b),
    complement: (a) => w(~a),
    shiftLeft: (a, b) => w(a << sh(b)),
    shiftRight: (a, b) => w(a >> sh(b)),
    decEq: (a, b) => L_bool(a === b), decLt: (a, b) => L_bool(a < b), decLe: (a, b) => L_bool(a <= b),
  };
};
const _i8 = _mkSInt(8), _i16 = _mkSInt(16), _i32 = _mkSInt(32), _i64 = _mkSInt(64), _isz = _mkSInt(64);
const lean_int8_of_int = _i8.ofInt, lean_int8_of_nat = _i8.ofNat, lean_int8_to_int = _i8.toInt, lean_int8_add = _i8.add, lean_int8_sub = _i8.sub, lean_int8_mul = _i8.mul, lean_int8_div = _i8.div, lean_int8_mod = _i8.mod, lean_int8_neg = _i8.neg, lean_int8_land = _i8.land, lean_int8_lor = _i8.lor, lean_int8_xor = _i8.xor, lean_int8_complement = _i8.complement, lean_int8_shift_left = _i8.shiftLeft, lean_int8_shift_right = _i8.shiftRight, lean_int8_dec_eq = _i8.decEq, lean_int8_dec_lt = _i8.decLt, lean_int8_dec_le = _i8.decLe;
const lean_int16_of_int = _i16.ofInt, lean_int16_of_nat = _i16.ofNat, lean_int16_to_int = _i16.toInt, lean_int16_add = _i16.add, lean_int16_sub = _i16.sub, lean_int16_mul = _i16.mul, lean_int16_div = _i16.div, lean_int16_mod = _i16.mod, lean_int16_neg = _i16.neg, lean_int16_land = _i16.land, lean_int16_lor = _i16.lor, lean_int16_xor = _i16.xor, lean_int16_complement = _i16.complement, lean_int16_shift_left = _i16.shiftLeft, lean_int16_shift_right = _i16.shiftRight, lean_int16_dec_eq = _i16.decEq, lean_int16_dec_lt = _i16.decLt, lean_int16_dec_le = _i16.decLe;
const lean_int32_of_int = _i32.ofInt, lean_int32_of_nat = _i32.ofNat, lean_int32_to_int = _i32.toInt, lean_int32_add = _i32.add, lean_int32_sub = _i32.sub, lean_int32_mul = _i32.mul, lean_int32_div = _i32.div, lean_int32_mod = _i32.mod, lean_int32_neg = _i32.neg, lean_int32_land = _i32.land, lean_int32_lor = _i32.lor, lean_int32_xor = _i32.xor, lean_int32_complement = _i32.complement, lean_int32_shift_left = _i32.shiftLeft, lean_int32_shift_right = _i32.shiftRight, lean_int32_dec_eq = _i32.decEq, lean_int32_dec_lt = _i32.decLt, lean_int32_dec_le = _i32.decLe;
const lean_int64_of_int = _i64.ofInt, lean_int64_of_nat = _i64.ofNat, lean_int64_to_int_sint = _i64.toInt, lean_int64_add = _i64.add, lean_int64_sub = _i64.sub, lean_int64_mul = _i64.mul, lean_int64_div = _i64.div, lean_int64_mod = _i64.mod, lean_int64_neg = _i64.neg, lean_int64_land = _i64.land, lean_int64_lor = _i64.lor, lean_int64_xor = _i64.xor, lean_int64_complement = _i64.complement, lean_int64_shift_left = _i64.shiftLeft, lean_int64_shift_right = _i64.shiftRight, lean_int64_dec_eq = _i64.decEq, lean_int64_dec_lt = _i64.decLt, lean_int64_dec_le = _i64.decLe;
const lean_isize_of_int = _isz.ofInt, lean_isize_of_nat = _isz.ofNat, lean_isize_to_int_sint = _isz.toInt, lean_isize_add = _isz.add, lean_isize_sub = _isz.sub, lean_isize_mul = _isz.mul, lean_isize_div = _isz.div, lean_isize_mod = _isz.mod, lean_isize_neg = _isz.neg, lean_isize_land = _isz.land, lean_isize_lor = _isz.lor, lean_isize_xor = _isz.xor, lean_isize_complement = _isz.complement, lean_isize_shift_left = _isz.shiftLeft, lean_isize_shift_right = _isz.shiftRight, lean_isize_dec_eq = _isz.decEq, lean_isize_dec_lt = _isz.decLt, lean_isize_dec_le = _isz.decLe;

// ---- Float (IEEE 754 binary64 == JS number). IEEE div-by-zero (Inf/NaN). ----
const lean_float_add = (a, b) => a + b;
const lean_float_sub = (a, b) => a - b;
const lean_float_mul = (a, b) => a * b;
const lean_float_div = (a, b) => a / b;
const lean_float_negate = (a) => -a;
const lean_float_beq = (a, b) => L_bool(a === b);
const lean_float_decLt = (a, b) => L_bool(a < b);
const lean_float_decLe = (a, b) => L_bool(a <= b);
const lean_float_isnan = (a) => L_bool(Number.isNaN(a));
const lean_float_isfinite = (a) => L_bool(Number.isFinite(a));
const lean_float_isinf = (a) => L_bool(a === Infinity || a === -Infinity);
const lean_float_sqrt = Math.sqrt, lean_float_sin = Math.sin, lean_float_cos = Math.cos;
const lean_float_exp = Math.exp, lean_float_log = Math.log, lean_float_pow = Math.pow;
const lean_float_floor = Math.floor, lean_float_ceil = Math.ceil, lean_float_abs = Math.abs;
const lean_float_round = (a) => Math.sign(a) * Math.round(Math.abs(a));
const lean_float_scaleb = (x, i) => x * Math.pow(2, Number(i));
// libm transcendentals. JS Math.* and C libm are each typically <=1 ULP but
// neither IEEE-754 nor ECMAScript mandates correctly-rounded results for these,
// so they are NOT guaranteed bit-exact vs the C backend; the diff-test compares
// through Float.toString (C `%f`, 6 fixed decimals), which absorbs the sub-ULP
// noise. sqrt/comparisons/+-*//div ARE IEEE-correctly-rounded and bit-exact.
const lean_float_tan = Math.tan;
const lean_float_asin = Math.asin, lean_float_acos = Math.acos, lean_float_atan = Math.atan;
const lean_float_atan2 = Math.atan2;
const lean_float_sinh = Math.sinh, lean_float_cosh = Math.cosh, lean_float_tanh = Math.tanh;
const lean_float_asinh = Math.asinh, lean_float_acosh = Math.acosh, lean_float_atanh = Math.atanh;
const lean_float_exp2 = (a) => Math.pow(2, a);
const lean_float_log2 = Math.log2, lean_float_log10 = Math.log10;
const lean_float_cbrt = Math.cbrt;
// frExp / ofBits / toBits are EXACT bit reinterpretations (DataView), matching
// the C externs lean_float_frexp / lean_float_of_bits / lean_float_to_bits.
const _f64buf = new ArrayBuffer(8);
const _f64dv = new DataView(_f64buf);
const lean_float_to_bits = (x) => { _f64dv.setFloat64(0, x); return _f64dv.getBigUint64(0); };
const lean_float_of_bits = (b) => { _f64dv.setBigUint64(0, BigInt.asUintN(64, b)); return _f64dv.getFloat64(0); };
// Float.frExp x = (m, e) with x = m * 2^e and 0.5 <= |m| < 1 (C frexp). Returns
// the Lean pair ctor {tag:0, fields:[m, e]} (e is an Int = bigint).
const lean_float_frexp = (x) => {
  if (x === 0 || !Number.isFinite(x)) return { tag: 0, fields: [x, 0n] };
  const b = lean_float_to_bits(x);
  let e = Number((b >> 52n) & 0x7ffn);
  let m;
  if (e === 0) {
    const sub = x / Math.pow(2, -1074);
    const fr = lean_float_frexp(sub);
    return { tag: 0, fields: [fr.fields[0], fr.fields[1] - 1074n] };
  } else {
    e -= 1022;
    m = lean_float_of_bits((b & ~(0x7ffn << 52n)) | (1022n << 52n));
  }
  return { tag: 0, fields: [m, BigInt(e)] };
};
const lean_float_to_uint = (a, bits) => {
  if (Number.isNaN(a) || a <= 0) return bits <= 32 ? 0 : 0n;
  const max = (1n << BigInt(bits)) - 1n;
  let t = BigInt(Math.trunc(a));
  if (t > max) t = max;
  return bits <= 32 ? Number(t) : t;
};
const lean_float_to_uint8 = (a) => lean_float_to_uint(a, 8);
const lean_float_to_uint16 = (a) => lean_float_to_uint(a, 16);
const lean_float_to_uint32 = (a) => lean_float_to_uint(a, 32);
const lean_float_to_uint64 = (a) => lean_float_to_uint(a, 64);
const lean_float_to_usize = (a) => lean_float_to_uint(a, 64);
// Float.ofScientific m e exp = m * 10^(e ? -exp : exp); parse via JS number
// literal for a correctly-rounded binary64 result (matches the extern).
const lean_float_of_scientific = (m, e, exp) =>
  Number(`${m}e${e ? '-' : ''}${exp}`);

// ---- Float32 (IEEE 754 binary32). Round every result via Math.fround. ----
const _f = Math.fround;
const lean_float32_add = (a, b) => _f(_f(a) + _f(b));
const lean_float32_sub = (a, b) => _f(_f(a) - _f(b));
const lean_float32_mul = (a, b) => _f(_f(a) * _f(b));
const lean_float32_div = (a, b) => _f(_f(a) / _f(b));
const lean_float32_negate = (a) => _f(-_f(a));
const lean_float32_beq = (a, b) => L_bool(_f(a) === _f(b));
const lean_float32_decLt = (a, b) => L_bool(_f(a) < _f(b));
const lean_float32_decLe = (a, b) => L_bool(_f(a) <= _f(b));
const lean_float32_to_float = (a) => _f(a);
const lean_float_to_float32 = (a) => _f(a);

// ---- Float.toString / Float32.toString : C `%f` (6 fixed decimals) ----
// Matches Lean: NaN -> "NaN"; +/-inf -> "inf"/"-inf"; sign of -0.0 preserved;
// |x| >= 1e21 falls back to the exact integer digits (JS toFixed would give
// exponential there). Float32 first rounds to binary32, then prints like Float.
const lean_float_to_string = (x) => {
  if (Number.isNaN(x)) return 'NaN';
  if (x === Infinity) return 'inf';
  if (x === -Infinity) return '-inf';
  const neg = x < 0 || Object.is(x, -0);
  const a = Math.abs(x);
  const s = a < 1e21 ? a.toFixed(6) : (BigInt(a).toString() + '.000000');
  return neg ? '-' + s : s;
};
const lean_float32_to_string = (x) => lean_float_to_string(Math.fround(x));
const lean_float32_sqrt = (a) => _f(Math.sqrt(_f(a)));
const lean_float32_abs = (a) => _f(Math.abs(_f(a)));
const lean_float32_floor = (a) => _f(Math.floor(_f(a)));
const lean_float32_ceil = (a) => _f(Math.ceil(_f(a)));
const lean_float32_round = (a) => _f(Math.sign(_f(a)) * Math.round(Math.abs(_f(a))));
const lean_float32_neg = lean_float32_negate;
const lean_float32_isnan = (a) => L_bool(Number.isNaN(_f(a)));
const lean_float32_isfinite = (a) => L_bool(Number.isFinite(_f(a)));
const lean_float32_isinf = (a) => { const v = _f(a); return L_bool(v === Infinity || v === -Infinity); };
// Float32 libm transcendentals: Lean uses the single-precision libm symbols
// (sinf, ...); the closest JS path is fround(Math.fn(fround x)) (double then
// narrow), a DIFFERENT rounding path that can differ by >1 ULP at f32 precision,
// so these are tolerance-only (compared through Float32.toString 6-digit output).
const _f32 = (fn) => (a) => _f(fn(_f(a)));
const lean_float32_sin = _f32(Math.sin), lean_float32_cos = _f32(Math.cos), lean_float32_tan = _f32(Math.tan);
const lean_float32_asin = _f32(Math.asin), lean_float32_acos = _f32(Math.acos), lean_float32_atan = _f32(Math.atan);
const lean_float32_atan2 = (a, b) => _f(Math.atan2(_f(a), _f(b)));
const lean_float32_sinh = _f32(Math.sinh), lean_float32_cosh = _f32(Math.cosh), lean_float32_tanh = _f32(Math.tanh);
const lean_float32_asinh = _f32(Math.asinh), lean_float32_acosh = _f32(Math.acosh), lean_float32_atanh = _f32(Math.atanh);
const lean_float32_exp = _f32(Math.exp), lean_float32_exp2 = _f32((a) => Math.pow(2, a));
const lean_float32_log = _f32(Math.log), lean_float32_log2 = _f32(Math.log2), lean_float32_log10 = _f32(Math.log10);
const lean_float32_pow = (a, b) => _f(Math.pow(_f(a), _f(b)));
const lean_float32_cbrt = _f32(Math.cbrt);
const lean_float32_to_uint8 = (a) => lean_float_to_uint(_f(a), 8);
const lean_float32_to_uint16 = (a) => lean_float_to_uint(_f(a), 16);
const lean_float32_to_uint32 = (a) => lean_float_to_uint(_f(a), 32);
const lean_float32_to_uint64 = (a) => lean_float_to_uint(_f(a), 64);
const lean_float32_to_usize = (a) => lean_float_to_uint(_f(a), 64);
// Float32 bit reinterpret (EXACT): lean_float32_of_bits / to_bits use UInt32.
const _f32buf = new ArrayBuffer(4);
const _f32dv = new DataView(_f32buf);
const lean_float32_to_bits = (x) => { _f32dv.setFloat32(0, _f(x)); return _f32dv.getUint32(0); };
const lean_float32_of_bits = (b) => { _f32dv.setUint32(0, Number(BigInt.asUintN(32, BigInt(b)))); return _f32dv.getFloat32(0); };
const lean_float32_scaleb = (x, i) => _f(_f(x) * Math.pow(2, Number(i)));
const lean_float32_frexp = (x) => {
  const fr = lean_float_frexp(_f(x));
  return { tag: 0, fields: [_f(fr.fields[0]), fr.fields[1]] };
};
const lean_uint8_to_float32 = (a) => _f(Number(a));
const lean_uint16_to_float32 = (a) => _f(Number(a));
const lean_uint32_to_float32 = (a) => _f(Number(a));
const lean_uint64_to_float32 = (a) => _f(Number(a));
const lean_usize_to_float32 = (a) => _f(Number(a));
const lean_usize_to_float = (a) => Number(a);

// ---- Char ----
const lean_uint32_of_nat = (n) => Number(n & 0xffffffffn);
const lean_char_to_nat = (c) => BigInt(c);

// ---- String: UTF-8 / code-point semantics ----
const lean_string_length = (s) => BigInt([...s].length);
const lean_string_append = (a, b) => a + b;
const lean_string_push = (s, c) => s + String.fromCodePoint(c);
const lean_string_dec_eq = (a, b) => L_bool(a === b);
const lean_string_isempty = (s) => L_bool(s.length === 0);
// String.hash (extern lean_string_hash): MurmurHash64A over the UTF-8 bytes
// with seed 11, transcribed from the runtime's hash_str so bucket layout (and
// thus HashMap/HashSet iteration order) is bit-identical to the native backend.
const _MURMUR_M = 0xc6a4a7935bd1e995n;
const _MURMUR_R = 47n;
const _wrap64 = (x) => BigInt.asUintN(64, x);
// mixHash (extern lean_uint64_mix_hash): the runtime's lean_uint64_mix_hash,
// used by Hashable for Prod/Option/Array/List and pointer hashing. Bit-exact.
const lean_uint64_mix_hash = (h, k) => {
  const m = _MURMUR_M, r = _MURMUR_R;
  k = _wrap64(k * m); k ^= k >> r; k ^= m;
  h ^= k; h = _wrap64(h * m);
  return _wrap64(h);
};
const lean_string_hash = (s) => {
  const b = _utf8enc.encode(s), len = b.length, m = _MURMUR_M, r = _MURMUR_R;
  let h = _wrap64(11n ^ _wrap64(BigInt(len) * m));
  const nblocks = (len / 8) | 0;
  for (let i = 0; i < nblocks; i++) {
    let k = 0n;
    for (let j = 0; j < 8; j++) k |= BigInt(b[i * 8 + j]) << BigInt(8 * j);
    k = _wrap64(k * m); k ^= k >> r; k = _wrap64(k * m);
    h ^= k; h = _wrap64(h * m);
  }
  const t = nblocks * 8, rem = len & 7;
  if (rem >= 7) h ^= BigInt(b[t + 6]) << 48n;
  if (rem >= 6) h ^= BigInt(b[t + 5]) << 40n;
  if (rem >= 5) h ^= BigInt(b[t + 4]) << 32n;
  if (rem >= 4) h ^= BigInt(b[t + 3]) << 24n;
  if (rem >= 3) h ^= BigInt(b[t + 2]) << 16n;
  if (rem >= 2) h ^= BigInt(b[t + 1]) << 8n;
  if (rem >= 1) { h ^= BigInt(b[t]); h = _wrap64(h * m); }
  h ^= h >> r; h = _wrap64(h * m); h ^= h >> r;
  return _wrap64(h);
};
// String.data / String.toList -> List Char (code points): tag 0 = nil, tag 1 = cons{head,tail}
const lean_string_data = (s) =>
  [...s].reduceRight((tl, ch) => ({ tag: 1, fields: [ch.codePointAt(0), tl] }), 0);
// String.mk : List Char -> String
const lean_string_mk = (lst) => {
  let out = '';
  let cur = lst;
  while (typeof cur !== 'number' && cur.tag === 1) {
    out += String.fromCodePoint(cur.fields[0]);
    cur = cur.fields[1];
  }
  return out;
};

// ---- String: UTF-8 byte-position layer (String.Pos == UTF-8 byte offset) ----
// Lean indexes the raw UTF-8 byte buffer, not JS UTF-16 units. Positions are
// byte offsets (bigint). We cache an encoded view per string.
const _utf8enc = new TextEncoder();
const _utf8dec = new TextDecoder('utf-8', { fatal: false });
const _utf8cache = new WeakMap();
const _bytesOf = (s) => {
  if (typeof s !== 'object') {
    const b = _utf8enc.encode(s);
    return b;
  }
  return s;
};
const lean_string_bytes = (s) => _utf8enc.encode(s);
// utf8Size of a code point (matches Char.utf8Size).
const lean_char_utf8_size = (c) =>
  c <= 0x7f ? 1n : c <= 0x7ff ? 2n : c <= 0xffff ? 3n : 4n;
// byteLen of the UTF-8 sequence whose first byte is b.
const _u8seqLen = (b) => (b < 0x80 ? 1 : b < 0xe0 ? 2 : b < 0xf0 ? 3 : 4);
const _u8isFirst = (b) => (b & 0xc0) !== 0x80;
const _decodeAt = (bytes, i) => {
  const c0 = bytes[i];
  if (c0 < 0x80) return [c0, 1];
  if (c0 < 0xe0) return [((c0 & 0x1f) << 6) | (bytes[i + 1] & 0x3f), 2];
  if (c0 < 0xf0)
    return [((c0 & 0x0f) << 12) | ((bytes[i + 1] & 0x3f) << 6) | (bytes[i + 2] & 0x3f), 3];
  return [((c0 & 0x07) << 18) | ((bytes[i + 1] & 0x3f) << 12) |
          ((bytes[i + 2] & 0x3f) << 6) | (bytes[i + 3] & 0x3f), 4];
};
// String.utf8ByteSize / rawEndPos.byteIdx
const lean_string_utf8_byte_size = (s) => BigInt(_utf8enc.encode(s).length);
// String.get : char at byte pos p, or 'A' (U+0041) if mid-char / out of range.
const lean_string_utf8_get = (s, p) => {
  const b = _utf8enc.encode(s), i = Number(p);
  if (i < 0 || i >= b.length || !_u8isFirst(b[i])) return 0x41;
  return _decodeAt(b, i)[0];
};
// String.get! : same value (panics in Lean on bad pos; here returns default).
const lean_string_utf8_get_bang = lean_string_utf8_get;
// String.get? : some codepoint (tag 1) or none (tag 0).
const lean_string_utf8_get_opt = (s, p) => {
  const b = _utf8enc.encode(s), i = Number(p);
  if (i < 0 || i >= b.length || !_u8isFirst(b[i])) return 0;
  return { tag: 1, fields: [_decodeAt(b, i)[0]] };
};
// String.next : advance byte offset by the char's UTF-8 size (1 at end/invalid).
const lean_string_utf8_next = (s, p) =>
  p + lean_char_utf8_size(lean_string_utf8_get(s, p));
// String.prev : start byte of the char before p; prev(0)=0.
const lean_string_utf8_prev = (s, p) => {
  const b = _utf8enc.encode(s);
  let i = Number(p);
  if (i <= 0) return 0n;
  if (i > b.length) return BigInt(i - 1);
  i -= 1;
  while (i > 0 && !_u8isFirst(b[i])) i -= 1;
  return BigInt(i);
};
// String.atEnd : byteIdx >= utf8ByteSize.
const lean_string_utf8_at_end = (s, p) =>
  L_bool(Number(p) >= _utf8enc.encode(s).length);
// String.extract : copy bytes [b, e); "" if b>=e; e clamps to end.
const lean_string_utf8_extract = (s, lo, hi) => {
  const bytes = _utf8enc.encode(s);
  let a = Number(lo), z = Number(hi);
  if (a >= z) return '';
  if (z > bytes.length) z = bytes.length;
  if (a > z) a = z;
  return _utf8dec.decode(bytes.slice(a, z));
};
// String.set : replace the char starting at byte pos p with codepoint c. A pos
// that is out of range or mid-char leaves the string unchanged (Lean returns s).
const lean_string_utf8_set = (s, p, c) => {
  const b = _utf8enc.encode(s), i = Number(p);
  if (i < 0 || i >= b.length || !_u8isFirst(b[i])) return s;
  const n = _decodeAt(b, i)[1];
  return _utf8dec.decode(b.slice(0, i)) + String.fromCodePoint(c) + _utf8dec.decode(b.slice(i + n));
};
// String.posOf : byte pos of first occurrence of c, else utf8ByteSize.
const lean_string_utf8_pos_of = (s, c) => {
  const b = _utf8enc.encode(s);
  for (let i = 0; i < b.length; ) {
    const [cp, n] = _decodeAt(b, i);
    if (cp === c) return BigInt(i);
    i += n;
  }
  return BigInt(b.length);
};
const lean_string_contains = (s, c) =>
  L_bool(Number(lean_string_utf8_pos_of(s, c)) !== _utf8enc.encode(s).length);
// String.get_byte : raw byte at offset.
const lean_string_get_byte = (s, p) => _utf8enc.encode(s)[Number(p)];
// String.getUTF8Byte (extern lean_string_get_byte_fast): byte at byte offset p.
// The dependent `p < rawEndPos` proof arg is erased/dropped by the emitter.
const lean_string_get_byte_fast = (s, p) => _utf8enc.encode(s)[Number(p)];
// String.decodeChar (extern lean_string_utf8_get_fast): decode the char whose
// UTF-8 sequence begins at byte offset; same decode as String.get.
const lean_string_utf8_get_fast = (s, p) => lean_string_utf8_get(s, p);
// String.Internal.isPrefixOf (extern lean_string_isprefixof): p, s -> Bool.
const lean_string_isprefixof = (p, s) => L_bool(s.startsWith(p));
// String.Internal.any (extern lean_string_any): apply the Char->Bool closure to
// each code point until one returns true (Bool scalar 1).
const lean_string_any = (s, p) => {
  for (const ch of s) if (lean_trampoline(lean_apply(p, [ch.codePointAt(0)]))) return 1;
  return 0;
};

// ---- ByteArray: a Uint8Array (matches IO read buffers). Setters copy, like
// Array, because the JS reference graph cannot honor Lean's uniqueness. ----
const lean_mk_empty_byte_array = (_cap) => new Uint8Array(0);
const lean_byte_array_size = (a) => BigInt(a.length);
const lean_sarray_size = (a) => BigInt(a.length);
const lean_byte_array_push = (a, b) => {
  const r = new Uint8Array(a.length + 1);
  r.set(a);
  r[a.length] = Number(b) & 0xff;
  return r;
};
// ByteArray.get! : byte at index; out-of-bounds panics in Lean, returns 0 here.
const lean_byte_array_get = (a, i) => { const x = a[Number(i)]; return x === undefined ? 0 : x; };
const lean_byte_array_fget = (a, i) => a[Number(i)];
const lean_byte_array_uget = (a, i) => a[Number(i)];
const lean_byte_array_set = (a, i, b) => {
  const j = Number(i);
  if (j < 0 || j >= a.length) return a;
  const r = a.slice();
  r[j] = Number(b) & 0xff;
  return r;
};
const lean_byte_array_fset = lean_byte_array_set;
const lean_byte_array_uset = lean_byte_array_set;
// ByteArray.copySlice src srcOff dest destOff len exact : splice src[srcOff,+len)
// into dest at destOff, growing dest, exactly as the Lean Array-extract spec.
const lean_byte_array_copy_slice = (src, srcOff, dest, destOff, len, _exact) => {
  const so = Number(srcOff), doff = Number(destOff), n = Number(len);
  const take = Math.min(n, Math.max(0, src.length - so));
  const head = dest.subarray(0, doff);
  const mid = src.subarray(so, so + take);
  const tail = dest.subarray(doff + take);
  const r = new Uint8Array(head.length + mid.length + tail.length);
  r.set(head, 0);
  r.set(mid, head.length);
  r.set(tail, head.length + mid.length);
  return r;
};
// String.toByteArray / toUTF8 (extern lean_string_to_utf8).
const lean_string_to_utf8 = (s) => _utf8enc.encode(s);
// String.ofByteArray / fromUTF8(!)/Unchecked (extern lean_string_from_utf8_unchecked).
const lean_string_from_utf8_unchecked = (b) => _utf8dec.decode(b);
// ByteArray.validateUTF8 (extern lean_string_validate_utf8): Bool scalar.
const lean_string_validate_utf8 = (b) => {
  try { new TextDecoder('utf-8', { fatal: true }).decode(b); return 1; }
  catch { return 0; }
};

// ---- FloatArray: packed doubles -> Float64Array (mirrors ByteArray=Uint8Array).
// The C runtime stores packed `double`s in an sarray; Float64Array is the exact
// JS analog. Setters copy-on-write, like the Array/ByteArray externs, because JS
// arrays are reference-shared and the compiler's unique-assumed paths would
// otherwise corrupt the caller. lean_sarray_size above already returns the length.
// FloatArray.mk (Array Float -> FloatArray): boxed plain array -> packed.
const lean_float_array_mk = (a) => Float64Array.from(a);
// FloatArray.data (FloatArray -> Array Float): packed -> boxed plain array.
const lean_float_array_data = (a) => Array.from(a);
const lean_copy_float_array = (a) => a.slice();
// emptyWithCapacity: capacity is advisory only.
const lean_mk_empty_float_array = (_cap) => new Float64Array(0);
// size : Nat (boxed bigint). usize : USize (bigint).
const lean_float_array_size = (a) => BigInt(a.length);
const lean_float_array_push = (a, d) => {
  const r = new Float64Array(a.length + 1);
  r.set(a);
  r[a.length] = d;          // d is a JS number (Float)
  return r;
};
const lean_float_array_uget = (a, i) => a[Number(i)];
const lean_float_array_fget = (a, i) => a[Number(i)];
// FloatArray.get! : OOB returns 0.0 (matches lean.h lean_float_array_get).
const lean_float_array_get = (a, i) => { const x = a[Number(i)]; return x === undefined ? 0.0 : x; };
// uset/fset : copy-on-write (same as Array/ByteArray setters).
const lean_float_array_uset = (a, i, d) => { const r = a.slice(); r[Number(i)] = d; return r; };
const lean_float_array_fset = lean_float_array_uset;
// FloatArray.set! : OOB returns the array unchanged (matches lean.h).
const lean_float_array_set = (a, i, d) => {
  const j = Number(i);
  if (j < 0 || j >= a.length) return a;
  const r = a.slice(); r[j] = d; return r;
};

// ---- dbgTrace / dbgTraceIfShared / dbgSleep ----
// lean_dbg_trace(s, fn): write s + '\n' to stderr, then force the thunk `fn`
// applied to Unit. Like lean_string_any, it forces a closure, so it has an
// explicit emitKnownFap arm + an emitKnownFapSpecialNames entry.
const lean_dbg_trace = (s, fn) => {
  process.stderr.write(String(s) + '\n');
  return lean_trampoline(lean_apply(fn, [0]));   // 0 = boxed Unit
};
// dbgTraceIfShared (s) (a): prints s only if `a` is RC-shared (RC(a) > 1). Its
// second arg is the VALUE `a` itself (not a thunk), and it returns `a`. Refcount
// is not modeled under JS GC, so a value is never "shared" in the RC sense:
// never print, just return `a` -- observably identical to native here.
const lean_dbg_trace_if_shared = (_s, a) => a;
// A millisecond sleep is not observable in program output; just force the thunk.
const lean_dbg_sleep = (_ms, fn) => lean_trampoline(lean_apply(fn, [0]));

// ---- pointer utilities (the SAFE surface is observationally pure) ----
// withPtrAddr's proof obligation (∀ u1 u2, k u1 = k u2) guarantees the result is
// address-independent, so a constant address is faithful for every safe caller.
const lean_ptr_addr = (_a) => 0n;          // USize (bigint)
// isExclusiveUnsafe: no RC in JS; report non-exclusive (0) so copy-on-write paths
// stay value-correct (the compiler already forced isShared elsewhere). Bool scalar.
const lean_is_exclusive_obj = (_a) => 0;

// ---- Array: JS array. get is bounds-checked w/ default; push mutates. ----
const lean_array_get_size = (a) => BigInt(a.length);
const lean_array_fget = (a, i) => a[Number(i)];
// Array.get!Internal (extern lean_array_get): the C signature passes the
// Inhabited default FIRST, then the array, then the index (a[i]! lowers here).
const lean_array_get = (dflt, a, i) => {
  const idx = Number(i); return idx >= 0 && idx < a.length ? a[idx] : dflt;
};
// Array.get!InternalBorrowed (extern lean_array_get_borrowed): identical
// signature and semantics to lean_array_get; the only C-level difference is the
// borrowed-vs-owned refcount on `a`, which is a no-op in GC'd JS. The compiler
// emits this variant when the indexed element is only borrowed (e.g. a[i]!.size).
const lean_array_get_borrowed = lean_array_get;
const lean_array_uget = (a, i) => a[Number(i)];
// Array.getInternalBorrowed (C lean_array_fget_borrowed) and Array.ugetBorrowed
// (C lean_array_uget_borrowed): the borrowed twins of fget/uget. The only
// C-level difference is the borrowed-vs-owned refcount on the returned element,
// which is a no-op in GC'd JS, so each is a direct alias of its owned variant.
// Defined as named symbols (symmetric with lean_array_get_borrowed) so the
// prelude is self-documenting rather than routing the Lean decls to lean_array_uget.
const lean_array_fget_borrowed = lean_array_fget;
const lean_array_uget_borrowed = lean_array_uget;
// Setters return a fresh array (functional), mirroring the ctor reuse/copy
// model: JS arrays are reference-shared with no refcount, so in-place updates
// from the compiler's unsafe (assumed-unique) map/foldl paths would corrupt the
// caller's array. Copying keeps Array semantics pure and aliases intact.
const lean_array_set = (a, i, v) => { const b = a.slice(); b[Number(i)] = v; return b; };
const lean_array_push = (a, v) => { const b = a.slice(); b.push(v); return b; };
const lean_array_pop = (a) => { const b = a.slice(); b.pop(); return b; };
const lean_array_swap = (a, i, j) => {
  const b = a.slice(), x = Number(i), y = Number(j); [b[x], b[y]] = [b[y], b[x]]; return b;
};
const lean_array_uset = (a, i, v) => { const b = a.slice(); b[Number(i)] = v; return b; };
const lean_array_usize = (a) => BigInt(a.length);
const lean_mk_array = (n, v) => new Array(Number(n)).fill(v);
// Array.toList -> List (tag 0 = nil, tag 1 = cons{head, tail}).
const lean_array_to_list = (a) =>
  a.reduceRight((tl, h) => ({ tag: 1, fields: [h, tl] }), 0);

// ---- Nat extras (bigint) ----
const lean_nat_log2 = (a) => { let n = a, r = 0n; while (n > 1n) { n >>= 1n; r += 1n; } return r; };
const lean_nat_shift_left = (a, b) => a << b;
const lean_nat_shift_right = (a, b) => a >> b;
const lean_nat_land = (a, b) => a & b;
const lean_nat_lor = (a, b) => a | b;
const lean_nat_xor = (a, b) => a ^ b;

// ---- Int / Nat conversions ----
const lean_int_of_nat = (n) => n;
const lean_int_to_nat = (i) => (i < 0n ? 0n : i);
const lean_nat_abs = (i) => (i < 0n ? -i : i);
const lean_uint32_of_nat2 = (n) => Number(BigInt.asUintN(32, n));
const lean_uint64_to_float = (a) => Number(a);
const lean_uint32_to_float = (a) => Number(a);

// ---- misc externs reached by toString / repr / platform ----
// Array.mk : List a -> Array a (the IR ctor for the Array's backing buffer).
const lean_array_mk = (lst) => {
  const out = [];
  let cur = lst;
  while (typeof cur !== 'number' && cur.tag === 1) { out.push(cur.fields[0]); cur = cur.fields[1]; }
  return out;
};
// USize.repr / Nat.repr style decimal rendering.
const lean_string_of_usize = (a) => a.toString();
// System.Platform.getNumBits : the platform word size. Derived from WORD_BITS so
// that flipping the single knob to 32 keeps getNumBits, USize.size, and the
// usize arithmetic wrap all consistent on a 32-bit profile.
const lean_system_platform_nbits = () => BigInt(WORD_BITS);

// ===================== IO runtime =====================
// Representation (verified against EmitC / lean.h):
//   - Every compiled IO/BaseIO action is a function `(...args) => io_result`.
//     The `World` token is an IR `void` param; the emitter drops void params,
//     so actions receive NO trailing world arg (closure `app` sites do pass an
//     erased `undefined`, which the prelude closures simply ignore).
//   - io_result mirrors `EST.Out` / `lean_io_result`: ok = ctor tag 0, error =
//     ctor tag 1, each with one field. So {tag:0,fields:[value]} / {tag:1,fields:[err]}.
const lean_io_result_mk_ok = (a) => ({ tag: 0, fields: [a] });
const lean_io_result_mk_error = (e) => ({ tag: 1, fields: [e] });
const lean_io_result_is_ok = (r) => lean_tag(r) === 0;
const lean_io_result_get_value = (r) => r.fields[0];
const lean_io_result_get_error = (r) => r.fields[0];

// IO.Error.userError msg. userError is the last ctor of the IO.Error inductive
// (cidx 18); render via its message field. Object form (multi-ctor inductive).
const IO_ERROR_USER = 18;
const lean_mk_io_user_error = (msg) => ({ tag: IO_ERROR_USER, fields: [msg] });
// Full IO.Error.toString matching `@[export lean_io_error_to_string]`
// (Init/System/IOError.lean): 19 constructors, cidx order
//   0 alreadyExists 1 otherError 2 resourceBusy 3 resourceVanished
//   4 unsupportedOperation 5 hardwareFault 6 unsatisfiedConstraints
//   7 illegalOperation 8 protocolError 9 timeExpired 10 interrupted
//   11 noFileOrDirectory 12 invalidArgument 13 permissionDenied
//   14 resourceExhausted 15 inappropriateType 16 noSuchThing
//   17 unexpectedEof (nullary) 18 userError.
// fopenErrorToString / otherErrorToString decapitalize the first char of the
// gist (and of `details` when present); osCode is a UInt32 (so -2 -> 4294967294).
const _decap = (s) => (typeof s !== 'string' || s.length === 0 ? s : s[0].toLowerCase() + s.slice(1));
const _ef = (e, i) => (typeof e === 'object' && e !== null && Array.isArray(e.fields)) ? e.fields[i] : undefined;
// `Option String` field: none == 0 (number), some == {tag:1,fields:[s]}.
const _optFn = (o) => (typeof o === 'object' && o !== null && Array.isArray(o.fields)) ? o.fields[0] : null;
const _ioFopen = (gist, fn, code, details) =>
  _decap(gist) + ' (error code: ' + String((Number(code) >>> 0)) +
  (details != null ? ', ' + _decap(details) : '') + ')\n  file: ' + fn;
const _ioOther = (gist, code, details) =>
  _decap(gist) + ' (error code: ' + String((Number(code) >>> 0)) +
  (details != null ? ', ' + _decap(details) : '') + ')';
const lean_io_error_to_string = (e) => {
  const tag = lean_tag(e);
  switch (tag) {
    case 0:  { const fn = _optFn(_ef(e, 0)); return fn != null ? _ioFopen('already exists', fn, _ef(e, 1), _ef(e, 2)) : _ioOther('already exists', _ef(e, 1), _ef(e, 2)); }
    case 1:  return _ioOther(_ef(e, 1), _ef(e, 0), null);
    case 2:  return _ioOther('resource busy', _ef(e, 0), _ef(e, 1));
    case 3:  return _ioOther('resource vanished', _ef(e, 0), _ef(e, 1));
    case 4:  return _ioOther('unsupported operation', _ef(e, 0), _ef(e, 1));
    case 5:  return _ioOther('hardware fault', _ef(e, 0), null);
    case 6:  return _ioOther('directory not empty', _ef(e, 0), null);
    case 7:  return _ioOther('illegal operation', _ef(e, 0), _ef(e, 1));
    case 8:  return _ioOther('protocol error', _ef(e, 0), _ef(e, 1));
    case 9:  return _ioOther('time expired', _ef(e, 0), _ef(e, 1));
    case 10: return _ioFopen('interrupted system call', _ef(e, 0), _ef(e, 1), _ef(e, 2));
    case 11: return _ioFopen('no such file or directory', _ef(e, 0), _ef(e, 1), null);
    case 12: { const fn = _optFn(_ef(e, 0)); return fn != null ? _ioFopen('invalid argument', fn, _ef(e, 1), _ef(e, 2)) : _ioOther('invalid argument', _ef(e, 1), _ef(e, 2)); }
    case 13: { const fn = _optFn(_ef(e, 0)), d = _ef(e, 2); return fn != null ? _ioFopen(d, fn, _ef(e, 1), null) : _ioOther(d, _ef(e, 1), null); }
    case 14: { const fn = _optFn(_ef(e, 0)); return fn != null ? _ioFopen('resource exhausted', fn, _ef(e, 1), _ef(e, 2)) : _ioOther('resource exhausted', _ef(e, 1), _ef(e, 2)); }
    case 15: { const fn = _optFn(_ef(e, 0)); return fn != null ? _ioFopen('inappropriate type', fn, _ef(e, 1), _ef(e, 2)) : _ioOther('inappropriate type', _ef(e, 1), _ef(e, 2)); }
    case 16: { const fn = _optFn(_ef(e, 0)); return fn != null ? _ioFopen('no such thing', fn, _ef(e, 1), _ef(e, 2)) : _ioOther('no such thing', _ef(e, 1), _ef(e, 2)); }
    case 17: return 'end of file';
    case 18: return _ef(e, 0);
    default: return String(e);
  }
};

// FS.Stream ctor: field order from `structure FS.Stream`
//   flush(0) read(1) write(2) getLine(3) putStr(4) isTty(5).
// Each field is itself an IO action closure: it takes its value args then an
// erased world arg, and returns an io_result. lean_apply invokes them.
const _utf8encIO = new TextEncoder();
const _mkWriteStream = (write) => ({
  tag: 0,
  fields: [
    () => lean_io_result_mk_ok(0),
    (_n) => lean_io_result_mk_ok(new Uint8Array(0)),
    (buf) => { write(Buffer.from(buf)); return lean_io_result_mk_ok(0); },
    () => lean_io_result_mk_ok(''),
    (s) => { write(s); return lean_io_result_mk_ok(0); },
    () => lean_io_result_mk_ok(0),
  ],
});
let _stdoutStream = _mkWriteStream((x) => process.stdout.write(x));
let _stderrStream = _mkWriteStream((x) => process.stderr.write(x));
// Real fd-0 stdin stream. Field order matches FS.Stream:
//   flush(0) read(1) write(2) getLine(3) putStr(4) isTty(5).
// Lean getLine reads up to AND including the next '\n' ('' == EOF); read(n)
// reads up to n bytes (empty array == EOF, stream stays open). Node has no
// portable blocking line read, so we readSync(0,...) byte-by-byte; works for
// piped/redirected input and files. readSync returning 0 (or EOF/EAGAIN) is EOF.
const _utf8decIO = new TextDecoder('utf-8');
const _readByte0 = () => {
  const b = Buffer.alloc(1);
  try {
    const k = _nodeFs.readSync(0, b, 0, 1, null);
    return k === 0 ? -1 : b[0];
  } catch (e) {
    if (e && (e.code === 'EOF' || e.code === 'EAGAIN')) return -1;
    throw e;
  }
};
let _stdinStream = {
  tag: 0,
  fields: [
    () => lean_io_result_mk_ok(0),
    (n) => {
      const want = Number(n);
      const buf = Buffer.alloc(want);
      let got = 0;
      try { got = _nodeFs.readSync(0, buf, 0, want, null); }
      catch (e) { if (!(e && (e.code === 'EOF' || e.code === 'EAGAIN'))) throw e; }
      return lean_io_result_mk_ok(new Uint8Array(buf.subarray(0, got)));
    },
    (_b) => lean_io_result_mk_ok(0),
    () => {
      const bytes = [];
      for (;;) {
        const c = _readByte0();
        if (c < 0) break;          // EOF
        bytes.push(c);
        if (c === 0x0a) break;     // '\n' inclusive
      }
      return lean_io_result_mk_ok(_utf8decIO.decode(Uint8Array.from(bytes)));
    },
    (_s) => lean_io_result_mk_ok(0),
    () => lean_io_result_mk_ok(process.stdin.isTTY ? 1 : 0),
  ],
};
// getStdout/getStderr/getStdin are BaseIO actions: BaseIO cannot error, so its
// `EST.Out.ok` is erased and the extern returns the bare Stream (the consuming
// IR does `proj[4]` directly on the result). Likewise the set* variants return
// the previous stream directly.
const lean_get_stdout = () => _stdoutStream;
const lean_get_stderr = () => _stderrStream;
const lean_get_stdin = () => _stdinStream;
const lean_get_set_stdout = (s) => { const p = _stdoutStream; _stdoutStream = s; return p; };
const lean_get_set_stderr = (s) => { const p = _stderrStream; _stderrStream = s; return p; };
const lean_get_set_stdin = (s) => { const p = _stdinStream; _stdinStream = s; return p; };
// @[export] aliases some emitted code calls directly.
const lean_io_eprint = (s) => { process.stderr.write(s); return lean_io_result_mk_ok(0); };
const lean_io_eprintln = (s) => { process.stderr.write(s + '\n'); return lean_io_result_mk_ok(0); };

// IO.Ref / ST.Ref : a single mutable cell {value}. These are BaseIO actions
// (cannot error), so `EST.Out.ok` is erased and the externs return bare values
// (the consuming IR uses the result directly, never `case`-ing on a tag).
const lean_st_mk_ref = (a) => ({ value: a });
const lean_st_ref_get = (r) => r.value;
const lean_st_ref_set = (r, a) => { r.value = a; return 0; };
const lean_st_ref_swap = (r, a) => { const o = r.value; r.value = a; return o; };
const lean_st_ref_take = (r) => { const o = r.value; r.value = undefined; return o; };
const lean_st_ref_ptr_eq = (r1, r2) => (r1 === r2 ? 1 : 0);

// IO.getEnv : BaseIO (Option String). BaseIO -> bare Option (no io_result wrap).
// none = 0 (nullary), some = {tag:1,fields:[s]}.
const lean_io_getenv = (name) => {
  const v = process.env[name];
  return v === undefined ? 0 : { tag: 1, fields: [v] };
};

// IO.Process.exit / forceExit.
const lean_io_exit = (code) => { process.exit(Number(code) & 0xff); };
const lean_io_force_exit = (code) => { process.exit(Number(code) & 0xff); };

// FS.Handle primitives (node:fs sync). `node:fs` is loaded lazily so the
// function-export diff-test harness (which evaluates the prelude with no module
// loader) is unaffected unless a handle primitive is actually called. Loaded via
// `process.getBuiltinModule` (Node >= 20.16) so it works from BOTH a CommonJS
// `new Function(src)` eval (no ESM `import`) AND an `.mjs` ES module (no
// `require`); falls back to a bare `require` if getBuiltinModule is absent.
let _nodeFsCache = null;
const _loadNodeFs = () => {
  if (_nodeFsCache) return _nodeFsCache;
  if (typeof process !== 'undefined' && typeof process.getBuiltinModule === 'function') {
    _nodeFsCache = process.getBuiltinModule('node:fs');
  } else {
    _nodeFsCache = require('node:fs');
  }
  return _nodeFsCache;
};
const _nodeFs = new Proxy({}, { get: (_t, k) => _loadNodeFs()[k] });
const _MODE_FLAG = ['r', 'w', 'wx', 'r+', 'a']; // FS.Mode cidx -> open flag
const lean_io_prim_handle_mk = (path, mode) => {
  try { return lean_io_result_mk_ok({ fd: _nodeFs.openSync(path, _MODE_FLAG[mode]) }); }
  catch (e) { return lean_io_result_mk_error(lean_mk_io_user_error(String(e && e.message ? e.message : e))); }
};
const lean_io_prim_handle_put_str = (h, s) => {
  _nodeFs.writeSync(h.fd, Buffer.from(s, 'utf8')); return lean_io_result_mk_ok(0);
};
const lean_io_prim_handle_write = (h, buf) => {
  _nodeFs.writeSync(h.fd, Buffer.from(buf)); return lean_io_result_mk_ok(0);
};
const lean_io_prim_handle_read = (h, n) => {
  const b = Buffer.alloc(Number(n));
  const k = _nodeFs.readSync(h.fd, b, 0, Number(n), null);
  return lean_io_result_mk_ok(new Uint8Array(b.subarray(0, k)));
};
const lean_io_prim_handle_flush = () => lean_io_result_mk_ok(0);
const lean_io_prim_handle_is_tty = () => lean_io_result_mk_ok(0);
// Handle.getLine: read up to and including the next '\n' from the handle's fd
// ('' == EOF). Byte-loop then UTF-8 decode, matching Lean's line semantics.
const lean_io_prim_handle_get_line = (h) => {
  const bytes = [];
  const one = Buffer.alloc(1);
  for (;;) {
    let k = 0;
    try { k = _nodeFs.readSync(h.fd, one, 0, 1, null); }
    catch (e) { if (e && (e.code === 'EOF' || e.code === 'EAGAIN')) break; throw e; }
    if (k === 0) break;
    bytes.push(one[0]);
    if (one[0] === 0x0a) break;
  }
  return lean_io_result_mk_ok(new TextDecoder('utf-8').decode(Uint8Array.from(bytes)));
};

// lean_io_result_show_error analogue: matches the C runtime which prints, to
// stderr, "uncaught exception: " + IO.Error.toString(err) + "\n" then exits 1.
const lean_io_result_show_error = (res) => {
  process.stderr.write('uncaught exception: ' +
    lean_io_error_to_string(lean_io_result_get_error(res)) + '\n');
};

// ---- module-initialization chain (emitInitFn / emitDeclInit analogue) ----
// EmitC emits, per module, an init fn that (1) runs imported modules' inits in
// dependency order, then (2) runs each decl's init in reverse decl order:
// @[init]/builtin_initialize IO Unit actions and closed-term global
// initializers, short-circuiting on the first IOResult error. We mirror that
// with a thunk registry. Each registered thunk returns an io_result (ok = value
// already assigned to its global inside the thunk; error = mk_error). The
// _G_initialized guard makes it idempotent.
const _leanInitThunks = [];
let _leanInitialized = false;
const lean_register_init = (thunk) => { _leanInitThunks.push(thunk); };
const lean_run_init = () => {
  if (_leanInitialized) return lean_io_result_mk_ok(0);
  _leanInitialized = true;
  for (const t of _leanInitThunks) {
    const res = t();
    if (!lean_io_result_is_ok(res)) return res; // propagate; do not continue
  }
  return lean_io_result_mk_ok(0);
};

// Entry point: run a compiled `main`, decode the io_result like C `main`.
// `mainFn` already has its void world param dropped (the emitter omits it), so
// arity-1 IO actions are invoked with no args; arity-2 (`List String -> IO X`)
// receives the argv-derived List. `retIsU32` picks the exit-code expression.
// Module init runs first (mirrors emitMainFn): an init-time IOResult error
// flows through the SAME show-error + exit-1 path as a main-time error.
const lean_run_main = (mainFn, hasArgs, retIsU32) => {
  let res = lean_run_init();
  if (lean_io_result_is_ok(res)) {
    if (hasArgs) {
      const argv = process.argv.slice(2);
      const args = argv.reduceRight((tl, s) => ({ tag: 1, fields: [s, tl] }), 0);
      res = mainFn(args);
    } else {
      res = mainFn();
    }
  }
  if (lean_io_result_is_ok(res)) {
    const v = lean_io_result_get_value(res);
    process.exitCode = retIsU32 ? Number(v) & 0xff : 0;
  } else {
    lean_io_result_show_error(res);
    process.exitCode = 1;
  }
};

// ================ GENERATED PROGRAM ================

function LeanJs_DemoIO_main__closed_0() {
  const x_1 = "lean-js IO demo";
  return x_1;
}

function LeanJs_DemoIO_fib__tc(x_1) {
  while (true) {
    const x_2 = 0n;
    const x_3 = lean_nat_dec_eq(x_1, x_2);
    switch (x_3) {
      case 1: {
        return x_2;
      }
      case 0: {
        const x_4 = 1n;
        const x_5 = (x_1 > x_4 ? x_1 - x_4 : 0n);
        const x_6 = lean_nat_dec_eq(x_5, x_2);
        switch (x_6) {
          case 1: {
            return x_4;
          }
          case 0: {
            const x_7 = (x_5 > x_4 ? x_5 - x_4 : 0n);
            const x_8 = LeanJs_DemoIO_fib(x_7);
            const x_9 = (x_7 + x_4);
            const x_10 = LeanJs_DemoIO_fib(x_9);
            const x_11 = (x_8 + x_10);
            return x_11;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_DemoIO_fib(x_1) {
  return lean_trampoline(LeanJs_DemoIO_fib__tc(x_1));
}

function LeanJs_DemoIO_main__closed_2__tc() {
  while (true) {
    const x_1 = 10n;
    return { __tc: 1, f: LeanJs_DemoIO_fib__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_2() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_2__tc());
}

function LeanJs_DemoIO_main__closed_3__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_main__closed_2();
    return { __tc: 1, f: Nat_reprFast__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_3() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_3__tc());
}

function LeanJs_DemoIO_main__closed_1() {
  const x_1 = "fib 10 = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_4() {
  const x_1 = LeanJs_DemoIO_main__closed_3();
  const x_2 = LeanJs_DemoIO_main__closed_1();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_main__closed_6__tc() {
  while (true) {
    const x_1 = 5n;
    return { __tc: 1, f: Nat_reprFast__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_6() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_6__tc());
}

function LeanJs_DemoIO_main__closed_5() {
  const x_1 = "2 + 3 = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_7() {
  const x_1 = LeanJs_DemoIO_main__closed_6();
  const x_2 = LeanJs_DemoIO_main__closed_5();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_main__closed_9__tc() {
  while (true) {
    const x_1 = 1000000000000000000n;
    return { __tc: 1, f: Nat_reprFast__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_9() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_9__tc());
}

function LeanJs_DemoIO_main__closed_8() {
  const x_1 = "big1 = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_10() {
  const x_1 = LeanJs_DemoIO_main__closed_9();
  const x_2 = LeanJs_DemoIO_main__closed_8();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_main__closed_12__tc() {
  while (true) {
    const x_1 = 1152921504606846976n;
    return { __tc: 1, f: Nat_reprFast__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_12() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_12__tc());
}

function LeanJs_DemoIO_main__closed_11() {
  const x_1 = "big2 = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_13() {
  const x_1 = LeanJs_DemoIO_main__closed_12();
  const x_2 = LeanJs_DemoIO_main__closed_11();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_main__closed_15() {
  const x_1 = 123456789012345678901234567890n;
  return x_1;
}

function LeanJs_DemoIO_main__closed_16__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_main__closed_15();
    return { __tc: 1, f: Nat_reprFast__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_16() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_16__tc());
}

function LeanJs_DemoIO_main__closed_14() {
  const x_1 = "huge = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_17() {
  const x_1 = LeanJs_DemoIO_main__closed_16();
  const x_2 = LeanJs_DemoIO_main__closed_14();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

// extern ST_Prim_mkRef -> runtime prelude

// extern ST_Prim_Ref_take -> runtime prelude

// extern ST_Prim_Ref_set -> runtime prelude

// extern ST_Prim_Ref_get -> runtime prelude

function LeanJs_DemoIO_main__closed_18() {
  const x_1 = "ref = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_21() {
  const x_1 = "walk dog";
  return x_1;
}

function LeanJs_DemoIO_main__closed_19() {
  const x_1 = "buy milk";
  return x_1;
}

function LeanTodo_instInhabitedTodoList_default__closed_0__tc() {
  while (true) {
    const x_1 = 0n;
    const x_2 = 0;
    const x_3 = lean_ctor(0, 2, 0, 0, x_2, x_1);
    return x_3;
  }
}
function LeanTodo_instInhabitedTodoList_default__closed_0() {
  return lean_trampoline(LeanTodo_instInhabitedTodoList_default__closed_0__tc());
}

function LeanTodo_TodoList_empty__tc() {
  while (true) {
    return { __tc: 1, f: LeanTodo_instInhabitedTodoList_default__closed_0__tc, a: [] };
  }
}
function LeanTodo_TodoList_empty() {
  return lean_trampoline(LeanTodo_TodoList_empty__tc());
}

function LeanJs_DemoIO_main__closed_20__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_main__closed_19();
    const x_2 = LeanTodo_TodoList_empty();
    return { __tc: 1, f: LeanTodo_TodoList_add__tc, a: [x_2, x_1] };
  }
}
function LeanJs_DemoIO_main__closed_20() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_20__tc());
}

function LeanTodo_TodoList_add__tc(x_1, x_2) {
  while (true) {
    const x_3 = 1;
    switch (x_3) {
      case 0: {
        const x_4 = x_1.fields[0];
        const x_5 = x_1.fields[1];
        const x_6 = 0;
        const x_7 = lean_ctor(0, 2, 0, 1, x_5, x_2);
        lean_ctor_set_u8(x_7, 0, x_6);
        const x_8 = lean_ctor(1, 2, 0, 0, x_7, x_4);
        const x_9 = 1n;
        const x_10 = (x_5 + x_9);
        x_1.fields[1] = x_10;
        x_1.fields[0] = x_8;
        return x_1;
      }
      case 1: {
        const x_11 = x_1.fields[0];
        const x_12 = x_1.fields[1];
        const x_13 = 0;
        const x_14 = lean_ctor(0, 2, 0, 1, x_12, x_2);
        lean_ctor_set_u8(x_14, 0, x_13);
        const x_15 = lean_ctor(1, 2, 0, 0, x_14, x_11);
        const x_16 = 1n;
        const x_17 = (x_12 + x_16);
        const x_18 = lean_ctor(0, 2, 0, 0, x_15, x_17);
        return x_18;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanTodo_TodoList_add(x_1, x_2) {
  return lean_trampoline(LeanTodo_TodoList_add__tc(x_1, x_2));
}

function LeanJs_DemoIO_main__closed_22__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_main__closed_21();
    const x_2 = LeanJs_DemoIO_main__closed_20();
    return { __tc: 1, f: LeanTodo_TodoList_add__tc, a: [x_2, x_1] };
  }
}
function LeanJs_DemoIO_main__closed_22() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_22__tc());
}

function List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0__tc(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        return { __tc: 1, f: List_reverse__redArg__tc, a: [x_3] };
      }
      case 1: {
        const x_5 = x_2.fields[0];
        const x_6 = x_2.fields[1];
        const x_7 = null;
        const x_12 = x_5.fields[0];
        const x_13 = x_5.fields[1];
        const x_14 = lean_ctor_get_u8(x_5, 0);
        const x_15 = lean_nat_dec_eq(x_12, x_1);
        switch (x_15) {
          case 0: {
            const x_8 = x_5;
            const x_9 = lean_ctor(1, 2, 0, 0, x_8, x_3);
            const __t_1 = x_1;
            const __t_2 = x_6;
            const __t_3 = x_9;
            x_1 = __t_1;
            x_2 = __t_2;
            x_3 = __t_3;
            continue;
          }
          case 1: {
            const x_16 = 1;
            switch (x_16) {
              case 0: {
                const x_17 = x_5.fields[1];
                const x_18 = x_5.fields[0];
                switch (x_14) {
                  case 0: {
                    lean_ctor_set_u8(x_5, 0, x_15);
                    const x_8 = x_5;
                    const x_9 = lean_ctor(1, 2, 0, 0, x_8, x_3);
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  case 1: {
                    const x_19 = 0;
                    lean_ctor_set_u8(x_5, 0, x_19);
                    const x_8 = x_5;
                    const x_9 = lean_ctor(1, 2, 0, 0, x_8, x_3);
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  default: { throw new Error("no matching case"); }
                }
              }
              case 1: {
                switch (x_14) {
                  case 0: {
                    const x_20 = lean_ctor(0, 2, 0, 1, x_12, x_13);
                    lean_ctor_set_u8(x_20, 0, x_15);
                    const x_8 = x_20;
                    const x_9 = lean_ctor(1, 2, 0, 0, x_8, x_3);
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  case 1: {
                    const x_21 = 0;
                    const x_22 = lean_ctor(0, 2, 0, 1, x_12, x_13);
                    lean_ctor_set_u8(x_22, 0, x_21);
                    const x_8 = x_22;
                    const x_9 = lean_ctor(1, 2, 0, 0, x_8, x_3);
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  default: { throw new Error("no matching case"); }
                }
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_1, x_2, x_3) {
  return lean_trampoline(List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0__tc(x_1, x_2, x_3));
}

function LeanTodo_TodoList_toggle__tc(x_1, x_2) {
  while (true) {
    const x_3 = 1;
    switch (x_3) {
      case 0: {
        const x_4 = x_1.fields[0];
        const x_5 = 0;
        const x_6 = List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_2, x_4, x_5);
        x_1.fields[0] = x_6;
        return x_1;
      }
      case 1: {
        const x_7 = x_1.fields[0];
        const x_8 = x_1.fields[1];
        const x_9 = 0;
        const x_10 = List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_2, x_7, x_9);
        const x_11 = lean_ctor(0, 2, 0, 0, x_10, x_8);
        return x_11;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanTodo_TodoList_toggle(x_1, x_2) {
  return lean_trampoline(LeanTodo_TodoList_toggle__tc(x_1, x_2));
}

function LeanJs_DemoIO_main__closed_23__tc() {
  while (true) {
    const x_1 = 0n;
    const x_2 = LeanJs_DemoIO_main__closed_22();
    return { __tc: 1, f: LeanTodo_TodoList_toggle__tc, a: [x_2, x_1] };
  }
}
function LeanJs_DemoIO_main__closed_23() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_23__tc());
}

function LeanJs_DemoIO_showList__closed_0() {
  const x_1 = "[";
  return x_1;
}

function LeanJs_DemoIO_showList__closed_1() {
  const x_1 = ",";
  return x_1;
}

function LeanJs_DemoIO_showTodo__closed_0() {
  const x_1 = ":";
  return x_1;
}

function LeanJs_DemoIO_showTodo__closed_1() {
  const x_1 = " ";
  return x_1;
}

function LeanJs_DemoIO_showTodo__closed_2() {
  const x_1 = "x";
  return x_1;
}

function LeanJs_DemoIO_showTodo(x_1) {
  const x_2 = x_1.fields[0];
  const x_3 = x_1.fields[1];
  const x_4 = lean_ctor_get_u8(x_1, 0);
  const block_12 = (x_5) => {
    const x_6 = Nat_reprFast(x_2);
    const x_7 = LeanJs_DemoIO_showTodo__closed_0();
    const x_8 = lean_string_append(x_6, x_7);
    const x_9 = lean_string_append(x_8, x_3);
    const x_10 = lean_string_append(x_9, x_7);
    const x_11 = lean_string_append(x_10, x_5);
    return x_11;
  };
  switch (x_4) {
    case 0: {
      const x_13 = LeanJs_DemoIO_showTodo__closed_1();
      return block_12(x_13);
    }
    case 1: {
      const x_14 = LeanJs_DemoIO_showTodo__closed_2();
      return block_12(x_14);
    }
    default: { throw new Error("no matching case"); }
  }
}

function List_mapTR_loop__at__LeanJs_DemoIO_showList_spec_0__tc(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        return { __tc: 1, f: List_reverse__redArg__tc, a: [x_2] };
      }
      case 1: {
        const x_4 = 1;
        switch (x_4) {
          case 0: {
            const x_5 = x_1.fields[0];
            const x_6 = x_1.fields[1];
            const x_7 = LeanJs_DemoIO_showTodo(x_5);
            x_1.fields[1] = x_2;
            x_1.fields[0] = x_7;
            const __t_1 = x_6;
            const __t_2 = x_1;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          case 1: {
            const x_9 = x_1.fields[0];
            const x_10 = x_1.fields[1];
            const x_11 = LeanJs_DemoIO_showTodo(x_9);
            const x_12 = lean_ctor(1, 2, 0, 0, x_11, x_2);
            const __t_1 = x_10;
            const __t_2 = x_12;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function List_mapTR_loop__at__LeanJs_DemoIO_showList_spec_0(x_1, x_2) {
  return lean_trampoline(List_mapTR_loop__at__LeanJs_DemoIO_showList_spec_0__tc(x_1, x_2));
}

function String_join__closed_0__tc() {
  while (true) {
    const x_1 = "";
    return x_1;
  }
}
function String_join__closed_0() {
  return lean_trampoline(String_join__closed_0__tc());
}

function _private_Init_Data_String_Defs_0_String_intercalate_go__tc(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_3)) {
      case 0: {
        return x_1;
      }
      case 1: {
        const x_4 = x_3.fields[0];
        const x_5 = x_3.fields[1];
        const x_6 = lean_string_append(x_1, x_2);
        const x_7 = lean_string_append(x_6, x_4);
        const __t_1 = x_7;
        const __t_2 = x_2;
        const __t_3 = x_5;
        x_1 = __t_1;
        x_2 = __t_2;
        x_3 = __t_3;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function _private_Init_Data_String_Defs_0_String_intercalate_go(x_1, x_2, x_3) {
  return lean_trampoline(_private_Init_Data_String_Defs_0_String_intercalate_go__tc(x_1, x_2, x_3));
}

function String_intercalate__tc(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        return { __tc: 1, f: String_join__closed_0__tc, a: [] };
      }
      case 1: {
        const x_4 = x_2.fields[0];
        const x_5 = x_2.fields[1];
        return { __tc: 1, f: _private_Init_Data_String_Defs_0_String_intercalate_go__tc, a: [x_4, x_1, x_5] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function String_intercalate(x_1, x_2) {
  return lean_trampoline(String_intercalate__tc(x_1, x_2));
}

function LeanJs_DemoIO_showList__closed_2() {
  const x_1 = "]@";
  return x_1;
}

function LeanJs_DemoIO_showList__tc(x_1) {
  while (true) {
    const x_2 = x_1.fields[0];
    const x_3 = x_1.fields[1];
    const x_4 = LeanJs_DemoIO_showList__closed_0();
    const x_5 = LeanJs_DemoIO_showList__closed_1();
    const x_6 = 0;
    const x_7 = List_mapTR_loop__at__LeanJs_DemoIO_showList_spec_0(x_2, x_6);
    const x_8 = String_intercalate(x_5, x_7);
    const x_9 = lean_string_append(x_4, x_8);
    const x_10 = LeanJs_DemoIO_showList__closed_2();
    const x_11 = lean_string_append(x_9, x_10);
    const x_12 = Nat_reprFast(x_3);
    const x_13 = lean_string_append(x_11, x_12);
    return x_13;
  }
}
function LeanJs_DemoIO_showList(x_1) {
  return lean_trampoline(LeanJs_DemoIO_showList__tc(x_1));
}

function LeanJs_DemoIO_main__closed_25__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_main__closed_23();
    return { __tc: 1, f: LeanJs_DemoIO_showList__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_main__closed_25() {
  return lean_trampoline(LeanJs_DemoIO_main__closed_25__tc());
}

function LeanJs_DemoIO_main__closed_24() {
  const x_1 = "todo = ";
  return x_1;
}

function LeanJs_DemoIO_main__closed_26() {
  const x_1 = LeanJs_DemoIO_main__closed_25();
  const x_2 = LeanJs_DemoIO_main__closed_24();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_tryCatchIO__closed_0() {
  const x_1 = "boom";
  return x_1;
}

function LeanJs_DemoIO_tryCatchIO__closed_1() {
  const x_1 = LeanJs_DemoIO_tryCatchIO__closed_0();
  const x_2 = lean_ctor(18, 1, 0, 0, x_1);
  return x_2;
}

function IO_Error_toString__closed_0() {
  const x_1 = "already exists";
  return x_1;
}

function IO_Error_toString__closed_1() {
  const x_1 = "resource busy";
  return x_1;
}

function IO_Error_toString__closed_2() {
  const x_1 = "resource vanished";
  return x_1;
}

function IO_Error_toString__closed_3() {
  const x_1 = "unsupported operation";
  return x_1;
}

function IO_Error_toString__closed_4() {
  const x_1 = "hardware fault";
  return x_1;
}

function IO_Error_toString__closed_5() {
  const x_1 = "directory not empty";
  return x_1;
}

function IO_Error_toString__closed_6() {
  const x_1 = "illegal operation";
  return x_1;
}

function IO_Error_toString__closed_7() {
  const x_1 = "protocol error";
  return x_1;
}

function IO_Error_toString__closed_8() {
  const x_1 = "time expired";
  return x_1;
}

function IO_Error_toString__closed_9() {
  const x_1 = "interrupted system call";
  return x_1;
}

function IO_Error_toString__closed_10() {
  const x_1 = "no such file or directory";
  return x_1;
}

function IO_Error_toString__closed_11() {
  const x_1 = "invalid argument";
  return x_1;
}

function IO_Error_toString__closed_12() {
  const x_1 = "resource exhausted";
  return x_1;
}

function IO_Error_toString__closed_13() {
  const x_1 = "inappropriate type";
  return x_1;
}

function IO_Error_otherErrorToString__closed_0() {
  const x_1 = ")";
  return x_1;
}

function IO_Error_otherErrorToString__tc(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_3)) {
      case 0: {
        const x_4 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_1);
        const x_5 = IO_Error_fopenErrorToString__closed_0();
        const x_6 = lean_string_append(x_4, x_5);
        const x_7 = lean_uint32_to_nat(x_2);
        const x_8 = Nat_reprFast(x_7);
        const x_9 = lean_string_append(x_6, x_8);
        const x_10 = IO_Error_otherErrorToString__closed_0();
        const x_11 = lean_string_append(x_9, x_10);
        return x_11;
      }
      case 1: {
        const x_12 = x_3.fields[0];
        const x_13 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_1);
        const x_14 = IO_Error_fopenErrorToString__closed_0();
        const x_15 = lean_string_append(x_13, x_14);
        const x_16 = lean_uint32_to_nat(x_2);
        const x_17 = Nat_reprFast(x_16);
        const x_18 = lean_string_append(x_15, x_17);
        const x_19 = IO_Error_fopenErrorToString__closed_2();
        const x_20 = lean_string_append(x_18, x_19);
        const x_21 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_12);
        const x_22 = lean_string_append(x_20, x_21);
        const x_23 = IO_Error_otherErrorToString__closed_0();
        const x_24 = lean_string_append(x_22, x_23);
        return x_24;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function IO_Error_otherErrorToString(x_1, x_2, x_3) {
  return lean_trampoline(IO_Error_otherErrorToString__tc(x_1, x_2, x_3));
}

function IO_Error_toString__closed_14() {
  const x_1 = "no such thing";
  return x_1;
}

function IO_Error_fopenErrorToString__closed_0() {
  const x_1 = " (error code: ";
  return x_1;
}

// extern UInt32_toNat -> runtime prelude

function List_range_loop__tc(x_1, x_2) {
  while (true) {
    const x_3 = 0n;
    const x_4 = lean_nat_dec_eq(x_1, x_3);
    switch (x_4) {
      case 1: {
        return x_2;
      }
      case 0: {
        const x_5 = 1n;
        const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
        const x_7 = lean_ctor(1, 2, 0, 0, x_6, x_2);
        const __t_1 = x_6;
        const __t_2 = x_7;
        x_1 = __t_1;
        x_2 = __t_2;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function List_range_loop(x_1, x_2) {
  return lean_trampoline(List_range_loop__tc(x_1, x_2));
}

function List_range__tc(x_1) {
  while (true) {
    const x_2 = 0;
    return { __tc: 1, f: List_range_loop__tc, a: [x_1, x_2] };
  }
}
function List_range(x_1) {
  return lean_trampoline(List_range__tc(x_1));
}

function _private_Init_Data_Repr_0_Nat_reprArray__closed_0__tc() {
  while (true) {
    const x_1 = 128n;
    return { __tc: 1, f: List_range__tc, a: [x_1] };
  }
}
function _private_Init_Data_Repr_0_Nat_reprArray__closed_0() {
  return lean_trampoline(_private_Init_Data_Repr_0_Nat_reprArray__closed_0__tc());
}

function List_reverseAux__redArg__tc(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        return x_2;
      }
      case 1: {
        const x_3 = 1;
        switch (x_3) {
          case 0: {
            const x_4 = x_1.fields[1];
            x_1.fields[1] = x_2;
            const __t_1 = x_4;
            const __t_2 = x_1;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          case 1: {
            const x_6 = x_1.fields[0];
            const x_7 = x_1.fields[1];
            const x_8 = lean_ctor(1, 2, 0, 0, x_6, x_2);
            const __t_1 = x_7;
            const __t_2 = x_8;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function List_reverseAux__redArg(x_1, x_2) {
  return lean_trampoline(List_reverseAux__redArg__tc(x_1, x_2));
}

function List_reverse__redArg__tc(x_1) {
  while (true) {
    const x_2 = 0;
    return { __tc: 1, f: List_reverseAux__redArg__tc, a: [x_1, x_2] };
  }
}
function List_reverse__redArg(x_1) {
  return lean_trampoline(List_reverse__redArg__tc(x_1));
}

// extern USize_ofNat -> runtime prelude

function List_mapTR_loop__at___private_Init_Data_Repr_0_Nat_reprArray_spec_0__tc(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        return { __tc: 1, f: List_reverse__redArg__tc, a: [x_2] };
      }
      case 1: {
        const x_4 = 1;
        switch (x_4) {
          case 0: {
            const x_5 = x_1.fields[0];
            const x_6 = x_1.fields[1];
            const x_7 = lean_usize_of_nat(x_5);
            const x_8 = lean_string_of_usize(x_7);
            x_1.fields[1] = x_2;
            x_1.fields[0] = x_8;
            const __t_1 = x_6;
            const __t_2 = x_1;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          case 1: {
            const x_10 = x_1.fields[0];
            const x_11 = x_1.fields[1];
            const x_12 = lean_usize_of_nat(x_10);
            const x_13 = lean_string_of_usize(x_12);
            const x_14 = lean_ctor(1, 2, 0, 0, x_13, x_2);
            const __t_1 = x_11;
            const __t_2 = x_14;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function List_mapTR_loop__at___private_Init_Data_Repr_0_Nat_reprArray_spec_0(x_1, x_2) {
  return lean_trampoline(List_mapTR_loop__at___private_Init_Data_Repr_0_Nat_reprArray_spec_0__tc(x_1, x_2));
}

function _private_Init_Data_Repr_0_Nat_reprArray__closed_1__tc() {
  while (true) {
    const x_1 = 0;
    const x_2 = _private_Init_Data_Repr_0_Nat_reprArray__closed_0();
    return { __tc: 1, f: List_mapTR_loop__at___private_Init_Data_Repr_0_Nat_reprArray_spec_0__tc, a: [x_2, x_1] };
  }
}
function _private_Init_Data_Repr_0_Nat_reprArray__closed_1() {
  return lean_trampoline(_private_Init_Data_Repr_0_Nat_reprArray__closed_1__tc());
}

// extern Array_mk -> runtime prelude

function _private_Init_Data_Repr_0_Nat_reprArray__closed_2__tc() {
  while (true) {
    const x_1 = _private_Init_Data_Repr_0_Nat_reprArray__closed_1();
    const x_2 = lean_array_mk(x_1);
    return x_2;
  }
}
function _private_Init_Data_Repr_0_Nat_reprArray__closed_2() {
  return lean_trampoline(_private_Init_Data_Repr_0_Nat_reprArray__closed_2__tc());
}

function _private_Init_Data_Repr_0_Nat_reprArray__tc() {
  while (true) {
    return { __tc: 1, f: _private_Init_Data_Repr_0_Nat_reprArray__closed_2__tc, a: [] };
  }
}
function _private_Init_Data_Repr_0_Nat_reprArray() {
  return lean_trampoline(_private_Init_Data_Repr_0_Nat_reprArray__tc());
}

// extern Array_size -> runtime prelude

function Nat_reprFast__closed_0() {
  const x_1 = _private_Init_Data_Repr_0_Nat_reprArray();
  const x_2 = lean_array_get_size(x_1);
  return x_2;
}

// extern System_Platform_getNumBits -> runtime prelude

function System_Platform_numBits__closed_0__tc() {
  while (true) {
    const x_1 = 0;
    const x_2 = lean_system_platform_nbits(x_1);
    return x_2;
  }
}
function System_Platform_numBits__closed_0() {
  return lean_trampoline(System_Platform_numBits__closed_0__tc());
}

function System_Platform_numBits__tc() {
  while (true) {
    return { __tc: 1, f: System_Platform_numBits__closed_0__tc, a: [] };
  }
}
function System_Platform_numBits() {
  return lean_trampoline(System_Platform_numBits__tc());
}

// extern Nat_pow -> runtime prelude

function Nat_reprFast__closed_1() {
  const x_1 = System_Platform_numBits();
  const x_2 = 2n;
  const x_3 = lean_nat_pow(x_2, x_1);
  return x_3;
}

// extern Nat_decLt -> runtime prelude

// extern Nat_add -> runtime prelude

// extern Nat_mod -> runtime prelude

function Nat_digitChar(x_1) {
  const x_2 = 0n;
  const x_3 = lean_nat_dec_eq(x_1, x_2);
  switch (x_3) {
    case 0: {
      const x_4 = 1n;
      const x_5 = lean_nat_dec_eq(x_1, x_4);
      switch (x_5) {
        case 0: {
          const x_6 = 2n;
          const x_7 = lean_nat_dec_eq(x_1, x_6);
          switch (x_7) {
            case 0: {
              const x_8 = 3n;
              const x_9 = lean_nat_dec_eq(x_1, x_8);
              switch (x_9) {
                case 0: {
                  const x_10 = 4n;
                  const x_11 = lean_nat_dec_eq(x_1, x_10);
                  switch (x_11) {
                    case 0: {
                      const x_12 = 5n;
                      const x_13 = lean_nat_dec_eq(x_1, x_12);
                      switch (x_13) {
                        case 0: {
                          const x_14 = 6n;
                          const x_15 = lean_nat_dec_eq(x_1, x_14);
                          switch (x_15) {
                            case 0: {
                              const x_16 = 7n;
                              const x_17 = lean_nat_dec_eq(x_1, x_16);
                              switch (x_17) {
                                case 0: {
                                  const x_18 = 8n;
                                  const x_19 = lean_nat_dec_eq(x_1, x_18);
                                  switch (x_19) {
                                    case 0: {
                                      const x_20 = 9n;
                                      const x_21 = lean_nat_dec_eq(x_1, x_20);
                                      switch (x_21) {
                                        case 0: {
                                          const x_22 = 10n;
                                          const x_23 = lean_nat_dec_eq(x_1, x_22);
                                          switch (x_23) {
                                            case 0: {
                                              const x_24 = 11n;
                                              const x_25 = lean_nat_dec_eq(x_1, x_24);
                                              switch (x_25) {
                                                case 0: {
                                                  const x_26 = 12n;
                                                  const x_27 = lean_nat_dec_eq(x_1, x_26);
                                                  switch (x_27) {
                                                    case 0: {
                                                      const x_28 = 13n;
                                                      const x_29 = lean_nat_dec_eq(x_1, x_28);
                                                      switch (x_29) {
                                                        case 0: {
                                                          const x_30 = 14n;
                                                          const x_31 = lean_nat_dec_eq(x_1, x_30);
                                                          switch (x_31) {
                                                            case 0: {
                                                              const x_32 = 15n;
                                                              const x_33 = lean_nat_dec_eq(x_1, x_32);
                                                              switch (x_33) {
                                                                case 0: {
                                                                  const x_34 = 42;
                                                                  return x_34;
                                                                }
                                                                case 1: {
                                                                  const x_35 = 102;
                                                                  return x_35;
                                                                }
                                                                default: { throw new Error("no matching case"); }
                                                              }
                                                            }
                                                            case 1: {
                                                              const x_36 = 101;
                                                              return x_36;
                                                            }
                                                            default: { throw new Error("no matching case"); }
                                                          }
                                                        }
                                                        case 1: {
                                                          const x_37 = 100;
                                                          return x_37;
                                                        }
                                                        default: { throw new Error("no matching case"); }
                                                      }
                                                    }
                                                    case 1: {
                                                      const x_38 = 99;
                                                      return x_38;
                                                    }
                                                    default: { throw new Error("no matching case"); }
                                                  }
                                                }
                                                case 1: {
                                                  const x_39 = 98;
                                                  return x_39;
                                                }
                                                default: { throw new Error("no matching case"); }
                                              }
                                            }
                                            case 1: {
                                              const x_40 = 97;
                                              return x_40;
                                            }
                                            default: { throw new Error("no matching case"); }
                                          }
                                        }
                                        case 1: {
                                          const x_41 = 57;
                                          return x_41;
                                        }
                                        default: { throw new Error("no matching case"); }
                                      }
                                    }
                                    case 1: {
                                      const x_42 = 56;
                                      return x_42;
                                    }
                                    default: { throw new Error("no matching case"); }
                                  }
                                }
                                case 1: {
                                  const x_43 = 55;
                                  return x_43;
                                }
                                default: { throw new Error("no matching case"); }
                              }
                            }
                            case 1: {
                              const x_44 = 54;
                              return x_44;
                            }
                            default: { throw new Error("no matching case"); }
                          }
                        }
                        case 1: {
                          const x_45 = 53;
                          return x_45;
                        }
                        default: { throw new Error("no matching case"); }
                      }
                    }
                    case 1: {
                      const x_46 = 52;
                      return x_46;
                    }
                    default: { throw new Error("no matching case"); }
                  }
                }
                case 1: {
                  const x_47 = 51;
                  return x_47;
                }
                default: { throw new Error("no matching case"); }
              }
            }
            case 1: {
              const x_48 = 50;
              return x_48;
            }
            default: { throw new Error("no matching case"); }
          }
        }
        case 1: {
          const x_49 = 49;
          return x_49;
        }
        default: { throw new Error("no matching case"); }
      }
    }
    case 1: {
      const x_50 = 48;
      return x_50;
    }
    default: { throw new Error("no matching case"); }
  }
}

// extern Nat_div -> runtime prelude

// extern Nat_decEq -> runtime prelude

// extern Nat_sub -> runtime prelude

function Nat_toDigitsCore__tc(x_1, x_2, x_3, x_4) {
  while (true) {
    const x_5 = 0n;
    const x_6 = lean_nat_dec_eq(x_2, x_5);
    switch (x_6) {
      case 1: {
        return x_4;
      }
      case 0: {
        const x_7 = (x_1 === 0n ? x_3 : x_3 % x_1);
        const x_8 = Nat_digitChar(x_7);
        const x_9 = (x_1 === 0n ? 0n : x_3 / x_1);
        const x_10 = lean_nat_dec_eq(x_9, x_5);
        switch (x_10) {
          case 0: {
            const x_11 = 1n;
            const x_12 = (x_2 > x_11 ? x_2 - x_11 : 0n);
            const x_13 = x_8;
            const x_14 = lean_ctor(1, 2, 0, 0, x_13, x_4);
            const __t_1 = x_1;
            const __t_2 = x_12;
            const __t_3 = x_9;
            const __t_4 = x_14;
            x_1 = __t_1;
            x_2 = __t_2;
            x_3 = __t_3;
            x_4 = __t_4;
            continue;
          }
          case 1: {
            const x_16 = x_8;
            const x_17 = lean_ctor(1, 2, 0, 0, x_16, x_4);
            return x_17;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function Nat_toDigitsCore(x_1, x_2, x_3, x_4) {
  return lean_trampoline(Nat_toDigitsCore__tc(x_1, x_2, x_3, x_4));
}

function Nat_toDigits__tc(x_1, x_2) {
  while (true) {
    const x_3 = 1n;
    const x_4 = (x_2 + x_3);
    const x_5 = 0;
    return { __tc: 1, f: Nat_toDigitsCore__tc, a: [x_1, x_4, x_2, x_5] };
  }
}
function Nat_toDigits(x_1, x_2) {
  return lean_trampoline(Nat_toDigits__tc(x_1, x_2));
}

// extern String_ofList -> runtime prelude

// extern USize_ofNatLT -> runtime prelude

// extern USize_repr -> runtime prelude

// extern Array_getInternal -> runtime prelude

function Nat_reprFast__tc(x_1) {
  while (true) {
    const x_2 = _private_Init_Data_Repr_0_Nat_reprArray();
    const x_3 = Nat_reprFast__closed_0();
    const x_4 = lean_nat_dec_lt(x_1, x_3);
    switch (x_4) {
      case 0: {
        const x_5 = Nat_reprFast__closed_1();
        const x_6 = lean_nat_dec_lt(x_1, x_5);
        switch (x_6) {
          case 0: {
            const x_7 = 10n;
            const x_8 = Nat_toDigits(x_7, x_1);
            const x_9 = lean_string_mk(x_8);
            return x_9;
          }
          case 1: {
            const x_10 = lean_usize_of_nat(x_1);
            const x_11 = lean_string_of_usize(x_10);
            return x_11;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 1: {
        const x_12 = lean_array_uget(x_2, x_1);
        return x_12;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function Nat_reprFast(x_1) {
  return lean_trampoline(Nat_reprFast__tc(x_1));
}

function IO_Error_fopenErrorToString__closed_2() {
  const x_1 = ", ";
  return x_1;
}

// extern String_Pos_Raw_get -> runtime prelude

// extern UInt32_decLe -> runtime prelude

// extern UInt32_add -> runtime prelude

// extern String_Pos_Raw_set -> runtime prelude

function _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_1) {
  const x_2 = 0n;
  const x_3 = lean_string_utf8_get(x_1, x_2);
  const x_4 = 65;
  const x_5 = lean_uint32_dec_le(x_4, x_3);
  switch (x_5) {
    case 0: {
      const x_6 = lean_string_utf8_set(x_1, x_2, x_3);
      return x_6;
    }
    case 1: {
      const x_7 = 90;
      const x_8 = lean_uint32_dec_le(x_3, x_7);
      switch (x_8) {
        case 0: {
          const x_9 = lean_string_utf8_set(x_1, x_2, x_3);
          return x_9;
        }
        case 1: {
          const x_10 = 32;
          const x_11 = lean_uint32_add(x_3, x_10);
          const x_12 = lean_string_utf8_set(x_1, x_2, x_11);
          return x_12;
        }
        default: { throw new Error("no matching case"); }
      }
    }
    default: { throw new Error("no matching case"); }
  }
}

function IO_Error_fopenErrorToString__closed_1() {
  const x_1 = ")\n  file: ";
  return x_1;
}

function IO_Error_fopenErrorToString__tc(x_1, x_2, x_3, x_4) {
  while (true) {
    switch (lean_tag(x_4)) {
      case 0: {
        const x_5 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_1);
        const x_6 = IO_Error_fopenErrorToString__closed_0();
        const x_7 = lean_string_append(x_5, x_6);
        const x_8 = lean_uint32_to_nat(x_3);
        const x_9 = Nat_reprFast(x_8);
        const x_10 = lean_string_append(x_7, x_9);
        const x_11 = IO_Error_fopenErrorToString__closed_1();
        const x_12 = lean_string_append(x_10, x_11);
        const x_13 = lean_string_append(x_12, x_2);
        return x_13;
      }
      case 1: {
        const x_14 = x_4.fields[0];
        const x_15 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_1);
        const x_16 = IO_Error_fopenErrorToString__closed_0();
        const x_17 = lean_string_append(x_15, x_16);
        const x_18 = lean_uint32_to_nat(x_3);
        const x_19 = Nat_reprFast(x_18);
        const x_20 = lean_string_append(x_17, x_19);
        const x_21 = IO_Error_fopenErrorToString__closed_2();
        const x_22 = lean_string_append(x_20, x_21);
        const x_23 = _private_Init_System_IOError_0_IO_Error_downCaseFirst(x_14);
        const x_24 = lean_string_append(x_22, x_23);
        const x_25 = IO_Error_fopenErrorToString__closed_1();
        const x_26 = lean_string_append(x_24, x_25);
        const x_27 = lean_string_append(x_26, x_2);
        return x_27;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function IO_Error_fopenErrorToString(x_1, x_2, x_3, x_4) {
  return lean_trampoline(IO_Error_fopenErrorToString__tc(x_1, x_2, x_3, x_4));
}

function IO_Error_toString__closed_15__tc() {
  while (true) {
    const x_1 = "end of file";
    return x_1;
  }
}
function IO_Error_toString__closed_15() {
  return lean_trampoline(IO_Error_toString__closed_15__tc());
}

function IO_Error_toString__tc(x_1) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        const x_7 = x_1.fields[0];
        switch (lean_tag(x_7)) {
          case 0: {
            const x_8 = lean_ctor_get_u32(x_1, 0);
            const x_9 = x_1.fields[1];
            const x_10 = IO_Error_toString__closed_0();
            const x_11 = lean_ctor(1, 1, 0, 0, x_9);
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_10, x_8, x_11] };
          }
          case 1: {
            const x_13 = lean_ctor_get_u32(x_1, 0);
            const x_14 = x_1.fields[1];
            const x_15 = 1;
            switch (x_15) {
              case 0: {
                const x_16 = x_7.fields[0];
                const x_17 = IO_Error_toString__closed_0();
                x_7.fields[0] = x_14;
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_17, x_16, x_13, x_7] };
              }
              case 1: {
                const x_19 = x_7.fields[0];
                const x_20 = IO_Error_toString__closed_0();
                const x_21 = lean_ctor(1, 1, 0, 0, x_14);
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_20, x_19, x_13, x_21] };
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 1: {
        const x_23 = lean_ctor_get_u32(x_1, 0);
        const x_24 = x_1.fields[0];
        const x_2 = x_23;
        const x_3 = x_24;
        const x_4 = 0;
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_3, x_2, x_4] };
      }
      case 2: {
        const x_25 = lean_ctor_get_u32(x_1, 0);
        const x_26 = x_1.fields[0];
        const x_27 = IO_Error_toString__closed_1();
        const x_28 = lean_ctor(1, 1, 0, 0, x_26);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_27, x_25, x_28] };
      }
      case 3: {
        const x_30 = lean_ctor_get_u32(x_1, 0);
        const x_31 = x_1.fields[0];
        const x_32 = IO_Error_toString__closed_2();
        const x_33 = lean_ctor(1, 1, 0, 0, x_31);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_32, x_30, x_33] };
      }
      case 4: {
        const x_35 = lean_ctor_get_u32(x_1, 0);
        const x_36 = x_1.fields[0];
        const x_37 = IO_Error_toString__closed_3();
        const x_38 = lean_ctor(1, 1, 0, 0, x_36);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_37, x_35, x_38] };
      }
      case 5: {
        const x_40 = lean_ctor_get_u32(x_1, 0);
        const x_41 = IO_Error_toString__closed_4();
        const x_42 = 0;
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_41, x_40, x_42] };
      }
      case 6: {
        const x_44 = lean_ctor_get_u32(x_1, 0);
        const x_45 = IO_Error_toString__closed_5();
        const x_46 = 0;
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_45, x_44, x_46] };
      }
      case 7: {
        const x_48 = lean_ctor_get_u32(x_1, 0);
        const x_49 = x_1.fields[0];
        const x_50 = IO_Error_toString__closed_6();
        const x_51 = lean_ctor(1, 1, 0, 0, x_49);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_50, x_48, x_51] };
      }
      case 8: {
        const x_53 = lean_ctor_get_u32(x_1, 0);
        const x_54 = x_1.fields[0];
        const x_55 = IO_Error_toString__closed_7();
        const x_56 = lean_ctor(1, 1, 0, 0, x_54);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_55, x_53, x_56] };
      }
      case 9: {
        const x_58 = lean_ctor_get_u32(x_1, 0);
        const x_59 = x_1.fields[0];
        const x_60 = IO_Error_toString__closed_8();
        const x_61 = lean_ctor(1, 1, 0, 0, x_59);
        return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_60, x_58, x_61] };
      }
      case 10: {
        const x_63 = x_1.fields[0];
        const x_64 = lean_ctor_get_u32(x_1, 0);
        const x_65 = x_1.fields[1];
        const x_66 = IO_Error_toString__closed_9();
        const x_67 = lean_ctor(1, 1, 0, 0, x_65);
        return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_66, x_63, x_64, x_67] };
      }
      case 11: {
        const x_69 = x_1.fields[0];
        const x_70 = lean_ctor_get_u32(x_1, 0);
        const x_71 = IO_Error_toString__closed_10();
        const x_72 = 0;
        return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_71, x_69, x_70, x_72] };
      }
      case 12: {
        const x_74 = x_1.fields[0];
        switch (lean_tag(x_74)) {
          case 0: {
            const x_75 = lean_ctor_get_u32(x_1, 0);
            const x_76 = x_1.fields[1];
            const x_77 = IO_Error_toString__closed_11();
            const x_78 = lean_ctor(1, 1, 0, 0, x_76);
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_77, x_75, x_78] };
          }
          case 1: {
            const x_80 = lean_ctor_get_u32(x_1, 0);
            const x_81 = x_1.fields[1];
            const x_82 = 1;
            switch (x_82) {
              case 0: {
                const x_83 = x_74.fields[0];
                const x_84 = IO_Error_toString__closed_11();
                x_74.fields[0] = x_81;
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_84, x_83, x_80, x_74] };
              }
              case 1: {
                const x_86 = x_74.fields[0];
                const x_87 = IO_Error_toString__closed_11();
                const x_88 = lean_ctor(1, 1, 0, 0, x_81);
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_87, x_86, x_80, x_88] };
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 13: {
        const x_90 = x_1.fields[0];
        switch (lean_tag(x_90)) {
          case 0: {
            const x_91 = lean_ctor_get_u32(x_1, 0);
            const x_92 = x_1.fields[1];
            const x_2 = x_91;
            const x_3 = x_92;
            const x_4 = 0;
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_3, x_2, x_4] };
          }
          case 1: {
            const x_93 = lean_ctor_get_u32(x_1, 0);
            const x_94 = x_1.fields[1];
            const x_95 = x_90.fields[0];
            const x_96 = 0;
            return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_94, x_95, x_93, x_96] };
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 14: {
        const x_98 = x_1.fields[0];
        switch (lean_tag(x_98)) {
          case 0: {
            const x_99 = lean_ctor_get_u32(x_1, 0);
            const x_100 = x_1.fields[1];
            const x_101 = IO_Error_toString__closed_12();
            const x_102 = lean_ctor(1, 1, 0, 0, x_100);
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_101, x_99, x_102] };
          }
          case 1: {
            const x_104 = lean_ctor_get_u32(x_1, 0);
            const x_105 = x_1.fields[1];
            const x_106 = 1;
            switch (x_106) {
              case 0: {
                const x_107 = x_98.fields[0];
                const x_108 = IO_Error_toString__closed_12();
                x_98.fields[0] = x_105;
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_108, x_107, x_104, x_98] };
              }
              case 1: {
                const x_110 = x_98.fields[0];
                const x_111 = IO_Error_toString__closed_12();
                const x_112 = lean_ctor(1, 1, 0, 0, x_105);
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_111, x_110, x_104, x_112] };
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 15: {
        const x_114 = x_1.fields[0];
        switch (lean_tag(x_114)) {
          case 0: {
            const x_115 = lean_ctor_get_u32(x_1, 0);
            const x_116 = x_1.fields[1];
            const x_117 = IO_Error_toString__closed_13();
            const x_118 = lean_ctor(1, 1, 0, 0, x_116);
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_117, x_115, x_118] };
          }
          case 1: {
            const x_120 = lean_ctor_get_u32(x_1, 0);
            const x_121 = x_1.fields[1];
            const x_122 = 1;
            switch (x_122) {
              case 0: {
                const x_123 = x_114.fields[0];
                const x_124 = IO_Error_toString__closed_13();
                x_114.fields[0] = x_121;
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_124, x_123, x_120, x_114] };
              }
              case 1: {
                const x_126 = x_114.fields[0];
                const x_127 = IO_Error_toString__closed_13();
                const x_128 = lean_ctor(1, 1, 0, 0, x_121);
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_127, x_126, x_120, x_128] };
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 16: {
        const x_130 = x_1.fields[0];
        switch (lean_tag(x_130)) {
          case 0: {
            const x_131 = lean_ctor_get_u32(x_1, 0);
            const x_132 = x_1.fields[1];
            const x_133 = IO_Error_toString__closed_14();
            const x_134 = lean_ctor(1, 1, 0, 0, x_132);
            return { __tc: 1, f: IO_Error_otherErrorToString__tc, a: [x_133, x_131, x_134] };
          }
          case 1: {
            const x_136 = lean_ctor_get_u32(x_1, 0);
            const x_137 = x_1.fields[1];
            const x_138 = 1;
            switch (x_138) {
              case 0: {
                const x_139 = x_130.fields[0];
                const x_140 = IO_Error_toString__closed_14();
                x_130.fields[0] = x_137;
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_140, x_139, x_136, x_130] };
              }
              case 1: {
                const x_142 = x_130.fields[0];
                const x_143 = IO_Error_toString__closed_14();
                const x_144 = lean_ctor(1, 1, 0, 0, x_137);
                return { __tc: 1, f: IO_Error_fopenErrorToString__tc, a: [x_143, x_142, x_136, x_144] };
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 17: {
        return { __tc: 1, f: IO_Error_toString__closed_15__tc, a: [] };
      }
      case 18: {
        const x_147 = x_1.fields[0];
        return x_147;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function IO_Error_toString(x_1) {
  return lean_trampoline(IO_Error_toString__tc(x_1));
}

function LeanJs_DemoIO_tryCatchIO__closed_3__tc() {
  while (true) {
    const x_1 = LeanJs_DemoIO_tryCatchIO__closed_1();
    return { __tc: 1, f: IO_Error_toString__tc, a: [x_1] };
  }
}
function LeanJs_DemoIO_tryCatchIO__closed_3() {
  return lean_trampoline(LeanJs_DemoIO_tryCatchIO__closed_3__tc());
}

function LeanJs_DemoIO_tryCatchIO__closed_2() {
  const x_1 = "caught: ";
  return x_1;
}

function LeanJs_DemoIO_tryCatchIO__closed_4() {
  const x_1 = LeanJs_DemoIO_tryCatchIO__closed_3();
  const x_2 = LeanJs_DemoIO_tryCatchIO__closed_2();
  const x_3 = lean_string_append(x_2, x_1);
  return x_3;
}

function LeanJs_DemoIO_tryCatchIO() {
  const x_2 = LeanJs_DemoIO_tryCatchIO__closed_4();
  const x_3 = lean_ctor(0, 1, 0, 0, x_2);
  return x_3;
}

function LeanJs_DemoIO_main__closed_27() {
  const x_1 = "trycatch = ";
  return x_1;
}

// extern String_append -> runtime prelude

// extern IO_getStdout -> runtime prelude

function IO_print__at__IO_println__at__LeanJs_DemoIO_main_spec_0_spec_0__tc(x_1) {
  while (true) {
    const x_3 = lean_get_stdout();
    const x_4 = x_3.fields[4];
    return { __tc: 2, clo: x_4, a: [x_1, undefined] };
  }
}
function IO_print__at__IO_println__at__LeanJs_DemoIO_main_spec_0_spec_0(x_1) {
  return lean_trampoline(IO_print__at__IO_println__at__LeanJs_DemoIO_main_spec_0_spec_0__tc(x_1));
}

function IO_println__at__LeanJs_DemoIO_main_spec_0__tc(x_1) {
  while (true) {
    const x_3 = 10;
    const x_4 = lean_string_push(x_1, x_3);
    return { __tc: 1, f: IO_print__at__IO_println__at__LeanJs_DemoIO_main_spec_0_spec_0__tc, a: [x_4, undefined] };
  }
}
function IO_println__at__LeanJs_DemoIO_main_spec_0(x_1) {
  return lean_trampoline(IO_println__at__LeanJs_DemoIO_main_spec_0__tc(x_1));
}

function LeanJs_DemoIO_main__closed_28() {
  const x_1 = "diagnostic to stderr";
  return x_1;
}

// extern String_push -> runtime prelude

// extern IO_getStderr -> runtime prelude

function IO_eprint__at___private_Init_System_IO_0_IO_eprintAux_spec_0__tc(x_1) {
  while (true) {
    const x_3 = lean_get_stderr();
    const x_4 = x_3.fields[4];
    return { __tc: 2, clo: x_4, a: [x_1, undefined] };
  }
}
function IO_eprint__at___private_Init_System_IO_0_IO_eprintAux_spec_0(x_1) {
  return lean_trampoline(IO_eprint__at___private_Init_System_IO_0_IO_eprintAux_spec_0__tc(x_1));
}

function IO_eprintln__at___private_Init_System_IO_0_IO_eprintlnAux_spec_0__tc(x_1) {
  while (true) {
    const x_3 = 10;
    const x_4 = lean_string_push(x_1, x_3);
    return { __tc: 1, f: IO_eprint__at___private_Init_System_IO_0_IO_eprintAux_spec_0__tc, a: [x_4, undefined] };
  }
}
function IO_eprintln__at___private_Init_System_IO_0_IO_eprintlnAux_spec_0(x_1) {
  return lean_trampoline(IO_eprintln__at___private_Init_System_IO_0_IO_eprintlnAux_spec_0__tc(x_1));
}

function LeanJs_DemoIO_main__tc() {
  while (true) {
    const x_2 = LeanJs_DemoIO_main__closed_0();
    const x_3 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_2, undefined);
    switch (lean_tag(x_3)) {
      case 0: {
        const x_4 = LeanJs_DemoIO_main__closed_4();
        const x_5 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_4, undefined);
        switch (lean_tag(x_5)) {
          case 0: {
            const x_6 = LeanJs_DemoIO_main__closed_7();
            const x_7 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_6, undefined);
            switch (lean_tag(x_7)) {
              case 0: {
                const x_8 = LeanJs_DemoIO_main__closed_10();
                const x_9 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_8, undefined);
                switch (lean_tag(x_9)) {
                  case 0: {
                    const x_10 = LeanJs_DemoIO_main__closed_13();
                    const x_11 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_10, undefined);
                    switch (lean_tag(x_11)) {
                      case 0: {
                        const x_12 = LeanJs_DemoIO_main__closed_17();
                        const x_13 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_12, undefined);
                        switch (lean_tag(x_13)) {
                          case 0: {
                            const x_14 = 0n;
                            const x_15 = lean_st_mk_ref(x_14);
                            const x_16 = 41n;
                            const x_17 = lean_st_ref_set(x_15, x_16);
                            const x_18 = lean_st_ref_take(x_15);
                            const x_19 = 1n;
                            const x_20 = (x_18 + x_19);
                            const x_21 = lean_st_ref_set(x_15, x_20);
                            const x_22 = lean_st_ref_get(x_15);
                            const x_23 = LeanJs_DemoIO_main__closed_18();
                            const x_24 = Nat_reprFast(x_22);
                            const x_25 = lean_string_append(x_23, x_24);
                            const x_26 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_25, undefined);
                            switch (lean_tag(x_26)) {
                              case 0: {
                                const x_27 = LeanJs_DemoIO_main__closed_26();
                                const x_28 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_27, undefined);
                                switch (lean_tag(x_28)) {
                                  case 0: {
                                    const x_29 = LeanJs_DemoIO_tryCatchIO(undefined);
                                    const x_30 = x_29.fields[0];
                                    const x_31 = LeanJs_DemoIO_main__closed_27();
                                    const x_32 = lean_string_append(x_31, x_30);
                                    const x_33 = IO_println__at__LeanJs_DemoIO_main_spec_0(x_32, undefined);
                                    switch (lean_tag(x_33)) {
                                      case 0: {
                                        const x_34 = LeanJs_DemoIO_main__closed_28();
                                        return { __tc: 1, f: IO_eprintln__at___private_Init_System_IO_0_IO_eprintlnAux_spec_0__tc, a: [x_34, undefined] };
                                      }
                                      case 1: {
                                        return x_33;
                                      }
                                      default: { throw new Error("no matching case"); }
                                    }
                                  }
                                  case 1: {
                                    return x_28;
                                  }
                                  default: { throw new Error("no matching case"); }
                                }
                              }
                              case 1: {
                                return x_26;
                              }
                              default: { throw new Error("no matching case"); }
                            }
                          }
                          case 1: {
                            return x_13;
                          }
                          default: { throw new Error("no matching case"); }
                        }
                      }
                      case 1: {
                        return x_11;
                      }
                      default: { throw new Error("no matching case"); }
                    }
                  }
                  case 1: {
                    return x_9;
                  }
                  default: { throw new Error("no matching case"); }
                }
              }
              case 1: {
                return x_7;
              }
              default: { throw new Error("no matching case"); }
            }
          }
          case 1: {
            return x_5;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      case 1: {
        return x_3;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_DemoIO_main() {
  return lean_trampoline(LeanJs_DemoIO_main__tc());
}


lean_run_main(LeanJs_DemoIO_main, false, false);
