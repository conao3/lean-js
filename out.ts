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

// ---- trampoline driver for mutual / cross-function tail calls ----
// A trampolined core returns a thunk { __tc:1, f, a:[args] } at an SCC-internal
// tail edge instead of recursing; the driver unrolls thunks so no JS stack
// frame is consumed per tail step. Ordinary return values (ctors, bigints,
// numbers, strings, arrays, closures) never carry `__tc`, so they pass through.
function lean_trampoline(t) {
  while (t && typeof t === 'object' && t.__tc === 1) { t = t.f(...t.a); }
  return t;
}

// ---- closure application (pap/ap model) ----
function lean_apply(clo, more) {
  if (typeof clo === 'function') return clo(...more);
  const all = clo.args.concat(more);
  return clo.fn(...all);
}

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
const _u8 = _mkUIntNum(8), _u16 = _mkUIntNum(16), _u32 = _mkUIntNum(32);
const _u64 = _mkUIntBig(64), _usz = _mkUIntBig(64);

const lean_uint8_of_nat = _u8.ofNat, lean_uint8_add = _u8.add, lean_uint8_sub = _u8.sub, lean_uint8_mul = _u8.mul, lean_uint8_div = _u8.div, lean_uint8_mod = _u8.mod, lean_uint8_land = _u8.land, lean_uint8_lor = _u8.lor, lean_uint8_xor = _u8.xor, lean_uint8_complement = _u8.complement, lean_uint8_neg = _u8.neg, lean_uint8_shift_left = _u8.shiftLeft, lean_uint8_shift_right = _u8.shiftRight, lean_uint8_dec_eq = _u8.decEq, lean_uint8_dec_lt = _u8.decLt, lean_uint8_dec_le = _u8.decLe, lean_uint8_to_nat = _u8.toNat;
const lean_uint16_of_nat = _u16.ofNat, lean_uint16_add = _u16.add, lean_uint16_sub = _u16.sub, lean_uint16_mul = _u16.mul, lean_uint16_div = _u16.div, lean_uint16_mod = _u16.mod, lean_uint16_land = _u16.land, lean_uint16_lor = _u16.lor, lean_uint16_xor = _u16.xor, lean_uint16_complement = _u16.complement, lean_uint16_neg = _u16.neg, lean_uint16_shift_left = _u16.shiftLeft, lean_uint16_shift_right = _u16.shiftRight, lean_uint16_dec_eq = _u16.decEq, lean_uint16_dec_lt = _u16.decLt, lean_uint16_dec_le = _u16.decLe, lean_uint16_to_nat = _u16.toNat;
const lean_uint32_add = _u32.add, lean_uint32_sub = _u32.sub, lean_uint32_mul = _u32.mul, lean_uint32_div = _u32.div, lean_uint32_mod = _u32.mod, lean_uint32_land = _u32.land, lean_uint32_lor = _u32.lor, lean_uint32_xor = _u32.xor, lean_uint32_complement = _u32.complement, lean_uint32_neg = _u32.neg, lean_uint32_shift_left = _u32.shiftLeft, lean_uint32_shift_right = _u32.shiftRight, lean_uint32_dec_eq = _u32.decEq, lean_uint32_dec_lt = _u32.decLt, lean_uint32_dec_le = _u32.decLe, lean_uint32_to_nat = _u32.toNat;
const lean_uint64_of_nat = _u64.ofNat, lean_uint64_add = _u64.add, lean_uint64_sub = _u64.sub, lean_uint64_mul = _u64.mul, lean_uint64_div = _u64.div, lean_uint64_mod = _u64.mod, lean_uint64_land = _u64.land, lean_uint64_lor = _u64.lor, lean_uint64_xor = _u64.xor, lean_uint64_complement = _u64.complement, lean_uint64_neg = _u64.neg, lean_uint64_shift_left = _u64.shiftLeft, lean_uint64_shift_right = _u64.shiftRight, lean_uint64_dec_eq = _u64.decEq, lean_uint64_dec_lt = _u64.decLt, lean_uint64_dec_le = _u64.decLe, lean_uint64_to_nat = _u64.toNat;
const lean_usize_of_nat = _usz.ofNat, lean_usize_add = _usz.add, lean_usize_sub = _usz.sub, lean_usize_mul = _usz.mul, lean_usize_div = _usz.div, lean_usize_mod = _usz.mod, lean_usize_land = _usz.land, lean_usize_lor = _usz.lor, lean_usize_xor = _usz.xor, lean_usize_complement = _usz.complement, lean_usize_neg = _usz.neg, lean_usize_shift_left = _usz.shiftLeft, lean_usize_shift_right = _usz.shiftRight, lean_usize_dec_eq = _usz.decEq, lean_usize_dec_lt = _usz.decLt, lean_usize_dec_le = _usz.decLe, lean_usize_to_nat = _usz.toNat;

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
    ofInt: w, ofNat: w, toInt: (x) => x,
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

// ---- Char ----
const lean_uint32_of_nat = (n) => Number(n & 0xffffffffn);
const lean_char_to_nat = (c) => BigInt(c);

// ---- String: UTF-8 / code-point semantics ----
const lean_string_length = (s) => BigInt([...s].length);
const lean_string_append = (a, b) => a + b;
const lean_string_push = (s, c) => s + String.fromCodePoint(c);
const lean_string_dec_eq = (a, b) => L_bool(a === b);
const lean_string_isempty = (s) => L_bool(s.length === 0);
const lean_string_hash = (s) => { let h = 0n; for (const c of s) { h = (h * 31n + BigInt(c.codePointAt(0))) & 0xffffffffffffffffn; } return h; };
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

// ---- Array: JS array. get is bounds-checked w/ default; push mutates. ----
const lean_array_get_size = (a) => BigInt(a.length);
const lean_array_fget = (a, i) => a[Number(i)];
const lean_array_get = (a, i, dflt) => {
  const idx = Number(i); return idx >= 0 && idx < a.length ? a[idx] : dflt;
};
const lean_array_uget = (a, i) => a[Number(i)];
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
// System.Platform.getNumBits : the host word size; the value model treats
// USize as 64-bit (see prelude header), so report 64.
const lean_system_platform_nbits = () => 64n;

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
const lean_io_error_to_string = (e) =>
  (typeof e === 'object' && e !== null && Array.isArray(e.fields) && typeof e.fields[0] === 'string')
    ? e.fields[0]
    : String(e);

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
let _stdinStream = {
  tag: 0,
  fields: [
    () => lean_io_result_mk_ok(0),
    (_n) => lean_io_result_mk_ok(new Uint8Array(0)),
    (_b) => lean_io_result_mk_ok(0),
    () => lean_io_result_mk_ok(''),
    (_s) => lean_io_result_mk_ok(0),
    () => lean_io_result_mk_ok(0),
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
// loader) is unaffected unless a handle primitive is actually called.
let _nodeFsCache = null;
const _nodeFs = new Proxy({}, { get: (_t, k) => {
  if (!_nodeFsCache) _nodeFsCache = require('node:fs');
  return _nodeFsCache[k];
} });
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

// Entry point: run a compiled `main`, decode the io_result like C `main`.
// `mainFn` already has its void world param dropped (the emitter omits it), so
// arity-1 IO actions are invoked with no args; arity-2 (`List String -> IO X`)
// receives the argv-derived List. `retIsU32` picks the exit-code expression.
const lean_run_main = (mainFn, hasArgs, retIsU32) => {
  let res;
  if (hasArgs) {
    const argv = process.argv.slice(2);
    const args = argv.reduceRight((tl, s) => ({ tag: 1, fields: [s, tl] }), 0);
    res = mainFn(args);
  } else {
    res = mainFn();
  }
  if (lean_io_result_is_ok(res)) {
    const v = lean_io_result_get_value(res);
    process.exitCode = retIsU32 ? Number(v) & 0xff : 0;
  } else {
    process.stderr.write('uncaught exception: ' +
      lean_io_error_to_string(lean_io_result_get_error(res)) + '\n');
    process.exitCode = 1;
  }
};

// ================ GENERATED ================

function LeanJs_Demo_double(x_1) {
  const x_2 = (x_1 + x_1);
  return x_2;
}

function LeanJs_Demo_mkShifted(x_1) {
  const x_2 = 1;
  switch (x_2) {
    case 0: {
      const x_3 = x_1.fields[0];
      const x_4 = x_1.fields[1];
      const x_5 = 1n;
      const x_6 = (x_3 + x_5);
      const x_7 = (x_4 + x_3);
      x_1.fields[1] = x_7;
      x_1.fields[0] = x_6;
      return x_1;
    }
    case 1: {
      const x_8 = x_1.fields[0];
      const x_9 = x_1.fields[1];
      const x_10 = 1n;
      const x_11 = (x_8 + x_10);
      const x_12 = (x_9 + x_8);
      const x_13 = lean_ctor(0, 2, 0, 0, x_11, x_12);
      return x_13;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanJs_Demo_sumTo_go(x_1, x_2) {
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
        const x_7 = (x_6 + x_5);
        const x_8 = (x_2 + x_7);
        const __t_1 = x_6;
        const __t_2 = x_8;
        x_1 = __t_1;
        x_2 = __t_2;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanJs_Demo_sumTo(x_1) {
  const x_2 = 0n;
  const x_3 = LeanJs_Demo_sumTo_go(x_1, x_2);
  return x_3;
}

function LeanJs_Demo_fact(x_1) {
  const x_2 = 0n;
  const x_3 = lean_nat_dec_eq(x_1, x_2);
  switch (x_3) {
    case 1: {
      const x_4 = 1n;
      return x_4;
    }
    case 0: {
      const x_5 = 1n;
      const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
      const x_7 = (x_6 + x_5);
      const x_8 = LeanJs_Demo_fact(x_6);
      const x_9 = (x_7 * x_8);
      return x_9;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanJs_Demo_mkMixed(x_1, x_2, x_3, x_4) {
  const x_5 = lean_ctor(0, 1, 0, 4, x_1);
  lean_ctor_set_u8(x_5, 2, x_2);
  lean_ctor_set_u8(x_5, 3, x_3);
  lean_ctor_set_u16(x_5, 0, x_4);
  return x_5;
}

// extern UInt8_toNat -> runtime prelude

// extern UInt16_toNat -> runtime prelude

function LeanJs_Demo_mixedSum(x_1) {
  const x_2 = x_1.fields[0];
  const x_3 = lean_ctor_get_u8(x_1, 2);
  const x_4 = lean_ctor_get_u8(x_1, 3);
  const x_5 = lean_ctor_get_u16(x_1, 0);
  const x_6 = lean_uint8_to_nat(x_3);
  const x_7 = (x_2 + x_6);
  const x_8 = lean_uint8_to_nat(x_4);
  const x_9 = (x_7 + x_8);
  const x_10 = lean_uint16_to_nat(x_5);
  const x_11 = (x_9 + x_10);
  return x_11;
}

// extern UInt32_add -> runtime prelude

function LeanJs_Demo_u32wrap(x_1, x_2) {
  const x_3 = lean_uint32_add(x_1, x_2);
  return x_3;
}

// extern UInt8_sub -> runtime prelude

function LeanJs_Demo_u8wrap(x_1, x_2) {
  const x_3 = lean_uint8_sub(x_1, x_2);
  return x_3;
}

// extern Int_ediv -> runtime prelude

function LeanJs_Demo_intEdiv(x_1, x_2) {
  const x_3 = lean_int_ediv(x_1, x_2);
  return x_3;
}

// extern Int_emod -> runtime prelude

function LeanJs_Demo_intEmod(x_1, x_2) {
  const x_3 = lean_int_emod(x_1, x_2);
  return x_3;
}

function LeanJs_Demo_intNeg(x_1) {
  const x_2 = lean_int_neg(x_1);
  return x_2;
}

// extern Float_add -> runtime prelude

// extern Nat_shiftLeft -> runtime prelude

// extern Nat_pow -> runtime prelude

// extern Nat_div -> runtime prelude

function Float_ofScientific__closed_0() {
  const x_1 = 4n;
  const x_2 = lean_int_of_nat(x_1);
  return x_2;
}

// extern Int_neg -> runtime prelude

function Float_ofScientific__closed_1() {
  const x_1 = Float_ofScientific__closed_0();
  const x_2 = lean_int_neg(x_1);
  return x_2;
}

// extern Int_mul -> runtime prelude

// extern Int_sub -> runtime prelude

// extern Nat_log2 -> runtime prelude

// extern Nat_shiftRight -> runtime prelude

// extern UInt64_ofNat -> runtime prelude

// extern Int_ofNat -> runtime prelude

// extern Int_add -> runtime prelude

// extern UInt64_toFloat -> runtime prelude

// extern Float_scaleB -> runtime prelude

function Float_ofBinaryScientific(x_1, x_2) {
  const x_3 = lean_nat_log2(x_1);
  const x_4 = 63n;
  const x_5 = (x_3 > x_4 ? x_3 - x_4 : 0n);
  const x_6 = lean_nat_shift_right(x_1, x_5);
  const x_7 = lean_uint64_of_nat(x_6);
  const x_8 = lean_int_of_nat(x_5);
  const x_9 = (x_2 + x_8);
  const x_10 = lean_uint64_to_float(x_7);
  const x_11 = Float_scaleB(x_10, x_9);
  return x_11;
}

function Float_ofScientific(x_1, x_2, x_3) {
  switch (x_2) {
    case 0: {
      const x_4 = 5n;
      const x_5 = lean_nat_pow(x_4, x_3);
      const x_6 = (x_1 * x_5);
      const x_7 = lean_int_of_nat(x_3);
      const x_8 = Float_ofBinaryScientific(x_6, x_7);
      return x_8;
    }
    case 1: {
      const x_9 = 64n;
      const x_10 = lean_nat_log2(x_1);
      const x_11 = (x_9 > x_10 ? x_9 - x_10 : 0n);
      const x_12 = 3n;
      const x_13 = (x_12 * x_3);
      const x_14 = (x_13 + x_11);
      const x_15 = lean_nat_shift_left(x_1, x_14);
      const x_16 = 5n;
      const x_17 = lean_nat_pow(x_16, x_3);
      const x_18 = (x_17 === 0n ? 0n : x_15 / x_17);
      const x_19 = Float_ofScientific__closed_1();
      const x_20 = lean_int_of_nat(x_3);
      const x_21 = (x_19 * x_20);
      const x_22 = lean_int_of_nat(x_11);
      const x_23 = (x_21 - x_22);
      const x_24 = Float_ofBinaryScientific(x_18, x_23);
      return x_24;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanJs_Demo_floatCalc__closed_0() {
  const x_1 = 1n;
  const x_2 = 1;
  const x_3 = 20n;
  const x_4 = lean_float_of_scientific(x_3, x_2, x_1);
  return x_4;
}

// extern Float_mul -> runtime prelude

// extern Float_div -> runtime prelude

function LeanJs_Demo_floatCalc(x_1, x_2) {
  const x_3 = lean_float_add(x_1, x_2);
  const x_4 = LeanJs_Demo_floatCalc__closed_0();
  const x_5 = lean_float_mul(x_3, x_4);
  const x_6 = lean_float_div(x_5, x_2);
  return x_6;
}

// extern String_length -> runtime prelude

function LeanJs_Demo_strLen(x_1) {
  const x_2 = lean_string_length(x_1);
  return x_2;
}

// extern String_utf8ByteSize -> runtime prelude

function LeanJs_Demo_strBytes(x_1) {
  const x_2 = lean_string_utf8_byte_size(x_1);
  return x_2;
}

function LeanJs_Demo_strGet0(x_1) {
  const x_2 = 0n;
  const x_3 = lean_string_utf8_get(x_1, x_2);
  return x_3;
}

// extern String_Pos_Raw_next -> runtime prelude

// extern String_Pos_Raw_get -> runtime prelude

function LeanJs_Demo_strGet1(x_1) {
  const x_2 = 0n;
  const x_3 = lean_string_utf8_next(x_1, x_2);
  const x_4 = lean_string_utf8_get(x_1, x_3);
  return x_4;
}

// extern String_Pos_Raw_extract -> runtime prelude

function LeanJs_Demo_strExtract(x_1, x_2, x_3) {
  const x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
  return x_4;
}

function LeanJs_Demo_arrSum(x_1) {
  const x_2 = 0n;
  const x_3 = lean_array_get_size(x_1);
  const x_4 = lean_nat_dec_lt(x_2, x_3);
  switch (x_4) {
    case 0: {
      return x_2;
    }
    case 1: {
      const x_5 = lean_nat_dec_le(x_3, x_3);
      switch (x_5) {
        case 0: {
          switch (x_4) {
            case 0: {
              return x_2;
            }
            case 1: {
              const x_6 = 0n;
              const x_7 = lean_usize_of_nat(x_3);
              const x_8 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__LeanJs_Demo_arrSum_spec_0(x_1, x_6, x_7, x_2);
              return x_8;
            }
            default: { throw new Error("no matching case"); }
          }
        }
        case 1: {
          const x_9 = 0n;
          const x_10 = lean_usize_of_nat(x_3);
          const x_11 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__LeanJs_Demo_arrSum_spec_0(x_1, x_9, x_10, x_2);
          return x_11;
        }
        default: { throw new Error("no matching case"); }
      }
    }
    default: { throw new Error("no matching case"); }
  }
}

// extern Array_usize -> runtime prelude

// extern USize_decLt -> runtime prelude

// extern Array_uget -> runtime prelude

// extern Nat_mul -> runtime prelude

// extern Array_uset -> runtime prelude

function _private_Init_Data_Array_Basic_0_Array_mapMUnsafe_map__at__LeanJs_Demo_arrMapSum_spec_0(x_1, x_2, x_3) {
  while (true) {
    const x_4 = lean_usize_dec_lt(x_2, x_1);
    switch (x_4) {
      case 0: {
        return x_3;
      }
      case 1: {
        const x_5 = lean_array_uget(x_3, x_2);
        const x_6 = 0n;
        const x_7 = lean_array_uset(x_3, x_2, x_6);
        const x_8 = 2n;
        const x_9 = (x_5 * x_8);
        const x_10 = 1n;
        const x_11 = lean_usize_add(x_2, x_10);
        const x_12 = lean_array_uset(x_7, x_2, x_9);
        const __t_1 = x_1;
        const __t_2 = x_11;
        const __t_3 = x_12;
        x_1 = __t_1;
        x_2 = __t_2;
        x_3 = __t_3;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__LeanJs_Demo_arrSum_spec_0(x_1, x_2, x_3, x_4) {
  while (true) {
    const x_5 = lean_usize_dec_eq(x_2, x_3);
    switch (x_5) {
      case 0: {
        const x_6 = lean_array_uget(x_1, x_2);
        const x_7 = (x_4 + x_6);
        const x_8 = 1n;
        const x_9 = lean_usize_add(x_2, x_8);
        const __t_1 = x_1;
        const __t_2 = x_9;
        const __t_3 = x_3;
        const __t_4 = x_7;
        x_1 = __t_1;
        x_2 = __t_2;
        x_3 = __t_3;
        x_4 = __t_4;
        continue;
      }
      case 1: {
        return x_4;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanJs_Demo_arrMapSum(x_1) {
  const x_2 = 0n;
  const x_3 = lean_array_usize(x_1);
  const x_4 = 0n;
  const x_5 = _private_Init_Data_Array_Basic_0_Array_mapMUnsafe_map__at__LeanJs_Demo_arrMapSum_spec_0(x_3, x_4, x_1);
  const x_6 = lean_array_get_size(x_5);
  const x_7 = lean_nat_dec_lt(x_2, x_6);
  switch (x_7) {
    case 0: {
      return x_2;
    }
    case 1: {
      const x_8 = lean_nat_dec_le(x_6, x_6);
      switch (x_8) {
        case 0: {
          switch (x_7) {
            case 0: {
              return x_2;
            }
            case 1: {
              const x_9 = lean_usize_of_nat(x_6);
              const x_10 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__LeanJs_Demo_arrSum_spec_0(x_5, x_4, x_9, x_2);
              return x_10;
            }
            default: { throw new Error("no matching case"); }
          }
        }
        case 1: {
          const x_11 = lean_usize_of_nat(x_6);
          const x_12 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__LeanJs_Demo_arrSum_spec_0(x_5, x_4, x_11, x_2);
          return x_12;
        }
        default: { throw new Error("no matching case"); }
      }
    }
    default: { throw new Error("no matching case"); }
  }
}

function Array_range__lam_0(x_1) {
  return x_1;
}

function Array_range__lam_0__boxed(x_1) {
  const x_2 = Array_range__lam_0(x_1);
  return x_2;
}

function Array_range__closed_0() {
  const x_1 = { fn: Array_range__lam_0__boxed, args: [] };
  return x_1;
}

// extern Array_emptyWithCapacity -> runtime prelude

function _private_Init_Data_Array_Basic_0_Array_ofFn_go__redArg(x_1, x_2, x_3, x_4) {
  while (true) {
    const x_5 = 0n;
    const x_6 = lean_nat_dec_eq(x_4, x_5);
    switch (x_6) {
      case 1: {
        return x_3;
      }
      case 0: {
        const x_7 = 1n;
        const x_8 = (x_4 > x_7 ? x_4 - x_7 : 0n);
        const x_9 = (x_1 > x_8 ? x_1 - x_8 : 0n);
        const x_10 = (x_9 > x_7 ? x_9 - x_7 : 0n);
        const x_11 = lean_apply(x_2, [x_10]);
        const x_12 = lean_array_push(x_3, x_11);
        const __t_1 = x_1;
        const __t_2 = x_2;
        const __t_3 = x_12;
        const __t_4 = x_8;
        x_1 = __t_1;
        x_2 = __t_2;
        x_3 = __t_3;
        x_4 = __t_4;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function Array_ofFn__redArg(x_1, x_2) {
  const x_3 = [];
  const x_4 = _private_Init_Data_Array_Basic_0_Array_ofFn_go__redArg(x_1, x_2, x_3, x_1);
  return x_4;
}

function Array_range(x_1) {
  const x_2 = Array_range__closed_0();
  const x_3 = Array_ofFn__redArg(x_1, x_2);
  return x_3;
}

function LeanJs_Demo_arrRange(x_1) {
  const x_2 = Array_range(x_1);
  return x_2;
}

// extern Array_getInternalBorrowed -> runtime prelude

function LeanJs_Demo_arrGetD(x_1, x_2) {
  const x_3 = lean_array_get_size(x_1);
  const x_4 = lean_nat_dec_lt(x_2, x_3);
  switch (x_4) {
    case 0: {
      const x_5 = 0n;
      return x_5;
    }
    case 1: {
      const x_6 = lean_array_uget(x_1, x_2);
      return x_6;
    }
    default: { throw new Error("no matching case"); }
  }
}

// extern Array_size -> runtime prelude

// extern Nat_decLt -> runtime prelude

// extern Nat_decLe -> runtime prelude

// extern USize_ofNat -> runtime prelude

// extern USize_decEq -> runtime prelude

// extern Array_ugetBorrowed -> runtime prelude

// extern Array_push -> runtime prelude

// extern USize_add -> runtime prelude

function _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__Array_append_spec_0__redArg(x_1, x_2, x_3, x_4) {
  while (true) {
    const x_5 = lean_usize_dec_eq(x_2, x_3);
    switch (x_5) {
      case 0: {
        const x_6 = lean_array_uget(x_1, x_2);
        const x_7 = lean_array_push(x_4, x_6);
        const x_8 = 1n;
        const x_9 = lean_usize_add(x_2, x_8);
        const __t_1 = x_1;
        const __t_2 = x_9;
        const __t_3 = x_3;
        const __t_4 = x_7;
        x_1 = __t_1;
        x_2 = __t_2;
        x_3 = __t_3;
        x_4 = __t_4;
        continue;
      }
      case 1: {
        return x_4;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function Array_append__redArg(x_1, x_2) {
  const x_3 = 0n;
  const x_4 = lean_array_get_size(x_2);
  const x_5 = lean_nat_dec_lt(x_3, x_4);
  switch (x_5) {
    case 0: {
      return x_1;
    }
    case 1: {
      const x_6 = lean_nat_dec_le(x_4, x_4);
      switch (x_6) {
        case 0: {
          switch (x_5) {
            case 0: {
              return x_1;
            }
            case 1: {
              const x_7 = 0n;
              const x_8 = lean_usize_of_nat(x_4);
              const x_9 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__Array_append_spec_0__redArg(x_2, x_7, x_8, x_1);
              return x_9;
            }
            default: { throw new Error("no matching case"); }
          }
        }
        case 1: {
          const x_10 = 0n;
          const x_11 = lean_usize_of_nat(x_4);
          const x_12 = _private_Init_Data_Array_Basic_0_Array_foldlMUnsafe_fold__at__Array_append_spec_0__redArg(x_2, x_10, x_11, x_1);
          return x_12;
        }
        default: { throw new Error("no matching case"); }
      }
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanJs_Demo_arrAppend(x_1, x_2) {
  const x_3 = Array_append__redArg(x_1, x_2);
  return x_3;
}

function LeanJs_Demo_listSum(x_1) {
  const x_2 = 0n;
  const x_3 = List_foldl__at__LeanJs_Demo_listSum_spec_0(x_2, x_1);
  return x_3;
}

function List_lengthTRAux__redArg(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        return x_2;
      }
      case 1: {
        const x_3 = x_1.fields[1];
        const x_4 = 1n;
        const x_5 = (x_2 + x_4);
        const __t_1 = x_3;
        const __t_2 = x_5;
        x_1 = __t_1;
        x_2 = __t_2;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function List_lengthTR__redArg(x_1) {
  const x_2 = 0n;
  const x_3 = List_lengthTRAux__redArg(x_1, x_2);
  return x_3;
}

function LeanJs_Demo_listLen(x_1) {
  const x_2 = List_lengthTR__redArg(x_1);
  return x_2;
}

function LeanJs_Demo_listRev(x_1) {
  const x_2 = List_reverse__redArg(x_1);
  return x_2;
}

function List_mapTR_loop__at__LeanJs_Demo_listMapSum_spec_0(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        const x_3 = List_reverse__redArg(x_2);
        return x_3;
      }
      case 1: {
        const x_4 = 1;
        switch (x_4) {
          case 0: {
            const x_5 = x_1.fields[0];
            const x_6 = x_1.fields[1];
            const x_7 = 1n;
            const x_8 = (x_5 + x_7);
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
            const x_12 = 1n;
            const x_13 = (x_10 + x_12);
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

function List_foldl__at__LeanJs_Demo_listSum_spec_0(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        return x_1;
      }
      case 1: {
        const x_3 = x_2.fields[0];
        const x_4 = x_2.fields[1];
        const x_5 = (x_1 + x_3);
        const __t_1 = x_5;
        const __t_2 = x_4;
        x_1 = __t_1;
        x_2 = __t_2;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanJs_Demo_listMapSum(x_1) {
  const x_2 = 0n;
  const x_3 = 0;
  const x_4 = List_mapTR_loop__at__LeanJs_Demo_listMapSum_spec_0(x_1, x_3);
  const x_5 = List_foldl__at__LeanJs_Demo_listSum_spec_0(x_2, x_4);
  return x_5;
}

function LeanJs_Demo_parityEven(x_1) {
  const x_2 = LeanJs_Demo_isEvenM(x_1);
  return x_2;
}

function LeanJs_Demo_isEvenM__tc(x_1) {
  while (true) {
    const x_2 = 0n;
    const x_3 = lean_nat_dec_eq(x_1, x_2);
    switch (x_3) {
      case 1: {
        return x_3;
      }
      case 0: {
        const x_4 = 1n;
        const x_5 = (x_1 > x_4 ? x_1 - x_4 : 0n);
        return { __tc: 1, f: LeanJs_Demo_isOddM__tc, a: [x_5] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_Demo_isEvenM(x_1) {
  return lean_trampoline(LeanJs_Demo_isEvenM__tc(x_1));
}

function LeanJs_Demo_isOddM__tc(x_1) {
  while (true) {
    const x_2 = 0n;
    const x_3 = lean_nat_dec_eq(x_1, x_2);
    switch (x_3) {
      case 1: {
        const x_4 = 0;
        return x_4;
      }
      case 0: {
        const x_5 = 1n;
        const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
        return { __tc: 1, f: LeanJs_Demo_isEvenM__tc, a: [x_6] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_Demo_isOddM(x_1) {
  return lean_trampoline(LeanJs_Demo_isOddM__tc(x_1));
}

function LeanJs_Demo_parityOdd(x_1) {
  const x_2 = LeanJs_Demo_isOddM(x_1);
  return x_2;
}

// extern Nat_sub -> runtime prelude

function LeanJs_Demo_m3c__tc(x_1) {
  while (true) {
    const x_2 = 0n;
    const x_3 = lean_nat_dec_eq(x_1, x_2);
    switch (x_3) {
      case 1: {
        const x_4 = 2n;
        return x_4;
      }
      case 0: {
        const x_5 = 1n;
        const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
        return { __tc: 1, f: LeanJs_Demo_m3a__tc, a: [x_6] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_Demo_m3c(x_1) {
  return lean_trampoline(LeanJs_Demo_m3c__tc(x_1));
}

function LeanJs_Demo_m3b__tc(x_1) {
  while (true) {
    const x_2 = 0n;
    const x_3 = lean_nat_dec_eq(x_1, x_2);
    switch (x_3) {
      case 1: {
        const x_4 = 1n;
        return x_4;
      }
      case 0: {
        const x_5 = 1n;
        const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
        return { __tc: 1, f: LeanJs_Demo_m3c__tc, a: [x_6] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_Demo_m3b(x_1) {
  return lean_trampoline(LeanJs_Demo_m3b__tc(x_1));
}

function LeanJs_Demo_m3a__tc(x_1) {
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
        return { __tc: 1, f: LeanJs_Demo_m3b__tc, a: [x_5] };
      }
      default: { throw new Error("no matching case"); }
    }
  }
}
function LeanJs_Demo_m3a(x_1) {
  return lean_trampoline(LeanJs_Demo_m3a__tc(x_1));
}

function LeanJs_Demo_cycle3(x_1) {
  const x_2 = LeanJs_Demo_m3a(x_1);
  return x_2;
}

// extern Int8_add -> runtime prelude

function LeanJs_Demo_i8wrap(x_1, x_2) {
  const x_3 = lean_int8_add(x_1, x_2);
  return x_3;
}

// extern Int8_neg -> runtime prelude

function LeanJs_Demo_i8neg(x_1) {
  const x_2 = lean_int8_neg(x_1);
  return x_2;
}

// extern Int8_div -> runtime prelude

function LeanJs_Demo_i8div(x_1, x_2) {
  const x_3 = lean_int8_div(x_1, x_2);
  return x_3;
}

// extern Int8_mod -> runtime prelude

function LeanJs_Demo_i8mod(x_1, x_2) {
  const x_3 = lean_int8_mod(x_1, x_2);
  return x_3;
}

// extern Int8_shiftRight -> runtime prelude

function LeanJs_Demo_i8shr(x_1, x_2) {
  const x_3 = lean_int8_shift_right(x_1, x_2);
  return x_3;
}

// extern Int16_mul -> runtime prelude

function LeanJs_Demo_i16wrap(x_1, x_2) {
  const x_3 = lean_int16_mul(x_1, x_2);
  return x_3;
}

// extern Int32_add -> runtime prelude

function LeanJs_Demo_i32wrap(x_1, x_2) {
  const x_3 = lean_int32_add(x_1, x_2);
  return x_3;
}

// extern Int64_mul -> runtime prelude

function LeanJs_Demo_i64mul(x_1, x_2) {
  const x_3 = lean_int64_mul(x_1, x_2);
  return x_3;
}

// extern Int8_toInt -> runtime prelude

function LeanJs_Demo_i8toInt(x_1) {
  const x_2 = lean_int8_to_int(x_1);
  return x_2;
}

// extern Int32_toInt -> runtime prelude

function LeanJs_Demo_i32toInt(x_1) {
  const x_2 = lean_int32_to_int(x_1);
  return x_2;
}

// extern Float_toString -> runtime prelude

function LeanJs_Demo_floatStr(x_1) {
  const x_2 = lean_float_to_string(x_1);
  return x_2;
}

// extern Float32_toString -> runtime prelude

function LeanJs_Demo_float32Str(x_1) {
  const x_2 = lean_float32_to_string(x_1);
  return x_2;
}

// extern Nat_add -> runtime prelude

function LeanTodo_TodoList_add(x_1, x_2) {
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

function List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        const x_4 = List_reverse__redArg(x_3);
        return x_4;
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

function LeanTodo_TodoList_toggle(x_1, x_2) {
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

function List_reverseAux__redArg(x_1, x_2) {
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

function List_reverse__redArg(x_1) {
  const x_2 = 0;
  const x_3 = List_reverseAux__redArg(x_1, x_2);
  return x_3;
}

// extern Nat_decEq -> runtime prelude

function List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        const x_4 = List_reverse__redArg(x_3);
        return x_4;
      }
      case 1: {
        const x_5 = 1;
        switch (x_5) {
          case 0: {
            const x_6 = x_2.fields[0];
            const x_7 = x_2.fields[1];
            const x_8 = x_6.fields[0];
            const x_9 = lean_nat_dec_eq(x_8, x_1);
            switch (x_9) {
              case 0: {
                x_2.fields[1] = x_3;
                const __t_1 = x_1;
                const __t_2 = x_7;
                const __t_3 = x_2;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              case 1: {
                const __t_1 = x_1;
                const __t_2 = x_7;
                const __t_3 = x_3;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              default: { throw new Error("no matching case"); }
            }
          }
          case 1: {
            const x_12 = x_2.fields[0];
            const x_13 = x_2.fields[1];
            const x_14 = x_12.fields[0];
            const x_15 = lean_nat_dec_eq(x_14, x_1);
            switch (x_15) {
              case 0: {
                const x_16 = lean_ctor(1, 2, 0, 0, x_12, x_3);
                const __t_1 = x_1;
                const __t_2 = x_13;
                const __t_3 = x_16;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              case 1: {
                const __t_1 = x_1;
                const __t_2 = x_13;
                const __t_3 = x_3;
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
}

function LeanTodo_TodoList_remove(x_1, x_2) {
  const x_3 = 1;
  switch (x_3) {
    case 0: {
      const x_4 = x_1.fields[0];
      const x_5 = 0;
      const x_6 = List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_2, x_4, x_5);
      x_1.fields[0] = x_6;
      return x_1;
    }
    case 1: {
      const x_7 = x_1.fields[0];
      const x_8 = x_1.fields[1];
      const x_9 = 0;
      const x_10 = List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_2, x_7, x_9);
      const x_11 = lean_ctor(0, 2, 0, 0, x_10, x_8);
      return x_11;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanTodo_TodoList_step(x_1, x_2) {
  switch (lean_tag(x_2)) {
    case 0: {
      const x_3 = x_2.fields[0];
      const x_4 = LeanTodo_TodoList_add(x_1, x_3);
      return x_4;
    }
    case 1: {
      const x_5 = x_2.fields[0];
      const x_6 = LeanTodo_TodoList_toggle(x_1, x_5);
      return x_6;
    }
    case 2: {
      const x_7 = x_2.fields[0];
      const x_8 = LeanTodo_TodoList_remove(x_1, x_7);
      return x_8;
    }
    default: { throw new Error("no matching case"); }
  }
}

