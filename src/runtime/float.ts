import type { Ctor, Obj } from "./object.ts"
import { asNat, lean_bool, lean_ctor } from "./object.ts"

// ---- Float (IEEE 754 binary64 == JS number). IEEE div-by-zero (Inf/NaN). ----
export function lean_float_add(a: number, b: number): number {
  return a + b
}

export function lean_float_sub(a: number, b: number): number {
  return a - b
}

export function lean_float_mul(a: number, b: number): number {
  return a * b
}

export function lean_float_div(a: number, b: number): number {
  return a / b
}

export function lean_float_negate(a: number): number {
  return -a
}

export function lean_float_beq(a: number, b: number): number {
  return lean_bool(a === b)
}

export function lean_float_decLt(a: number, b: number): number {
  return lean_bool(a < b)
}

export function lean_float_decLe(a: number, b: number): number {
  return lean_bool(a <= b)
}

export function lean_float_isnan(a: number): number {
  return lean_bool(Number.isNaN(a))
}

export function lean_float_isfinite(a: number): number {
  return lean_bool(Number.isFinite(a))
}

export function lean_float_isinf(a: number): number {
  return lean_bool(a === Infinity || a === -Infinity)
}

export function lean_float_sqrt(a: number): number {
  return Math.sqrt(a)
}

export function lean_float_sin(a: number): number {
  return Math.sin(a)
}

export function lean_float_cos(a: number): number {
  return Math.cos(a)
}

export function lean_float_exp(a: number): number {
  return Math.exp(a)
}

export function lean_float_log(a: number): number {
  return Math.log(a)
}

export function lean_float_pow(a: number, b: number): number {
  return Math.pow(a, b)
}

export function lean_float_floor(a: number): number {
  return Math.floor(a)
}

export function lean_float_ceil(a: number): number {
  return Math.ceil(a)
}

export function lean_float_abs(a: number): number {
  return Math.abs(a)
}

export function lean_float_round(a: number): number {
  return Math.sign(a) * Math.round(Math.abs(a))
}

export function lean_float_scaleb(x: number, i: Obj): number {
  return x * Math.pow(2, Number(asNat(i)))
}

// libm transcendentals. JS Math.* and C libm are each typically <=1 ULP but
// neither IEEE-754 nor ECMAScript mandates correctly-rounded results for these,
// so they are NOT guaranteed bit-exact vs the C backend; the diff-test compares
// through Float.toString (C `%f`, 6 fixed decimals), which absorbs the sub-ULP
// noise. sqrt/comparisons/+-*//div ARE IEEE-correctly-rounded and bit-exact.
export function lean_float_tan(a: number): number {
  return Math.tan(a)
}

export function lean_float_asin(a: number): number {
  return Math.asin(a)
}

export function lean_float_acos(a: number): number {
  return Math.acos(a)
}

export function lean_float_atan(a: number): number {
  return Math.atan(a)
}

export function lean_float_atan2(a: number, b: number): number {
  return Math.atan2(a, b)
}

export function lean_float_sinh(a: number): number {
  return Math.sinh(a)
}

export function lean_float_cosh(a: number): number {
  return Math.cosh(a)
}

export function lean_float_tanh(a: number): number {
  return Math.tanh(a)
}

export function lean_float_asinh(a: number): number {
  return Math.asinh(a)
}

export function lean_float_acosh(a: number): number {
  return Math.acosh(a)
}

export function lean_float_atanh(a: number): number {
  return Math.atanh(a)
}

export function lean_float_exp2(a: number): number {
  return Math.pow(2, a)
}

export function lean_float_log2(a: number): number {
  return Math.log2(a)
}

export function lean_float_log10(a: number): number {
  return Math.log10(a)
}

export function lean_float_cbrt(a: number): number {
  return Math.cbrt(a)
}

// frExp / ofBits / toBits are EXACT bit reinterpretations (DataView), matching
// the C externs lean_float_frexp / lean_float_of_bits / lean_float_to_bits.
const f64dv = new DataView(new ArrayBuffer(8))

export function lean_float_to_bits(x: number): bigint {
  f64dv.setFloat64(0, x)
  return f64dv.getBigUint64(0)
}

export function lean_float_of_bits(b: bigint): number {
  f64dv.setBigUint64(0, BigInt.asUintN(64, b))
  return f64dv.getFloat64(0)
}

function frexp(x: number): [number, bigint] {
  if (x === 0 || !Number.isFinite(x)) return [x, 0n]
  const b = lean_float_to_bits(x)
  const e = Number((b >> 52n) & 0x7ffn)
  if (e === 0) {
    const [m, e2] = frexp(x / Math.pow(2, -1074))
    return [m, e2 - 1074n]
  }
  return [lean_float_of_bits((b & ~(0x7ffn << 52n)) | (1022n << 52n)), BigInt(e - 1022)]
}

// Float.frExp x = (m, e) with x = m * 2^e and 0.5 <= |m| < 1 (C frexp). Returns
// the Lean pair ctor {tag:0, fields:[m, e]} (e is an Int = bigint).
export function lean_float_frexp(x: number): Ctor {
  const [m, e] = frexp(x)
  return lean_ctor(0, 2, 0, 0, m, e)
}

function floatToUint(a: number, bits: number): bigint {
  if (Number.isNaN(a) || a <= 0) return 0n
  const max = (1n << BigInt(bits)) - 1n
  const t = BigInt(Math.trunc(a))
  return t > max ? max : t
}

export function lean_float_to_uint8(a: number): number {
  return Number(floatToUint(a, 8))
}

export function lean_float_to_uint16(a: number): number {
  return Number(floatToUint(a, 16))
}

export function lean_float_to_uint32(a: number): number {
  return Number(floatToUint(a, 32))
}

export function lean_float_to_uint64(a: number): bigint {
  return floatToUint(a, 64)
}

export function lean_float_to_usize(a: number): bigint {
  return floatToUint(a, 64)
}

// Float.ofScientific m e exp = m * 10^(e ? -exp : exp); parse via JS number
// literal for a correctly-rounded binary64 result (matches the extern).
export function lean_float_of_scientific(m: Obj, e: number, exp: Obj): number {
  return Number(`${asNat(m)}e${e ? "-" : ""}${asNat(exp)}`)
}

// ---- Float32 (IEEE 754 binary32). Round every result via Math.fround. ----
const f = Math.fround

function f32(fn: (a: number) => number, a: number): number {
  return f(fn(f(a)))
}

export function lean_float32_add(a: number, b: number): number {
  return f(f(a) + f(b))
}

export function lean_float32_sub(a: number, b: number): number {
  return f(f(a) - f(b))
}

export function lean_float32_mul(a: number, b: number): number {
  return f(f(a) * f(b))
}

export function lean_float32_div(a: number, b: number): number {
  return f(f(a) / f(b))
}

export function lean_float32_negate(a: number): number {
  return f(-f(a))
}

export function lean_float32_neg(a: number): number {
  return f(-f(a))
}

export function lean_float32_beq(a: number, b: number): number {
  return lean_bool(f(a) === f(b))
}

export function lean_float32_decLt(a: number, b: number): number {
  return lean_bool(f(a) < f(b))
}

export function lean_float32_decLe(a: number, b: number): number {
  return lean_bool(f(a) <= f(b))
}

export function lean_float32_to_float(a: number): number {
  return f(a)
}

export function lean_float_to_float32(a: number): number {
  return f(a)
}

// ---- Float.toString / Float32.toString : C `%f` (6 fixed decimals) ----
// Matches Lean: NaN -> "NaN"; +/-inf -> "inf"/"-inf"; sign of -0.0 preserved;
// |x| >= 1e21 falls back to the exact integer digits (JS toFixed would give
// exponential there). Float32 first rounds to binary32, then prints like Float.
export function lean_float_to_string(x: number): string {
  if (Number.isNaN(x)) return "NaN"
  if (x === Infinity) return "inf"
  if (x === -Infinity) return "-inf"
  const neg = x < 0 || Object.is(x, -0)
  const a = Math.abs(x)
  const s = a < 1e21 ? a.toFixed(6) : BigInt(a).toString() + ".000000"
  return neg ? "-" + s : s
}

export function lean_float32_to_string(x: number): string {
  return lean_float_to_string(f(x))
}

export function lean_float32_sqrt(a: number): number {
  return f32(Math.sqrt, a)
}

export function lean_float32_abs(a: number): number {
  return f32(Math.abs, a)
}

export function lean_float32_floor(a: number): number {
  return f32(Math.floor, a)
}

export function lean_float32_ceil(a: number): number {
  return f32(Math.ceil, a)
}

export function lean_float32_round(a: number): number {
  return f(Math.sign(f(a)) * Math.round(Math.abs(f(a))))
}

export function lean_float32_isnan(a: number): number {
  return lean_bool(Number.isNaN(f(a)))
}

export function lean_float32_isfinite(a: number): number {
  return lean_bool(Number.isFinite(f(a)))
}

export function lean_float32_isinf(a: number): number {
  const v = f(a)
  return lean_bool(v === Infinity || v === -Infinity)
}

// Float32 libm transcendentals: Lean uses the single-precision libm symbols
// (sinf, ...); the closest JS path is fround(Math.fn(fround x)) (double then
// narrow), a DIFFERENT rounding path that can differ by >1 ULP at f32 precision,
// so these are tolerance-only (compared through Float32.toString 6-digit output).
export function lean_float32_sin(a: number): number {
  return f32(Math.sin, a)
}

export function lean_float32_cos(a: number): number {
  return f32(Math.cos, a)
}

export function lean_float32_tan(a: number): number {
  return f32(Math.tan, a)
}

export function lean_float32_asin(a: number): number {
  return f32(Math.asin, a)
}

export function lean_float32_acos(a: number): number {
  return f32(Math.acos, a)
}

export function lean_float32_atan(a: number): number {
  return f32(Math.atan, a)
}

export function lean_float32_atan2(a: number, b: number): number {
  return f(Math.atan2(f(a), f(b)))
}

export function lean_float32_sinh(a: number): number {
  return f32(Math.sinh, a)
}

export function lean_float32_cosh(a: number): number {
  return f32(Math.cosh, a)
}

export function lean_float32_tanh(a: number): number {
  return f32(Math.tanh, a)
}

export function lean_float32_asinh(a: number): number {
  return f32(Math.asinh, a)
}

export function lean_float32_acosh(a: number): number {
  return f32(Math.acosh, a)
}

export function lean_float32_atanh(a: number): number {
  return f32(Math.atanh, a)
}

export function lean_float32_exp(a: number): number {
  return f32(Math.exp, a)
}

export function lean_float32_exp2(a: number): number {
  return f(Math.pow(2, f(a)))
}

export function lean_float32_log(a: number): number {
  return f32(Math.log, a)
}

export function lean_float32_log2(a: number): number {
  return f32(Math.log2, a)
}

export function lean_float32_log10(a: number): number {
  return f32(Math.log10, a)
}

export function lean_float32_pow(a: number, b: number): number {
  return f(Math.pow(f(a), f(b)))
}

export function lean_float32_cbrt(a: number): number {
  return f32(Math.cbrt, a)
}

export function lean_float32_to_uint8(a: number): number {
  return Number(floatToUint(f(a), 8))
}

export function lean_float32_to_uint16(a: number): number {
  return Number(floatToUint(f(a), 16))
}

export function lean_float32_to_uint32(a: number): number {
  return Number(floatToUint(f(a), 32))
}

export function lean_float32_to_uint64(a: number): bigint {
  return floatToUint(f(a), 64)
}

export function lean_float32_to_usize(a: number): bigint {
  return floatToUint(f(a), 64)
}

// Float32 bit reinterpret (EXACT): lean_float32_of_bits / to_bits use UInt32.
const f32dv = new DataView(new ArrayBuffer(4))

export function lean_float32_to_bits(x: number): number {
  f32dv.setFloat32(0, f(x))
  return f32dv.getUint32(0)
}

export function lean_float32_of_bits(b: number): number {
  f32dv.setUint32(0, b >>> 0)
  return f32dv.getFloat32(0)
}

export function lean_float32_scaleb(x: number, i: Obj): number {
  return f(f(x) * Math.pow(2, Number(asNat(i))))
}

export function lean_float32_frexp(x: number): Ctor {
  const [m, e] = frexp(f(x))
  return lean_ctor(0, 2, 0, 0, f(m), e)
}

export function lean_uint8_to_float32(a: number): number {
  return f(a)
}

export function lean_uint16_to_float32(a: number): number {
  return f(a)
}

export function lean_uint32_to_float32(a: number): number {
  return f(a)
}

export function lean_uint64_to_float32(a: bigint): number {
  return f(Number(a))
}

export function lean_usize_to_float32(a: bigint): number {
  return f(Number(a))
}

export function lean_usize_to_float(a: bigint): number {
  return Number(a)
}

export function lean_uint64_to_float(a: bigint): number {
  return Number(a)
}

export function lean_uint32_to_float(a: number): number {
  return a
}
