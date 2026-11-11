import type { Obj } from "./object.ts"
import { asNat, lean_bool } from "./object.ts"

// ---- Int (bigint). div/mod = T-rounding; ediv/emod = Euclidean. ----
export function lean_int_add(a: Obj, b: Obj): bigint {
  return asNat(a) + asNat(b)
}

export function lean_int_sub(a: Obj, b: Obj): bigint {
  return asNat(a) - asNat(b)
}

export function lean_int_mul(a: Obj, b: Obj): bigint {
  return asNat(a) * asNat(b)
}

export function lean_int_neg(a: Obj): bigint {
  return -asNat(a)
}

export function lean_int_div(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  return y === 0n ? 0n : x / y
}

export function lean_int_mod(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  return y === 0n ? x : x % y
}

export function lean_int_emod(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  if (y === 0n) return x
  const r = x % y
  return r < 0n ? r + (y < 0n ? -y : y) : r
}

export function lean_int_ediv(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  if (y === 0n) return 0n
  const q = x / y
  const r = x % y
  return r < 0n ? (y > 0n ? q - 1n : q + 1n) : q
}

export function lean_int_dec_eq(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) === asNat(b))
}

export function lean_int_dec_lt(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) < asNat(b))
}

export function lean_int_dec_le(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) <= asNat(b))
}

export function lean_int_of_nat(n: Obj): bigint {
  return asNat(n)
}

export function lean_int_neg_succ_of_nat(n: Obj): bigint {
  return -(asNat(n) + 1n)
}

export function lean_int_to_nat(i: Obj): bigint {
  const x = asNat(i)
  return x < 0n ? 0n : x
}

export function lean_nat_abs(i: Obj): bigint {
  const x = asNat(i)
  return x < 0n ? -x : x
}

// ---- Signed fixed-width ints Int8/16/32/64/ISize ----
// Int8/16/32 share the IR scalar types uint8/16/32, so they are JS numbers
// holding the unsigned bit pattern (lean.h stores int8_t in a uint8_t); every
// op reinterprets its operands as signed, computes in bigint and stores the
// result back as the unsigned pattern. Int64/ISize are bigints in two's
// complement, and every op normalizes its operands first, since a value read
// back from a packed field arrives as the unsigned 64-bit pattern.
// div truncates toward zero and (MIN/-1) wraps to MIN (no trap); mod takes the
// sign of the dividend; div-by-zero -> 0, mod-by-zero -> lhs (total, like Int).
// shiftRight is arithmetic (sign-extending); the shift amount is reduced into
// [0, bits). complement = ~.
function sh(bits: number, b: bigint): bigint {
  const B = BigInt(bits)
  return ((b % B) + B) % B
}

function s8(x: number): bigint {
  return BigInt.asIntN(8, BigInt(x))
}

function w8(x: bigint): number {
  return Number(BigInt.asUintN(8, x))
}

export function lean_int8_of_int(i: Obj): number {
  return w8(asNat(i))
}

export function lean_int8_of_nat(n: Obj): number {
  return w8(asNat(n))
}

export function lean_int8_to_int(x: number): bigint {
  return s8(x)
}

export function lean_int8_add(a: number, b: number): number {
  return w8(s8(a) + s8(b))
}

export function lean_int8_sub(a: number, b: number): number {
  return w8(s8(a) - s8(b))
}

export function lean_int8_mul(a: number, b: number): number {
  return w8(s8(a) * s8(b))
}

export function lean_int8_div(a: number, b: number): number {
  return s8(b) === 0n ? 0 : w8(s8(a) / s8(b))
}

export function lean_int8_mod(a: number, b: number): number {
  return s8(b) === 0n ? w8(s8(a)) : w8(s8(a) % s8(b))
}

export function lean_int8_neg(a: number): number {
  return w8(-s8(a))
}

export function lean_int8_land(a: number, b: number): number {
  return w8(s8(a) & s8(b))
}

export function lean_int8_lor(a: number, b: number): number {
  return w8(s8(a) | s8(b))
}

export function lean_int8_xor(a: number, b: number): number {
  return w8(s8(a) ^ s8(b))
}

export function lean_int8_complement(a: number): number {
  return w8(~s8(a))
}

export function lean_int8_shift_left(a: number, b: number): number {
  return w8(s8(a) << sh(8, s8(b)))
}

export function lean_int8_shift_right(a: number, b: number): number {
  return w8(s8(a) >> sh(8, s8(b)))
}

export function lean_int8_dec_eq(a: number, b: number): number {
  return lean_bool(s8(a) === s8(b))
}

export function lean_int8_dec_lt(a: number, b: number): number {
  return lean_bool(s8(a) < s8(b))
}

export function lean_int8_dec_le(a: number, b: number): number {
  return lean_bool(s8(a) <= s8(b))
}

function s16(x: number): bigint {
  return BigInt.asIntN(16, BigInt(x))
}

function w16(x: bigint): number {
  return Number(BigInt.asUintN(16, x))
}

export function lean_int16_of_int(i: Obj): number {
  return w16(asNat(i))
}

export function lean_int16_of_nat(n: Obj): number {
  return w16(asNat(n))
}

export function lean_int16_to_int(x: number): bigint {
  return s16(x)
}

export function lean_int16_add(a: number, b: number): number {
  return w16(s16(a) + s16(b))
}

export function lean_int16_sub(a: number, b: number): number {
  return w16(s16(a) - s16(b))
}

export function lean_int16_mul(a: number, b: number): number {
  return w16(s16(a) * s16(b))
}

export function lean_int16_div(a: number, b: number): number {
  return s16(b) === 0n ? 0 : w16(s16(a) / s16(b))
}

export function lean_int16_mod(a: number, b: number): number {
  return s16(b) === 0n ? w16(s16(a)) : w16(s16(a) % s16(b))
}

export function lean_int16_neg(a: number): number {
  return w16(-s16(a))
}

export function lean_int16_land(a: number, b: number): number {
  return w16(s16(a) & s16(b))
}

export function lean_int16_lor(a: number, b: number): number {
  return w16(s16(a) | s16(b))
}

export function lean_int16_xor(a: number, b: number): number {
  return w16(s16(a) ^ s16(b))
}

export function lean_int16_complement(a: number): number {
  return w16(~s16(a))
}

export function lean_int16_shift_left(a: number, b: number): number {
  return w16(s16(a) << sh(16, s16(b)))
}

export function lean_int16_shift_right(a: number, b: number): number {
  return w16(s16(a) >> sh(16, s16(b)))
}

export function lean_int16_dec_eq(a: number, b: number): number {
  return lean_bool(s16(a) === s16(b))
}

export function lean_int16_dec_lt(a: number, b: number): number {
  return lean_bool(s16(a) < s16(b))
}

export function lean_int16_dec_le(a: number, b: number): number {
  return lean_bool(s16(a) <= s16(b))
}

function s32(x: number): bigint {
  return BigInt.asIntN(32, BigInt(x))
}

function w32(x: bigint): number {
  return Number(BigInt.asUintN(32, x))
}

export function lean_int32_of_int(i: Obj): number {
  return w32(asNat(i))
}

export function lean_int32_of_nat(n: Obj): number {
  return w32(asNat(n))
}

export function lean_int32_to_int(x: number): bigint {
  return s32(x)
}

export function lean_int32_add(a: number, b: number): number {
  return w32(s32(a) + s32(b))
}

export function lean_int32_sub(a: number, b: number): number {
  return w32(s32(a) - s32(b))
}

export function lean_int32_mul(a: number, b: number): number {
  return w32(s32(a) * s32(b))
}

export function lean_int32_div(a: number, b: number): number {
  return s32(b) === 0n ? 0 : w32(s32(a) / s32(b))
}

export function lean_int32_mod(a: number, b: number): number {
  return s32(b) === 0n ? w32(s32(a)) : w32(s32(a) % s32(b))
}

export function lean_int32_neg(a: number): number {
  return w32(-s32(a))
}

export function lean_int32_land(a: number, b: number): number {
  return w32(s32(a) & s32(b))
}

export function lean_int32_lor(a: number, b: number): number {
  return w32(s32(a) | s32(b))
}

export function lean_int32_xor(a: number, b: number): number {
  return w32(s32(a) ^ s32(b))
}

export function lean_int32_complement(a: number): number {
  return w32(~s32(a))
}

export function lean_int32_shift_left(a: number, b: number): number {
  return w32(s32(a) << sh(32, s32(b)))
}

export function lean_int32_shift_right(a: number, b: number): number {
  return w32(s32(a) >> sh(32, s32(b)))
}

export function lean_int32_dec_eq(a: number, b: number): number {
  return lean_bool(s32(a) === s32(b))
}

export function lean_int32_dec_lt(a: number, b: number): number {
  return lean_bool(s32(a) < s32(b))
}

export function lean_int32_dec_le(a: number, b: number): number {
  return lean_bool(s32(a) <= s32(b))
}

function s64(x: bigint): bigint {
  return BigInt.asIntN(64, x)
}

export function lean_int64_of_int(i: Obj): bigint {
  return s64(asNat(i))
}

export function lean_int64_of_nat(n: Obj): bigint {
  return s64(asNat(n))
}

export function lean_int64_to_int_sint(x: bigint): bigint {
  return s64(x)
}

export function lean_int64_add(a: bigint, b: bigint): bigint {
  return s64(s64(a) + s64(b))
}

export function lean_int64_sub(a: bigint, b: bigint): bigint {
  return s64(s64(a) - s64(b))
}

export function lean_int64_mul(a: bigint, b: bigint): bigint {
  return s64(s64(a) * s64(b))
}

export function lean_int64_div(a: bigint, b: bigint): bigint {
  return s64(b) === 0n ? 0n : s64(s64(a) / s64(b))
}

export function lean_int64_mod(a: bigint, b: bigint): bigint {
  return s64(b) === 0n ? s64(a) : s64(s64(a) % s64(b))
}

export function lean_int64_neg(a: bigint): bigint {
  return s64(-s64(a))
}

export function lean_int64_land(a: bigint, b: bigint): bigint {
  return s64(s64(a) & s64(b))
}

export function lean_int64_lor(a: bigint, b: bigint): bigint {
  return s64(s64(a) | s64(b))
}

export function lean_int64_xor(a: bigint, b: bigint): bigint {
  return s64(s64(a) ^ s64(b))
}

export function lean_int64_complement(a: bigint): bigint {
  return s64(~s64(a))
}

export function lean_int64_shift_left(a: bigint, b: bigint): bigint {
  return s64(s64(a) << sh(64, s64(b)))
}

export function lean_int64_shift_right(a: bigint, b: bigint): bigint {
  return s64(s64(a) >> sh(64, s64(b)))
}

export function lean_int64_dec_eq(a: bigint, b: bigint): number {
  return lean_bool(s64(a) === s64(b))
}

export function lean_int64_dec_lt(a: bigint, b: bigint): number {
  return lean_bool(s64(a) < s64(b))
}

export function lean_int64_dec_le(a: bigint, b: bigint): number {
  return lean_bool(s64(a) <= s64(b))
}

export function lean_isize_of_int(i: Obj): bigint {
  return s64(asNat(i))
}

export function lean_isize_of_nat(n: Obj): bigint {
  return s64(asNat(n))
}

export function lean_isize_to_int_sint(x: bigint): bigint {
  return s64(x)
}

export function lean_isize_add(a: bigint, b: bigint): bigint {
  return s64(s64(a) + s64(b))
}

export function lean_isize_sub(a: bigint, b: bigint): bigint {
  return s64(s64(a) - s64(b))
}

export function lean_isize_mul(a: bigint, b: bigint): bigint {
  return s64(s64(a) * s64(b))
}

export function lean_isize_div(a: bigint, b: bigint): bigint {
  return s64(b) === 0n ? 0n : s64(s64(a) / s64(b))
}

export function lean_isize_mod(a: bigint, b: bigint): bigint {
  return s64(b) === 0n ? s64(a) : s64(s64(a) % s64(b))
}

export function lean_isize_neg(a: bigint): bigint {
  return s64(-s64(a))
}

export function lean_isize_land(a: bigint, b: bigint): bigint {
  return s64(s64(a) & s64(b))
}

export function lean_isize_lor(a: bigint, b: bigint): bigint {
  return s64(s64(a) | s64(b))
}

export function lean_isize_xor(a: bigint, b: bigint): bigint {
  return s64(s64(a) ^ s64(b))
}

export function lean_isize_complement(a: bigint): bigint {
  return s64(~s64(a))
}

export function lean_isize_shift_left(a: bigint, b: bigint): bigint {
  return s64(s64(a) << sh(64, s64(b)))
}

export function lean_isize_shift_right(a: bigint, b: bigint): bigint {
  return s64(s64(a) >> sh(64, s64(b)))
}

export function lean_isize_dec_eq(a: bigint, b: bigint): number {
  return lean_bool(s64(a) === s64(b))
}

export function lean_isize_dec_lt(a: bigint, b: bigint): number {
  return lean_bool(s64(a) < s64(b))
}

export function lean_isize_dec_le(a: bigint, b: bigint): number {
  return lean_bool(s64(a) <= s64(b))
}
