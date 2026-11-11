import type { Obj } from "./object.ts"
import { asNat, lean_bool } from "./object.ts"

// USize / pointer width. The C runtime's size_t == sizeof(void*) (8 on 64-bit,
// 4 on 32-bit), and usize ctor slots / the packed-usize accessor width are
// derived from it. lean-ts targets a 64-bit-like host (BigInt for 64-bit), so
// WORD_BITS defaults to 64; route every usize-width decision through this single
// constant so a 32-bit profile is a one-line change.
export const WORD_BITS: number = 64

// ---- UIntN / USize: wrap-around modular arithmetic over 2^N ----
// Representation convention (matches scalar literal emission and `switch`):
//   UInt8/16/32 -> plain JS number ; UInt64/USize -> bigint.
// All binary ops wrap mod 2^N. div = unsigned floor (/0 -> 0); mod = unsigned
// remainder (%0 -> dividend). Shift amount reduced mod N. Comparisons unsigned
// and return the scalar 0/1 the emitted `switch` expects.
function um(bits: number, x: number): number {
  const mod = 2 ** bits
  let r = x % mod
  if (r < 0) r += mod
  return r
}

function bm(bits: number, x: bigint): bigint {
  return BigInt.asUintN(bits, x)
}

export function lean_uint8_of_nat(n: Obj): number {
  return um(8, Number(BigInt.asUintN(8, asNat(n))))
}

export function lean_uint8_add(a: number, b: number): number {
  return um(8, a + b)
}

export function lean_uint8_sub(a: number, b: number): number {
  return um(8, a - b)
}

export function lean_uint8_mul(a: number, b: number): number {
  return um(8, Number((BigInt(um(8, a)) * BigInt(um(8, b))) % BigInt(2 ** 8)))
}

export function lean_uint8_div(a: number, b: number): number {
  return b === 0 ? 0 : um(8, Math.trunc(um(8, a) / um(8, b)))
}

export function lean_uint8_mod(a: number, b: number): number {
  return b === 0 ? um(8, a) : um(8, um(8, a) % um(8, b))
}

export function lean_uint8_land(a: number, b: number): number {
  return um(8, Number(BigInt(um(8, a)) & BigInt(um(8, b))))
}

export function lean_uint8_lor(a: number, b: number): number {
  return um(8, Number(BigInt(um(8, a)) | BigInt(um(8, b))))
}

export function lean_uint8_xor(a: number, b: number): number {
  return um(8, Number(BigInt(um(8, a)) ^ BigInt(um(8, b))))
}

export function lean_uint8_complement(a: number): number {
  return um(8, 2 ** 8 - 1 - um(8, a))
}

export function lean_uint8_neg(a: number): number {
  return um(8, -um(8, a))
}

export function lean_uint8_shift_left(a: number, b: number): number {
  return um(8, Number(BigInt(um(8, a)) << BigInt(b % 8)))
}

export function lean_uint8_shift_right(a: number, b: number): number {
  return um(8, Number(BigInt(um(8, a)) >> BigInt(b % 8)))
}

export function lean_uint8_dec_eq(a: number, b: number): number {
  return lean_bool(um(8, a) === um(8, b))
}

export function lean_uint8_dec_lt(a: number, b: number): number {
  return lean_bool(um(8, a) < um(8, b))
}

export function lean_uint8_dec_le(a: number, b: number): number {
  return lean_bool(um(8, a) <= um(8, b))
}

export function lean_uint8_to_nat(a: number): bigint {
  return BigInt(um(8, a))
}

export function lean_uint16_of_nat(n: Obj): number {
  return um(16, Number(BigInt.asUintN(16, asNat(n))))
}

export function lean_uint16_add(a: number, b: number): number {
  return um(16, a + b)
}

export function lean_uint16_sub(a: number, b: number): number {
  return um(16, a - b)
}

export function lean_uint16_mul(a: number, b: number): number {
  return um(16, Number((BigInt(um(16, a)) * BigInt(um(16, b))) % BigInt(2 ** 16)))
}

export function lean_uint16_div(a: number, b: number): number {
  return b === 0 ? 0 : um(16, Math.trunc(um(16, a) / um(16, b)))
}

export function lean_uint16_mod(a: number, b: number): number {
  return b === 0 ? um(16, a) : um(16, um(16, a) % um(16, b))
}

export function lean_uint16_land(a: number, b: number): number {
  return um(16, Number(BigInt(um(16, a)) & BigInt(um(16, b))))
}

export function lean_uint16_lor(a: number, b: number): number {
  return um(16, Number(BigInt(um(16, a)) | BigInt(um(16, b))))
}

export function lean_uint16_xor(a: number, b: number): number {
  return um(16, Number(BigInt(um(16, a)) ^ BigInt(um(16, b))))
}

export function lean_uint16_complement(a: number): number {
  return um(16, 2 ** 16 - 1 - um(16, a))
}

export function lean_uint16_neg(a: number): number {
  return um(16, -um(16, a))
}

export function lean_uint16_shift_left(a: number, b: number): number {
  return um(16, Number(BigInt(um(16, a)) << BigInt(b % 16)))
}

export function lean_uint16_shift_right(a: number, b: number): number {
  return um(16, Number(BigInt(um(16, a)) >> BigInt(b % 16)))
}

export function lean_uint16_dec_eq(a: number, b: number): number {
  return lean_bool(um(16, a) === um(16, b))
}

export function lean_uint16_dec_lt(a: number, b: number): number {
  return lean_bool(um(16, a) < um(16, b))
}

export function lean_uint16_dec_le(a: number, b: number): number {
  return lean_bool(um(16, a) <= um(16, b))
}

export function lean_uint16_to_nat(a: number): bigint {
  return BigInt(um(16, a))
}

export function lean_uint32_add(a: number, b: number): number {
  return um(32, a + b)
}

export function lean_uint32_sub(a: number, b: number): number {
  return um(32, a - b)
}

export function lean_uint32_mul(a: number, b: number): number {
  return um(32, Number((BigInt(um(32, a)) * BigInt(um(32, b))) % BigInt(2 ** 32)))
}

export function lean_uint32_div(a: number, b: number): number {
  return b === 0 ? 0 : um(32, Math.trunc(um(32, a) / um(32, b)))
}

export function lean_uint32_mod(a: number, b: number): number {
  return b === 0 ? um(32, a) : um(32, um(32, a) % um(32, b))
}

export function lean_uint32_land(a: number, b: number): number {
  return um(32, Number(BigInt(um(32, a)) & BigInt(um(32, b))))
}

export function lean_uint32_lor(a: number, b: number): number {
  return um(32, Number(BigInt(um(32, a)) | BigInt(um(32, b))))
}

export function lean_uint32_xor(a: number, b: number): number {
  return um(32, Number(BigInt(um(32, a)) ^ BigInt(um(32, b))))
}

export function lean_uint32_complement(a: number): number {
  return um(32, 2 ** 32 - 1 - um(32, a))
}

export function lean_uint32_neg(a: number): number {
  return um(32, -um(32, a))
}

export function lean_uint32_shift_left(a: number, b: number): number {
  return um(32, Number(BigInt(um(32, a)) << BigInt(b % 32)))
}

export function lean_uint32_shift_right(a: number, b: number): number {
  return um(32, Number(BigInt(um(32, a)) >> BigInt(b % 32)))
}

export function lean_uint32_dec_eq(a: number, b: number): number {
  return lean_bool(um(32, a) === um(32, b))
}

export function lean_uint32_dec_lt(a: number, b: number): number {
  return lean_bool(um(32, a) < um(32, b))
}

export function lean_uint32_dec_le(a: number, b: number): number {
  return lean_bool(um(32, a) <= um(32, b))
}

export function lean_uint32_to_nat(a: number): bigint {
  return BigInt(um(32, a))
}

export function lean_uint64_of_nat(n: Obj): bigint {
  return bm(64, asNat(n))
}

export function lean_uint64_of_nat_mk(n: Obj): bigint {
  return bm(64, asNat(n))
}

export function lean_uint64_add(a: bigint, b: bigint): bigint {
  return bm(64, a + b)
}

export function lean_uint64_sub(a: bigint, b: bigint): bigint {
  return bm(64, a - b)
}

export function lean_uint64_mul(a: bigint, b: bigint): bigint {
  return bm(64, a * b)
}

export function lean_uint64_div(a: bigint, b: bigint): bigint {
  return b === 0n ? 0n : bm(64, a / b)
}

export function lean_uint64_mod(a: bigint, b: bigint): bigint {
  return b === 0n ? bm(64, a) : bm(64, a % b)
}

export function lean_uint64_land(a: bigint, b: bigint): bigint {
  return bm(64, a & b)
}

export function lean_uint64_lor(a: bigint, b: bigint): bigint {
  return bm(64, a | b)
}

export function lean_uint64_xor(a: bigint, b: bigint): bigint {
  return bm(64, a ^ b)
}

export function lean_uint64_complement(a: bigint): bigint {
  return bm(64, ~a)
}

export function lean_uint64_neg(a: bigint): bigint {
  return bm(64, -a)
}

export function lean_uint64_shift_left(a: bigint, b: bigint): bigint {
  return bm(64, a << (b % BigInt(64)))
}

export function lean_uint64_shift_right(a: bigint, b: bigint): bigint {
  return bm(64, a) >> (b % BigInt(64))
}

export function lean_uint64_dec_eq(a: bigint, b: bigint): number {
  return lean_bool(bm(64, a) === bm(64, b))
}

export function lean_uint64_dec_lt(a: bigint, b: bigint): number {
  return lean_bool(bm(64, a) < bm(64, b))
}

export function lean_uint64_dec_le(a: bigint, b: bigint): number {
  return lean_bool(bm(64, a) <= bm(64, b))
}

export function lean_uint64_to_nat(a: bigint): bigint {
  return bm(64, a)
}

export function lean_usize_of_nat(n: Obj): bigint {
  return bm(WORD_BITS, asNat(n))
}

export function lean_usize_add(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a + b)
}

export function lean_usize_sub(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a - b)
}

export function lean_usize_mul(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a * b)
}

export function lean_usize_div(a: bigint, b: bigint): bigint {
  return b === 0n ? 0n : bm(WORD_BITS, a / b)
}

export function lean_usize_mod(a: bigint, b: bigint): bigint {
  return b === 0n ? bm(WORD_BITS, a) : bm(WORD_BITS, a % b)
}

export function lean_usize_land(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a & b)
}

export function lean_usize_lor(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a | b)
}

export function lean_usize_xor(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a ^ b)
}

export function lean_usize_complement(a: bigint): bigint {
  return bm(WORD_BITS, ~a)
}

export function lean_usize_neg(a: bigint): bigint {
  return bm(WORD_BITS, -a)
}

export function lean_usize_shift_left(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a << (b % BigInt(WORD_BITS)))
}

export function lean_usize_shift_right(a: bigint, b: bigint): bigint {
  return bm(WORD_BITS, a) >> (b % BigInt(WORD_BITS))
}

export function lean_usize_dec_eq(a: bigint, b: bigint): number {
  return lean_bool(bm(WORD_BITS, a) === bm(WORD_BITS, b))
}

export function lean_usize_dec_lt(a: bigint, b: bigint): number {
  return lean_bool(bm(WORD_BITS, a) < bm(WORD_BITS, b))
}

export function lean_usize_dec_le(a: bigint, b: bigint): number {
  return lean_bool(bm(WORD_BITS, a) <= bm(WORD_BITS, b))
}

export function lean_usize_to_nat(a: bigint): bigint {
  return bm(WORD_BITS, a)
}

// UInt64 -> USize truncates to the platform word width; on the 64-bit profile
// this is an identity re-mask, on a 32-bit profile it drops the high 32 bits.
export function lean_uint64_to_usize(x: bigint): bigint {
  return BigInt.asUintN(WORD_BITS, x)
}

export function lean_uint32_of_nat(n: Obj): number {
  return Number(asNat(n) & 0xffffffffn)
}

export function lean_uint32_of_nat2(n: Obj): number {
  return Number(BigInt.asUintN(32, asNat(n)))
}

// System.Platform.getNumBits : the platform word size. Derived from WORD_BITS so
// that flipping the single knob to 32 keeps getNumBits, USize.size, and the
// usize arithmetic wrap all consistent on a 32-bit profile.
export function lean_system_platform_nbits(_unit?: Obj): bigint {
  return BigInt(WORD_BITS)
}

export function lean_uint32_of_nat_mk(n: Obj): number {
  return lean_uint32_of_nat(n)
}

export function lean_uint8_to_uint64(a: number): bigint {
  return BigInt(a)
}

export function lean_uint16_to_uint64(a: number): bigint {
  return BigInt(a)
}

export function lean_uint32_to_uint64(a: number): bigint {
  return BigInt(a)
}

export function lean_usize_to_uint64(a: bigint): bigint {
  return a
}
