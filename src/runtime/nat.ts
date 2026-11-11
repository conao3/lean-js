import type { Obj } from "./object.ts"
import { asNat, lean_bool } from "./object.ts"

// ---- Nat (bigint, total: /0 and %0 -> 0/lhs; sub is truncated monus) ----
export function lean_nat_add(a: Obj, b: Obj): bigint {
  return asNat(a) + asNat(b)
}

export function lean_nat_sub(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  return x > y ? x - y : 0n
}

export function lean_nat_mul(a: Obj, b: Obj): bigint {
  return asNat(a) * asNat(b)
}

export function lean_nat_div(a: Obj, b: Obj): bigint {
  const y = asNat(b)
  return y === 0n ? 0n : asNat(a) / y
}

export function lean_nat_mod(a: Obj, b: Obj): bigint {
  const x = asNat(a)
  const y = asNat(b)
  return y === 0n ? x : x % y
}

export function lean_nat_pow(a: Obj, b: Obj): bigint {
  return asNat(a) ** asNat(b)
}

export function lean_nat_pred(a: Obj): bigint {
  const x = asNat(a)
  return x > 0n ? x - 1n : 0n
}

export function lean_nat_gcd(a: Obj, b: Obj): bigint {
  let x = asNat(a)
  let y = asNat(b)
  while (y) {
    ;[x, y] = [y, x % y]
  }
  return x
}

export function lean_nat_dec_eq(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) === asNat(b))
}

export function lean_nat_dec_lt(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) < asNat(b))
}

export function lean_nat_dec_le(a: Obj, b: Obj): number {
  return lean_bool(asNat(a) <= asNat(b))
}

export function lean_nat_log2(a: Obj): bigint {
  let n = asNat(a)
  let r = 0n
  while (n > 1n) {
    n >>= 1n
    r += 1n
  }
  return r
}

export function lean_nat_shift_left(a: Obj, b: Obj): bigint {
  return asNat(a) << asNat(b)
}

export function lean_nat_shift_right(a: Obj, b: Obj): bigint {
  return asNat(a) >> asNat(b)
}

export function lean_nat_land(a: Obj, b: Obj): bigint {
  return asNat(a) & asNat(b)
}

export function lean_nat_lor(a: Obj, b: Obj): bigint {
  return asNat(a) | asNat(b)
}

export function lean_nat_xor(a: Obj, b: Obj): bigint {
  return asNat(a) ^ asNat(b)
}
