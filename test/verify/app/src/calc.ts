import { lean } from "lean-ts"
import type { Nat } from "lean-ts/schema"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/calc.ts"

export const specBlock = lean(
  "spec",
  String.raw`
def clampSpec (x lo hi : Int) : Int := max lo (min hi x)

def ordered (_x lo hi : Int) : Bool := lo ≤ hi

def inRange (_x lo hi : Int) (r : Int) : Bool := lo ≤ r && r ≤ hi

def firstOr (xs : List Int) (d : Int) : Int := xs.headD d

def sumTo (n : Nat) : Nat := n * (n + 1) / 2

def nonneg (_xs : List Int) (r : Int) : Bool := 0 ≤ r

def double (x : Int) : Int := 2 * x
`,
)

export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo
  if (x > hi) return hi
  return x
}

model(clamp, {
  refines: spec.clampSpec,
  requires: spec.ordered,
  ensures: { inRange: spec.inRange },
})

export function firstOr(xs: readonly number[], d: number): number {
  return xs[0] ?? d
}

model(firstOr, { refines: spec.firstOr })

export function sumTo(n: Nat): Nat {
  let total = 0n
  for (let i = 0n; i <= n; i++) total += i
  return total
}

model(sumTo, { refines: spec.sumTo })

export function sumAbs(xs: readonly number[]): number {
  let total = 0
  for (const x of xs) total += Math.abs(x)
  return total
}

model(sumAbs, { ensures: { nonneg: spec.nonneg } })

export const twice = (x: number): number => x + x

model(twice, { refines: spec.double })
