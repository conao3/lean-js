import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as more from "./_lean/more.ts"
import type { Color, Point, Shape } from "./_lean/more.ts"

export const moreBlock = lean(
  "more",
  String.raw`
structure Point where
  x : Int
  y : Int

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

inductive Color where
  | red
  | green
  | blue

def manhattan (p : Point) : Int := (if p.x < 0 then -p.x else p.x) + (if p.y < 0 then -p.y else p.y)

def area (s : Shape) : Int :=
  match s with
  | .circle r => 3 * r * r
  | .rect w h => w * h

def code (c : Color) : Int :=
  match c with
  | .red => 1
  | .green => 2
  | .blue => 3

def shift (p : Point) (d : Int) : Point := { x := p.x + d, y := p.y }

def evens (xs : List Int) : List Int := xs.filter (fun x => x % 2 == 0)

def label (n : Int) : String := "n=" ++ toString n

def countDown (n : Int) : List Int := (List.range n.toNat).reverse.map (fun (k : Nat) => (k : Int) + 1)

def safeDiv (a b : Int) : Int := if b = 0 then 0 else a.tdiv b

def sumSquares (xs : List Int) : Int := (xs.map (fun x => x * x)).foldl (· + ·) 0

def firstPositive (xs : List Int) : Option Int := xs.find? (fun x => 0 < x)

def describe (o : Option Int) : Int :=
  match o with
  | some v => v
  | none => -1

def isNonNeg (x : Int) : Bool := 0 ≤ x

def same (x : Int) : Int := x

def swap (p : Int × Int) : Int × Int := (p.2, p.1)

def tag (s : String) (n : Int) : String := if s.startsWith "a" then s ++ "!" else s ++ "?" ++ toString n
`,
)

export function manhattan(p: Point): bigint {
  return (p.x < 0n ? -p.x : p.x) + (p.y < 0n ? -p.y : p.y)
}

model(manhattan, { refines: more.manhattan })

export function area(s: Shape): bigint {
  switch (s.ctor) {
    case "circle":
      return 3n * s.r * s.r
    default:
      return s.w * s.h
  }
}

model(area, { refines: more.area })

export function code(c: Color): number {
  switch (c) {
    case "red":
      return 1
    case "green":
      return 2
    default:
      return 3
  }
}

model(code, { refines: more.code })

export function shift(p: Point, d: bigint): Point {
  return { x: p.x + d, y: p.y }
}

model(shift, { refines: more.shift })

export function evens(xs: readonly number[]): number[] {
  const out: number[] = []
  for (const x of xs) if (x % 2 === 0) out.push(x)
  return out
}

model(evens, { refines: more.evens })

export function label(n: number): string {
  return `n=${n}`
}

model(label, { refines: more.label })

export function countDown(n: number): number[] {
  const out: number[] = []
  let k = n
  while (k > 0) {
    out.push(k)
    k -= 1
  }
  return out
}

model(countDown, { refines: more.countDown })

export function safeDiv(a: number, b: number): number {
  if (b === 0) return 0
  return Math.trunc(a / b)
}

model(safeDiv, { refines: more.safeDiv })

export function sumSquares(xs: readonly number[]): number {
  return xs.map((x) => x * x).reduce((acc, x) => acc + x, 0)
}

model(sumSquares, { refines: more.sumSquares })

export function firstPositive(xs: readonly number[]): number | null {
  for (const x of xs) {
    if (x > 0) return x
  }
  return null
}

model(firstPositive, { refines: more.firstPositive })

export function describe(o: number | null): number {
  if (o === null) return -1
  return o
}

model(describe, { refines: more.describe })

export function nonNeg(x: number): number {
  if (x < 0) throw new RangeError("negative")
  return x
}

model(nonNeg, { refines: more.same, requires: more.isNonNeg })

export function swap(p: readonly [number, number]): [number, number] {
  const [a, b] = p
  return [b, a]
}

model(swap, { refines: more.swap })

export function tag(s: string, n: number): string {
  if (s.startsWith("a")) return s + "!"
  return s + "?" + n
}

model(tag, { refines: more.tag })
