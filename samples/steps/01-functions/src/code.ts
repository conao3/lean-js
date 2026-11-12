import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
def double (n : Nat) : Nat := 2 * n

def greet (name : String) : String := s!"Hello, {name}!"

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range (n - 2)).all fun k => n % (k + 2) != 0
`,
)

export { m }
