import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
inductive Suit where
  | hearts | diamonds | clubs | spades

def Suit.isRed : Suit → Bool
  | .hearts | .diamonds => true
  | _ => false

inductive Expr where
  | num (n : Int)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)

def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .neg a => - a.eval

def Expr.simp : Expr → Expr
  | .add (.num 0) e | .add e (.num 0) => e.simp
  | .mul (.num 1) e | .mul e (.num 1) => e.simp
  | .add a b => .add a.simp b.simp
  | .mul a b => .mul a.simp b.simp
  | .neg a => .neg a.simp
  | e => e
`,
)

export { m }
