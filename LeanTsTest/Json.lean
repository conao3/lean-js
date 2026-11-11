import Lean.Data.Json

/-! Values with `deriving ToJson, FromJson` whose JSON `test/json.test.ts` compares with `stringify` and `parse`. -/

open Lean

namespace LeanTsTest.Json

structure Inner where
  n : Nat
  s : String
  deriving ToJson, FromJson

inductive Color where
  | red
  | green
  deriving ToJson, FromJson

inductive Shape where
  | dot
  | circle (r : Nat)
  | rect (w h : Nat)
  | tagged : String → Shape
  | pair : Nat → Bool → Shape
  | wrap (inner : Inner)
  deriving ToJson, FromJson

inductive Tree where
  | leaf
  | node (l : Tree) (v : Int) (r : Tree)
  deriving ToJson, FromJson

structure Record where
  inner : Inner
  opt : Option Nat
  note? : Option String := none
  xs : List Int
  arr : Array String
  pair : Nat × String
  color : Color
  shape : Shape
  tree : Tree
  big : Nat
  flag : Bool
  f : Float
  u64 : UInt64
  nested : List (Option (Nat × Bool))
  deriving ToJson, FromJson

structure Child extends Inner where
  extra : Bool
  deriving ToJson, FromJson

def record1 : Record :=
  { inner := ⟨1, "one"⟩, opt := some 3, note? := some "hi", xs := [-1, 0, 2 ^ 70], arr := #["a", "é"],
    pair := (7, "seven"), color := .green, shape := .rect 2 3,
    tree := .node (.node .leaf (-5) .leaf) 6 .leaf, big := 2 ^ 80, flag := true, f := 2.5,
    u64 := 18446744073709551615, nested := [some (1, true), none] }

def record2 : Record :=
  { inner := ⟨0, ""⟩, opt := none, xs := [], arr := #[], pair := (0, ""), color := .red,
    shape := .dot, tree := .leaf, big := 0, flag := false, f := -0.25, u64 := 0, nested := [] }

def shapes : List Shape :=
  [.dot, .circle 4, .rect 1 2, .tagged "t", .pair 9 false, .wrap ⟨5, "five"⟩]

def child : Child := { n := 2, s := "two", extra := true }

def colors : Array Color := #[.red, .green]

end LeanTsTest.Json
