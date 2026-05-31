import Std.Data.HashMap

-- Independent verifier-authored realistic program (NOT in the implementer set).
-- Exercises: a recursive JSON-like value with a hand-written pretty printer,
-- run-length encode/decode round-trip over Char lists, integer matrix multiply
-- with Array (Array Int), Dijkstra-ish relaxation over a Std.HashMap-backed
-- adjacency structure, and List/Option combinators. Written non-exponentially.

namespace LeanJs.DemoVerify

-- A small recursive JSON value + pretty printer.
inductive JVal where
  | jnull
  | jbool (b : Bool)
  | jint (n : Int)
  | jstr (s : String)
  | jarr (xs : List JVal)
  | jobj (kvs : List (String × JVal))

partial def render : JVal → String
  | .jnull => "null"
  | .jbool b => if b then "true" else "false"
  | .jint n => toString n
  | .jstr s => "\"" ++ s ++ "\""
  | .jarr xs => "[" ++ String.intercalate "," (xs.map render) ++ "]"
  | .jobj kvs =>
    "{" ++ String.intercalate ","
      (kvs.map (fun (k, v) => "\"" ++ k ++ "\":" ++ render v)) ++ "}"

def sample : JVal :=
  .jobj [("name", .jstr "lean"), ("ver", .jint 4),
         ("tags", .jarr [.jstr "ir", .jstr "ts", .jnull]),
         ("ok", .jbool true), ("nested", .jobj [("x", .jint (-7))])]

-- Run-length encode / decode round-trip over Char lists.
partial def rleGo (cur : Char) (cnt : Nat) : List Char → List (Char × Nat)
  | [] => [(cur, cnt)]
  | d :: ds => if d == cur then rleGo cur (cnt + 1) ds else (cur, cnt) :: rleGo d 1 ds

def rleEnc : List Char → List (Char × Nat)
  | [] => []
  | c :: rest => rleGo c 1 rest

def rleDec (ps : List (Char × Nat)) : List Char :=
  ps.foldr (fun (c, n) acc => (List.replicate n c) ++ acc) []

-- Integer matrix multiply over Array (Array Int).
def dot (r : Array Int) (c : Array Int) : Int :=
  (Array.range r.size).foldl (fun s k => s + r[k]! * c[k]!) 0

def col (m : Array (Array Int)) (j : Nat) : Array Int :=
  m.map (fun row => row[j]!)

def matmul (a : Array (Array Int)) (b : Array (Array Int)) : Array (Array Int) :=
  let bcols := if b.size == 0 then 0 else b[0]!.size
  a.map (fun row => (Array.range bcols).map (fun j => dot row (col b j)))

-- One round of Dijkstra-ish relaxation using a Std.HashMap dist map.
def relax (edges : List (String × String × Nat)) (dist : Std.HashMap String Nat) :
    Std.HashMap String Nat :=
  edges.foldl (fun d (u, v, w) =>
    match d.get? u with
    | some du =>
      let alt := du + w
      match d.get? v with
      | some dv => if alt < dv then d.insert v alt else d
      | none => d.insert v alt
    | none => d) dist

-- Build a deterministic distance map after `rounds` relaxation passes.
def shortest (edges : List (String × String × Nat)) (src : String) (rounds : Nat) :
    Std.HashMap String Nat :=
  let init := (Std.HashMap.emptyWithCapacity : Std.HashMap String Nat).insert src 0
  (List.range rounds).foldl (fun d _ => relax edges d) init

def verifyMain : IO Unit := do
  IO.println s!"json = {render sample}"
  let cs := "aaabbbcccd".toList ++ "eee".toList
  let enc := rleEnc cs
  let encStr := enc.map (fun (c, n) => toString c ++ toString n)
  IO.println s!"rle = {encStr}"
  IO.println s!"rle-roundtrip = {String.ofList (rleDec enc) == String.ofList cs}"
  let a : Array (Array Int) := #[#[1, 2, 3], #[4, 5, 6]]
  let b : Array (Array Int) := #[#[7, 8], #[9, 10], #[11, 12]]
  IO.println s!"matmul = {matmul a b}"
  let edges : List (String × String × Nat) :=
    [("a", "b", 4), ("a", "c", 1), ("c", "b", 1), ("b", "d", 1), ("c", "d", 5)]
  let dist := shortest edges "a" 4
  let keys := ["a", "b", "c", "d"]
  IO.println s!"dist = {keys.map (fun k => (k, dist.getD k 999))}"

end LeanJs.DemoVerify
