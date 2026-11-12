import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
open Std

def wordIndex (ws : List String) : List (String × List Nat) :=
  let idx : HashMap String (List Nat) := ws.zipIdx.foldl (fun m (w, i) => m.insert w (m.getD w [] ++ [i])) {}
  (idx.toList.toArray.qsort (fun a b => a.1 < b.1)).toList

def dedup (xs : List Nat) : List Nat :=
  let s : HashSet Nat := xs.foldl (·.insert ·) {}
  (s.toList.toArray.qsort (· < ·)).toList
`,
  { imports: ["Std.Data.HashMap", "Std.Data.HashSet"] },
)

export { m }
