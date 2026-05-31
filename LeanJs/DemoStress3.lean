import Std.Data.HashMap
import Std.Data.HashSet

/-! Round-7 probes: HashMap/HashSet iteration order (bucket layout depends on
the hash being bit-identical to the native runtime) and Nat/UInt hashing. -/

namespace LeanJs.DemoStress3

def hmOrderProg : IO Unit := do
  let m : Std.HashMap String Nat :=
    (["zebra", "apple", "mango", "fig", "kiwi", "pear", "lime", "date"]).foldl
      (fun acc (w : String) => acc.insert w w.length) Std.HashMap.emptyWithCapacity
  -- toList order is determined by bucket layout = String hash mod capacity.
  IO.println s!"hm-str = {m.toList}"
  let mn : Std.HashMap Nat Nat :=
    ((List.range 16).foldl (fun acc i => acc.insert (i * 7 % 13) i) Std.HashMap.emptyWithCapacity)
  IO.println s!"hm-nat = {mn.toList}"
  let s : Std.HashSet Nat := ([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5].foldl (·.insert ·) Std.HashSet.emptyWithCapacity)
  IO.println s!"hs = {s.toList}"

def stress3Main : IO Unit := hmOrderProg

end LeanJs.DemoStress3
