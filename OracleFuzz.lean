import LeanJs.Fuzz

open LeanJs.Fuzz

partial def loop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let line := line.dropRightWhile (· == '\n')
  let parts := line.splitOn "\t"
  let out ← match parts with
    | ["NAT", a] => pure s!"NAT\t{fNat a.toNat!}"
    | ["INT", a, b] => pure s!"INT\t{fInt (parseInt a) (parseInt b)}"
    | ["U32", a, b] => pure s!"U32\t{fU32 a.toNat!.toUInt32 b.toNat!.toUInt32}"
    | ["U8", a, b] => pure s!"U8\t{fU8 a.toNat!.toUInt8 b.toNat!.toUInt8}"
    | ["STR", s] => pure s!"STR\t{fStr (unescape s)}"
    | ["HASH", s] => pure s!"HASH\t{fHash (unescape s)}"
    | "LNAT" :: rest => pure s!"LNAT\t{fListNat (parseNats rest)}"
    | "ANAT" :: rest => pure s!"ANAT\t{fArrNat (Array.mk (parseNats rest))}"
    | _ => pure s!"ERR\t{line}"
  IO.println out
  loop h

def main : IO Unit := do loop (← IO.getStdin)
