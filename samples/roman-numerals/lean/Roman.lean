namespace Roman

private def numerals : List (Nat × String) :=
  [(1000, "M"), (900, "CM"), (500, "D"), (400, "CD"), (100, "C"), (90, "XC"),
   (50, "L"), (40, "XL"), (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")]

private def toRomanAux : Nat → List (Nat × String) → Nat → String
  | 0, _, _ => ""
  | _, [], _ => ""
  | fuel + 1, (v, s) :: rest, n =>
    if v ≤ n then s ++ toRomanAux fuel ((v, s) :: rest) (n - v) else toRomanAux fuel rest n

def toRoman (n : Nat) : String := toRomanAux (n + 13) numerals n

private def value : Char → Nat
  | 'I' => 1 | 'V' => 5 | 'X' => 10 | 'L' => 50 | 'C' => 100 | 'D' => 500 | 'M' => 1000 | _ => 0

private def fromRomanAux : List Char → Option Nat
  | [] => some 0
  | c :: rest =>
    if value c == 0 then none
    else match rest with
      | d :: _ => if value c < value d then (fromRomanAux rest).map (· - value c) else (fromRomanAux rest).map (· + value c)
      | [] => some (value c)

def fromRoman (s : String) : Option Nat :=
  if s.isEmpty then none else fromRomanAux s.toList

theorem toRoman_1994 : toRoman 1994 = "MCMXCIV" := by decide +kernel

theorem roundtrip : ∀ n, n < 1000 → fromRoman (toRoman n) = if n = 0 then none else some n := by decide +kernel

end Roman
