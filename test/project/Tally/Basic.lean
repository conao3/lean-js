namespace Tally

def total (xs : List Nat) : Nat := xs.foldl (· + ·) 0

theorem total_nil : total [] = 0 := rfl

end Tally
