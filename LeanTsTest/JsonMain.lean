import LeanTsTest.Json

open Lean LeanTsTest.Json

def main : IO Unit := do
  IO.println (toJson record1).compress
  IO.println (toJson record2).compress
  IO.println (toJson shapes).compress
  IO.println (toJson child).compress
  IO.println (toJson colors).compress
