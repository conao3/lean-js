import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as calendar from "./_lean/calendar.ts"

export const block = lean(
  "calendar",
  String.raw`
def leap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def leapYears (lo hi : Nat) : List Nat := (List.range (hi - lo)).map (· + lo) |>.filter (fun y => leap y)
`,
)

export function isLeap(year: number): boolean {
  if (year % 4 !== 0) return false
  if (year % 100 !== 0) return true
  return year % 400 === 0
}

model(isLeap, { refines: calendar.leap })

export { calendar }
