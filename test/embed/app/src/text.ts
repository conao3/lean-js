import * as L from "lean-ts"
import * as greetingLean from "./_lean/text__greeting.ts"
import * as wordsLean from "./_lean/text__words.ts"

export const greeting = L.lean(
  "greeting",
  `
def greet (name : String) : String := "hello, " ++ name ++ "\\n"

def shout (s : String) : String := s.toUpper
`,
  { imports: ["Std.Data.HashMap"] },
)

export const words = L.lean(
  "words",
  String.raw`
def wordCount (s : String) : Nat := (s.splitOn " ").length
`,
)

export function greetAll(names: readonly string[]): string {
  return (
    names.map((n) => greetingLean.greet(n)).join("") + String(wordsLean.wordCount(names.join(" ")))
  )
}
