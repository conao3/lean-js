import { mkdtempSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { LeanIOError } from "lean-ts/runtime"
import { m } from "./code.ts"

const dir = mkdtempSync(join(tmpdir(), "lean-ts-step-07-"))
const f = join(dir, "log.txt")
writeFileSync(f, "one\ntwo\n")
m.appendLine(f, "three")
console.log(m.countLines(f).toString())
m.greet("Lean")
process.env["GREETING"] = "Bonjour"
m.greet("Lean")
try {
  m.countLines(join(dir, "missing.txt"))
} catch (e) {
  if (e instanceof LeanIOError) console.log(e.name, e.code, e.message.includes("no such file"))
}
