import { mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { LeanValidationError, parse, stringify } from "lean-ts/schema"
import { todos } from "./model.ts"

const store = join(mkdtempSync(join(tmpdir(), "lean-ts-todo-")), "todos.json")

let ts = todos.empty()
ts = todos.add(ts, "write the README", "high")
ts = todos.add(ts, "publish to npm", "normal")
ts = todos.add(ts, "water the plants", "low")
ts = todos.complete(ts, 0)
writeFileSync(store, stringify(todos.Todos, ts))
console.log(readFileSync(store, "utf8"))

const loaded = parse(todos.Todos, readFileSync(store, "utf8"))
console.log(JSON.stringify(todos.pending(loaded).map((t) => t.title)))
console.log(JSON.stringify(todos.byPriority(loaded, "high").map((t) => t.title)))

const tampered = readFileSync(store, "utf8").replace('"id":1', '"id":7')
try {
  parse(todos.Todos, tampered)
} catch (e) {
  if (e instanceof LeanValidationError) console.log("rejected:", e.issues[0]?.message)
}
