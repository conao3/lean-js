#!/usr/bin/env node
import { spawnSync } from "node:child_process"
import { readFileSync } from "node:fs"
import { leanTypescriptCli, readPackage, statusPackage, SyncError, syncPackage } from "./sync.ts"
import { checkPackage, csimpFiles, statusModels } from "./verify/check.ts"

const USAGE = `usage: lean-ts [--version] <command> [parameters]

commands:
  sync       Check the Lean blocks of a package and generate their TypeScript modules
  check      Translate the model(...) functions and judge the proofs of their obligations
  status     List the blocks whose generated modules are stale (no Lean)
  generate   Emit a TypeScript module per Lean module of a lake project

lean-ts sync
  --package <dir>            The package (the directory with package.json and src/) (required)
  --lean-typescript <path>   The Lean CLI (default: $LEAN_TYPESCRIPT, then lean-typescript on PATH)

lean-ts check
  --package <dir>            The package (required)
  --lean-typescript <path>   as for sync
  --require proved           Exit with 254 unless every obligation is proved
  Writes <dir>/lean-ts.lock and prints one line per obligation: <status> <module>:<function> <label>

lean-ts status
  --package <dir>            The package (required); exits with 254 when a block or an obligation is stale

lean-ts generate
  --lake-dir <dir>           Lake project to build (required)
  --output-dir <dir>         Directory of the TypeScript modules (required)
  --modules <Name> ...       Modules to emit (default: every module the project builds)
  --lean-typescript <path>   as for sync

exit codes: 0 success, 252 invalid parameters, 254 input that cannot be converted, 255 other errors
`

interface Args {
  readonly single: ReadonlyMap<string, string>
  readonly modules: readonly string[]
}

function parseArgs(argv: readonly string[], allowed: readonly string[]): Args {
  const single = new Map<string, string>()
  const modules: string[] = []
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i] ?? ""
    if (a === "--modules" && allowed.includes(a)) {
      while (i + 1 < argv.length && !(argv[i + 1] ?? "").startsWith("--"))
        modules.push(argv[++i] ?? "")
      continue
    }
    const v = argv[i + 1]
    if (!allowed.includes(a) || v === undefined || v.startsWith("--"))
      throw new SyncError(`unknown or incomplete parameter: ${a}`, 252)
    single.set(a, v)
    i++
  }
  return { single, modules }
}

function required(args: Args, name: string): string {
  const v = args.single.get(name)
  if (v === undefined) throw new SyncError(`${name} is required`, 252)
  return v
}

function log(line: string): void {
  process.stderr.write(line.endsWith("\n") ? line : `${line}\n`)
}

function version(): string {
  const pkg: unknown = JSON.parse(readFileSync(new URL("../package.json", import.meta.url), "utf8"))
  const v: unknown =
    typeof pkg === "object" && pkg !== null ? Reflect.get(pkg, "version") : undefined
  if (typeof v !== "string") throw new SyncError("package.json has no version", 255)
  return v
}

async function main(argv: readonly string[]): Promise<number> {
  const [command, ...rest] = argv
  if (command === undefined || command === "help" || command === "--help") {
    process.stdout.write(USAGE)
    return 0
  }
  if (command === "--version") {
    process.stdout.write(`${version()}\n`)
    return 0
  }
  if (command === "sync") {
    const args = parseArgs(rest, ["--package", "--lean-typescript"])
    await syncPackage(
      required(args, "--package"),
      args.single.get("--lean-typescript"),
      log,
      csimpFiles,
    )
    return 0
  }
  if (command === "check") {
    const args = parseArgs(rest, ["--package", "--lean-typescript", "--require"])
    const req = args.single.get("--require")
    if (req !== undefined && req !== "proved")
      throw new SyncError(`--require takes proved (got ${req})`, 252)
    const { rows } = await checkPackage(
      required(args, "--package"),
      args.single.get("--lean-typescript"),
      log,
    )
    for (const r of rows) process.stdout.write(`${r.status.padEnd(12)}${r.fn} ${r.label}\n`)
    return req === undefined || rows.every((r) => r.status === "proved") ? 0 : 254
  }
  if (command === "status") {
    const args = parseArgs(rest, ["--package"])
    const dir = required(args, "--package")
    const pkg = await readPackage(dir, false)
    const rows = statusPackage(pkg)
    for (const r of rows) process.stdout.write(`${r.state.padEnd(8)}${r.block}\n`)
    const models = statusModels(pkg)
    for (const r of models) process.stdout.write(`${r.status.padEnd(12)}${r.fn} ${r.label}\n`)
    return rows.every((r) => r.state === "fresh") && models.every((r) => r.status !== "stale")
      ? 0
      : 254
  }
  if (command === "generate") {
    const args = parseArgs(rest, ["--lake-dir", "--output-dir", "--modules", "--lean-typescript"])
    const cli = leanTypescriptCli(args.single.get("--lean-typescript"))
    const modules = args.modules.length === 0 ? [] : ["--modules", ...args.modules]
    const r = spawnSync(
      cli,
      [
        "project",
        "generate",
        "--lake-dir",
        required(args, "--lake-dir"),
        "--output-dir",
        required(args, "--output-dir"),
        ...modules,
        "--output",
        "text",
      ],
      { stdio: "inherit" },
    )
    if (r.error !== undefined) throw new SyncError(`cannot run ${cli}: ${r.error.message}`, 255)
    return r.status ?? 255
  }
  throw new SyncError(`unknown command ${command} (see \`lean-ts help\`)`, 252)
}

try {
  process.exitCode = await main(process.argv.slice(2))
} catch (e) {
  log(`lean-ts: ${e instanceof Error ? e.message : String(e)}`)
  process.exitCode = e instanceof SyncError ? e.code : 255
}
