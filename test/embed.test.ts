import { spawnSync } from "node:child_process"
import {
  cpSync,
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs"
import { dirname, join, relative, resolve } from "node:path"
import { beforeAll, describe, expect, test } from "vite-plus/test"
import { GENERATOR_VERSION } from "../src/embed.ts"

const ROOT = resolve(import.meta.dirname, "..")
const CLI = join(ROOT, "src/cli.ts")
const LEAN_TYPESCRIPT = join(ROOT, ".lake/build/bin/lean-typescript")
const FIXTURE = join(ROOT, "test/embed/app")
const OUT = join(ROOT, "test-out/embed")
const NODE_ONLY = join(OUT, "node-only-bin")
const TIMEOUT = 300_000

interface Run {
  readonly status: number
  readonly stdout: string
  readonly stderr: string
}

function run(cmd: string, args: readonly string[], cwd: string, env: NodeJS.ProcessEnv = {}): Run {
  const r = spawnSync(cmd, args, {
    cwd,
    encoding: "utf8",
    env: { ...process.env, LEAN_TYPESCRIPT, LEAN_TS_AUTO_SYNC: "0", ...env },
  })
  if (r.error !== undefined) throw r.error
  return { status: r.status ?? -1, stdout: r.stdout, stderr: r.stderr }
}

function leanTs(args: readonly string[], cwd: string = ROOT, env: NodeJS.ProcessEnv = {}): Run {
  return run(process.execPath, [CLI, ...args], cwd, env)
}

function copyProject(from: string, name: string): string {
  const dir = join(OUT, name)
  rmSync(dir, { recursive: true, force: true })
  cpSync(from, dir, {
    recursive: true,
    filter: (src) => !src.includes("/.lean-ts/workspace") && !src.includes("/node_modules"),
  })
  mkdirSync(join(dir, "node_modules"), { recursive: true })
  symlinkSync(relative(join(dir, "node_modules"), ROOT), join(dir, "node_modules/lean-ts"))
  symlinkSync(
    relative(join(dir, "node_modules"), join(ROOT, "node_modules/zod")),
    join(dir, "node_modules/zod"),
  )
  return dir
}

function sync(dir: string): Run {
  return leanTs(["sync", "--package", dir])
}

function nodeEval(dir: string, code: string, env: NodeJS.ProcessEnv = {}): Run {
  return run(process.execPath, ["--input-type=module", "-e", code], dir, env)
}

function edit(file: string, from: string, to: string): void {
  const text = readFileSync(file, "utf8")
  if (!text.includes(from)) throw new Error(`${file} does not contain ${from}`)
  writeFileSync(file, text.replace(from, to))
}

function generatedFiles(dir: string): Map<string, string> {
  const out = new Map<string, string>()
  const walk = (d: string): void => {
    for (const e of readdirSync(d, { withFileTypes: true })) {
      const p = join(d, e.name)
      if (e.isDirectory()) walk(p)
      else if (p.includes("/_lean/")) out.set(relative(dir, p), readFileSync(p, "utf8"))
    }
  }
  walk(join(dir, "src"))
  out.set(".lean-ts/blocks.json", readFileSync(join(dir, ".lean-ts/blocks.json"), "utf8"))
  return out
}

const SCHEMAS = `function schema(min: number) {
  const json = {
    type: "object",
    properties: { sku: { type: "string" }, qty: { type: "integer", minimum: min } },
    required: ["sku", "qty"],
    additionalProperties: false,
  }
  return {
    "~standard": {
      version: 1 as const,
      vendor: "test",
      validate: (value: unknown) => ({ value }),
      jsonSchema: { input: () => json, output: () => json },
    },
  }
}

export const LineItem = schema(1)
`

const PRICED = `import { lean } from "lean-ts"
import * as priced from "./_lean/priced.ts"
import { LineItem } from "./schemas.ts"

export const pricedBlock = lean(
  "priced",
  String.raw\`
def total (prices : List Nat) : Nat := prices.foldl (· + ·) 0
\`,
  { models: { LineItem }, output: { tagKey: "kind" } },
)

export const total: typeof priced.total = priced.total
`

let app = ""
let appSync: Run = { status: -1, stdout: "", stderr: "" }

beforeAll(() => {
  if (!existsSync(LEAN_TYPESCRIPT))
    throw new Error(`${LEAN_TYPESCRIPT} is missing; run lake build lean-typescript`)
  if (!existsSync(join(ROOT, "dist/index.js")))
    throw new Error("dist/index.js is missing; run vp pack")
  mkdirSync(OUT, { recursive: true })
  rmSync(NODE_ONLY, { recursive: true, force: true })
  mkdirSync(NODE_ONLY)
  symlinkSync(process.execPath, join(NODE_ONLY, "node"))
  app = copyProject(FIXTURE, "app")
  appSync = sync(app)
}, TIMEOUT)

describe("lean-ts sync", () => {
  test("checks the proofs and generates modules whose functions run", () => {
    expect(appSync.stderr).toContain("6 blocks of")
    expect(appSync.status).toBe(0)
    const r = run(process.execPath, ["--test", "--test-reporter=tap", "test/"], app)
    expect(r.stdout).toContain("# pass 5")
    expect(r.status).toBe(0)
  })

  test("the committed fixture is what sync generates", () => {
    expect(generatedFiles(app)).toEqual(generatedFiles(FIXTURE))
  })

  test("a block shares the types of the block it uses", () => {
    expect(
      readFileSync(join(app, ".lean-ts/workspace/LeanTsEmbed/report/report.lean"), "utf8"),
    ).toContain(
      "import LeanTsEmbed.«geometry».«geometry»\n\nnamespace LeanTsEmbed.«report».«report»\nopen LeanTsEmbed.«geometry».«geometry»\n",
    )
    expect(appSync.stderr).not.toContain("skipped LeanTsEmbed.report.report.boxArea")
    const report = readFileSync(join(app, "src/_lean/report__report.ts"), "utf8")
    expect(report).toContain('import * as $x0 from "./geometry__geometry.ts"')
    expect(report).toContain("export function boxArea(b: $x0.Box): bigint")
  })

  test("a model becomes a Lean structure whose constraints are proof fields", () => {
    const models = readFileSync(join(app, ".lean-ts/workspace/LeanTsModels/pricing.lean"), "utf8")
    expect(models).toContain(
      "structure LineItem where\n  kind : LeanTsEnums.«pricing».LineItem_kind\n  note? : Option String\n  qty : Nat\n  qty_ge : 1 ≤ qty\n",
    )
    expect(models).toContain(
      '/-- The model LineItem of src/pricing.ts. Not assumed in Lean: sku pattern "^[A-Z0-9-]+$". -/',
    )
    expect(models).toContain("structure Order where\n  buyer : String\n  item : LineItem\n")
    expect(
      readFileSync(join(app, ".lean-ts/workspace/LeanTsEmbed/pricing/pricing.lean"), "utf8"),
    ).toContain(
      "import LeanTsModels.«pricing»\n\nnamespace LeanTsEmbed.«pricing».«pricing»\nopen LeanTsModels.«pricing»\n",
    )
    const pricing = readFileSync(join(app, "src/_lean/pricing__pricing.ts"), "utf8")
    expect(pricing).toContain('import type { LineItem as $m0 } from "../pricing.ts"')
    expect(pricing).toContain(
      "export function total(items: readonly L.InferOutput<typeof $m0>[], d: Discount): bigint",
    )
  })

  test(
    "a model whose JSON Schema has no Lean form stops with 254",
    () => {
      const dir = copyProject(FIXTURE, "bad-model")
      edit(
        join(dir, "src/pricing.ts"),
        "note: z.string().optional(),",
        "note: z.union([z.string(), z.number()]),",
      )
      const r = sync(dir)
      expect(r.status).toBe(254)
      expect(r.stderr).toContain("src/pricing.ts: the model LineItem.note: the schema")
      const named = copyProject(FIXTURE, "inline-model")
      edit(
        join(named, "src/pricing.ts"),
        "{ models: { LineItem, Order },",
        "{ models: { LineItem: z.object({}) },",
      )
      const inline = sync(named)
      expect(inline.status).toBe(252)
      expect(inline.stderr).toContain(
        "the model LineItem must be an exported variable of the module",
      )
    },
    TIMEOUT,
  )

  test(
    "a wrong proof stops with 254 and the position in the TypeScript file",
    () => {
      const dir = copyProject(FIXTURE, "wrong-proof")
      const file = join(dir, "src/arith.ts")
      edit(file, "unfold double; omega", "unfold double; rfl")
      const r = sync(dir)
      expect(r.status).toBe(254)
      expect(r.stderr).toContain(
        `${file}:10:18: error: (lean block arith, Lean 5:17) Tactic \`rfl\` failed`,
      )
    },
    TIMEOUT,
  )

  test("a block with an unknown use stops with 252", () => {
    const dir = copyProject(FIXTURE, "unknown-use")
    edit(join(dir, "src/report.ts"), "./geometry.ts:geometry", "./geometry.ts:shapes")
    const r = sync(dir)
    expect(r.status).toBe(252)
    expect(r.stderr).toContain('uses "./geometry.ts:shapes", which is not a block of the package')
  })

  test("a source that is not a literal stops with 252", () => {
    const dir = copyProject(FIXTURE, "dynamic-source")
    edit(
      join(dir, "src/arith.ts"),
      'lean(\n  "arith",\n  String.raw`',
      'lean(\n  "arith",\n  String.raw`${"x"}',
    )
    const r = sync(dir)
    expect(r.status).toBe(252)
    expect(r.stderr).toContain(
      `${join(dir, "src/arith.ts")}:6:3: the Lean source of lean(...) must be a template literal`,
    )
  })

  test("an invalid output setting stops with 254", () => {
    const dir = copyProject(FIXTURE, "bad-setting")
    edit(
      join(dir, "src/arith.ts"),
      "`,\n)",
      '`,\n  { output: { tagKey: "not-an-identifier" } },\n)',
    )
    const r = sync(dir)
    expect(r.status).toBe(254)
    expect(r.stderr).toContain("tagKey must be a JavaScript identifier")
  })
})

describe("stale blocks", () => {
  test(
    "lean() throws LeanBlockStale and status lists the block without Lean",
    () => {
      const dir = copyProject(app, "stale")
      edit(join(dir, "src/arith.ts"), "xs.foldl (· + ·) 0", "xs.foldl (· + ·) 1")
      const r = nodeEval(dir, 'await import("./src/arith.ts")')
      expect(r.status).not.toBe(0)
      expect(r.stderr).toContain('LeanBlockStale: the Lean block "arith" is stale')
      const s = leanTs(["status", "--package", dir], ROOT, { PATH: NODE_ONLY })
      expect(s.stdout).toBe(
        [
          "stale   src/arith.ts:arith",
          "fresh   src/geometry.ts:geometry",
          "fresh   src/pricing.ts:pricing",
          "fresh   src/report.ts:report",
          "fresh   src/text.ts:greeting",
          "fresh   src/text.ts:words",
          "",
        ].join("\n"),
      )
      expect(s.status).toBe(254)
      expect(leanTs(["status", "--package", app], ROOT, { PATH: NODE_ONLY }).status).toBe(0)
    },
    TIMEOUT,
  )

  test(
    "LEAN_TS_AUTO_SYNC=1 runs sync and the next start uses the new module",
    () => {
      const dir = copyProject(app, "auto-sync")
      edit(join(dir, "src/arith.ts"), "xs.foldl (· + ·) 0", "xs.foldl (· + ·) 100")
      const code =
        'const a = await import("./src/_lean/arith.ts"); await import("./src/arith.ts"); console.log(String(a.sum([1n])))'
      const first = nodeEval(dir, code, { LEAN_TS_AUTO_SYNC: "1" })
      expect(first.stderr).toContain('lean-ts: regenerated the Lean block "arith"')
      expect(first.stdout).toBe("1\n")
      expect(first.status).toBe(0)
      const second = nodeEval(dir, code)
      expect(second.stdout).toBe("101\n")
      expect(second.status).toBe(0)
    },
    TIMEOUT,
  )

  test(
    "the JSON Schema of the models and the output settings are in the key",
    () => {
      const dir = copyProject(app, "models")
      writeFileSync(join(dir, "src/schemas.ts"), SCHEMAS)
      writeFileSync(join(dir, "src/priced.ts"), PRICED)
      const r = sync(dir)
      expect(r.stderr).toContain("7 blocks of")
      expect(r.status).toBe(0)
      const ok = nodeEval(
        dir,
        'const m = await import("./src/priced.ts"); console.log(String(m.total([2n, 3n])), String(m.pricedBlock.models.LineItem !== undefined))',
      )
      expect(ok.stdout).toBe("5 true\n")
      expect(ok.status).toBe(0)
      edit(join(dir, "src/schemas.ts"), "schema(1)", "schema(2)")
      expect(leanTs(["status", "--package", dir]).stdout).toContain("stale   src/priced.ts:priced")
      const stale = nodeEval(dir, 'await import("./src/priced.ts")')
      expect(stale.stderr).toContain('LeanBlockStale: the Lean block "priced" is stale')
      edit(join(dir, "src/schemas.ts"), "schema(2)", "schema(1)")
      edit(join(dir, "src/priced.ts"), 'tagKey: "kind"', 'tagKey: "type"')
      expect(leanTs(["status", "--package", dir]).stdout).toContain("stale   src/priced.ts:priced")
      edit(join(dir, "src/priced.ts"), 'tagKey: "type"', 'tagKey: "kind"')
      const pkg = join(dir, "package.json")
      expect(leanTs(["status", "--package", dir]).status).toBe(0)
      writeFileSync(
        pkg,
        JSON.stringify({
          ...JSON.parse(readFileSync(pkg, "utf8")),
          "lean-ts": { option: "undefined" },
        }),
      )
      expect(leanTs(["status", "--package", dir]).stdout).toContain("stale   src/arith.ts:arith")
      const pkgStale = nodeEval(dir, 'await import("./src/arith.ts")')
      expect(pkgStale.stderr).toContain(
        'LeanBlockStale: the Lean block "arith" is stale (the lean-ts settings of its package.json changed since `lean-ts sync` generated it)',
      )
      expect(sync(dir).status).toBe(0)
      expect(nodeEval(dir, 'await import("./src/arith.ts")').status).toBe(0)
    },
    TIMEOUT,
  )
})

describe("without Lean", () => {
  test("the committed fixture runs with node --test when lake and lean-typescript are not on PATH", () => {
    const env = { PATH: NODE_ONLY }
    for (const cmd of ["lake", "lean-typescript", "lean"]) {
      const r = spawnSync(cmd, ["--version"], { env })
      expect(r.error?.message).toContain("ENOENT")
    }
    const dir = copyProject(FIXTURE, "no-lean")
    const r = run("node", ["--test", "--test-reporter=tap", "test/"], dir, env)
    expect(r.stdout).toContain("# pass 5")
    expect(r.status).toBe(0)
  })
})

describe("lean-ts generate", () => {
  test(
    "emits a TypeScript module per module of a lake project",
    () => {
      const dir = copyProject(join(ROOT, "test/project"), "project")
      const r = leanTs(["generate", "--lake-dir", dir, "--output-dir", join(dir, "ts")])
      expect(r.status).toBe(0)
      expect(readdirSync(join(dir, "ts/Tally")).toSorted()).toEqual(["Basic.ts", "Format.ts"])
      const out = nodeEval(
        dir,
        'const f = await import("./ts/Tally/Format.ts"); const b = await import("./ts/Tally/Basic.ts"); console.log(f.Tally.report([1n, 2n]), String(b.Tally.total([4n, 5n])))',
      )
      expect(out.stdout).toBe("2 items, total 3 9\n")
      expect(out.status).toBe(0)
    },
    TIMEOUT,
  )
})

describe("versions", () => {
  test("GENERATOR_VERSION is the generatorVersion of Main.lean and of lean-typescript", () => {
    const m = /^def generatorVersion : String := "([^"]*)"$/mu.exec(
      readFileSync(join(ROOT, "Main.lean"), "utf8"),
    )
    expect(m?.[1]).toBe(GENERATOR_VERSION)
    expect(run(LEAN_TYPESCRIPT, ["--generator-version"], ROOT).stdout).toBe(
      `${GENERATOR_VERSION}\n`,
    )
  })

  test("lean-ts --version is the package version", () => {
    const pkg: unknown = JSON.parse(readFileSync(join(ROOT, "package.json"), "utf8"))
    expect(leanTs(["--version"]).stdout).toBe(`${String(Reflect.get(Object(pkg), "version"))}\n`)
  })
})

describe("cli parameters", () => {
  test("sync without --package exits with 252", () => {
    const r = leanTs(["sync"])
    expect(r.status).toBe(252)
    expect(r.stderr).toContain("--package is required")
  })

  test("lean-typescript --batch with an invalid file exits with 252", () => {
    const f = join(OUT, "bad-batch.json")
    mkdirSync(dirname(f), { recursive: true })
    writeFileSync(f, '[{"module": "X"}]')
    const r = run(LEAN_TYPESCRIPT, ["module", "generate", "--batch", f], ROOT)
    expect(r.status).toBe(252)
    expect(r.stderr).toContain("invalid --batch file")
  })
})
