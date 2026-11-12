<p align="center"><strong>Write and prove functions in Lean 4, run them as TypeScript</strong></p>

<p align="center">
  <a href="https://www.npmjs.com/package/lean-ts"><img src="https://img.shields.io/npm/v/lean-ts" alt="npm version"></a>
  <a href="https://github.com/conao3/lean-ts/actions/workflows/ci.yml"><img src="https://github.com/conao3/lean-ts/actions/workflows/ci.yml/badge.svg?branch=master" alt="CI"></a>
  <a href="https://github.com/conao3/lean-ts/blob/master/LICENSE"><img src="https://img.shields.io/github/license/conao3/lean-ts" alt="License: Apache-2.0"></a>
  <a href="https://github.com/conao3/lean-ts/blob/master/package.json"><img src="https://img.shields.io/badge/Node-%3E%3D22.18-blue" alt="Node >=22.18"></a>
  <a href="https://github.com/conao3/lean-ts/blob/master/lean-toolchain"><img src="https://img.shields.io/badge/Lean-v4.35.0-blue" alt="Lean v4.35.0"></a>
  <a href="https://github.com/conao3/lean-ts/stargazers"><img src="https://img.shields.io/github/stars/conao3/lean-ts?style=flat" alt="GitHub stars"></a>
</p>

<p align="center">
  <a href="#install">Install</a> ·
  <a href="#lean-blocks">Lean blocks</a> ·
  <a href="#values">Values</a> ·
  <a href="#verifying-typescript-functions">Verifying TypeScript functions</a> ·
  <a href="#examples">Examples</a> ·
  <a href="https://www.npmjs.com/package/lean-ts">npm</a>
</p>

# lean-ts

lean-ts lets you write functions in Lean 4, prove theorems about them, and call them from
TypeScript with plain values and Standard Schema types as arguments and results. The npm package
and its CLI are `lean-ts`; the Lean CLI that generates the TypeScript is `lean-typescript`.

```ts
import { lean } from "lean-ts"
import * as z from "zod"
import * as pricing from "./_lean/pricing.ts"

export const LineItem = z.object({
  sku: z.string().min(1),
  qty: z.number().int().min(1),
  unitPrice: z.number().int().min(0),
})

export const pricingBlock = lean(
  "pricing",
  String.raw`
inductive Discount where
  | none
  | percent (p : Nat) (h : p ≤ 100)
  | fixed (amount : Nat)

def subtotal (items : List LineItem) : Nat :=
  items.foldl (fun acc i => acc + i.qty * i.unitPrice) 0

def total (items : List LineItem) (d : Discount) : Nat :=
  match d with
  | .none => subtotal items
  | .percent p _ => subtotal items - subtotal items * p / 100
  | .fixed a => subtotal items - a

theorem total_le (items : List LineItem) (d : Discount) : total items d ≤ subtotal items := by
  unfold total; split <;> omega
`,
  { models: { LineItem } },
)

pricing.total([{ sku: "a", qty: 2, unitPrice: 100 }], { ctor: "percent", p: 10n }) // 180n
pricing.Discount["~standard"].validate({ percent: { p: 150 } }) // issues: Discount.percent.h: p ≤ 100
```

- `lean-ts sync` checks the proofs with Lake and compiles the Lean code from Lean's IR to typed
  TypeScript modules in `src/_lean/`, which you commit. They pass `tsc --strict` and run with the npm
  package alone, in Node (22.18 or later), Bun and browsers. You do not need Lean to run them.
- The generated TypeScript computes what the C backend computes. A diff test runs the same Lean
  programs natively and as TypeScript and compares the output byte for byte.
- Lean structures and inductive types become TypeScript types and Standard Schema values. A proof
  field (`h : p ≤ 100`) becomes a check compiled from the proposition, so every value that reaches
  Lean satisfies the invariants the proofs rely on. The JSON is the JSON of Lean's
  `deriving ToJson, FromJson`, and the schemas have a JSON Schema.
- Lean code can use your own zod, valibot or arktype schemas (`models: { ... }`). Their constraints
  (`min`, `max`, `minLength`, ...) become proof fields that Lean proofs may assume.
- `model(fn, { refines, requires, ensures })` binds a TypeScript function to Lean specifications.
  `lean-ts check` translates the function to Lean and judges your proofs
  ([Verifying TypeScript functions](#verifying-typescript-functions)).

## Install

The npm package and the Lean CLI:

```sh
pnpm add lean-ts                              # the runtime, lean(), lean-ts sync and check
nix profile install github:conao3/lean-ts     # the Lean CLI `lean-typescript` (add /vX.Y.Z for a release)
```

`lean-ts sync` also needs `lake` and the Lean toolchain of `lean-toolchain` (v4.35.0) on `PATH`.
`checkModel` needs `fast-check` (an optional peer dependency). Bun (1.4.4) turns the non-ASCII
characters of a `String.raw` template into `\u` escapes, so a block with `⟨`, `·` or `≤` is stale
there; write such blocks as plain template literals to run them with Bun.

## Lean blocks

```ts
// src/arith.ts
import { lean } from "lean-ts"
import * as arith from "./_lean/arith.ts"

export const arithBlock = lean(
  "arith",
  String.raw`
def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double; omega
`,
)

arith.double(21n) // 42n
```

```
lean-ts sync --package <dir> [--lean-typescript <path>]
lean-ts status --package <dir>
lean-ts generate --lake-dir <dir> --output-dir <dir> [--modules <Name> ...]
```

- `lean-ts sync` reads the `lean(...)` calls of `<dir>/src/**/*.ts` with oxc-parser
  (the name is a string literal, the source a template literal or `String.raw`, the
  options `imports`, `uses`, `models` and `output` an object literal), writes each
  block to `.lean-ts/workspace/LeanTsEmbed/<module>/<name>.lean`, builds it with Lake
  and generates `_lean/<module>__<name>.ts` next to the module (and `_lean/<module>.ts`
  when the module has one block) and `.lean-ts/blocks.json`. A Lean error is reported
  at the line of the TypeScript file with exit code 254.
- `uses: ["./geometry.ts:geometry"]` imports and opens another block of the package;
  the generated module imports the types and schemas of that block's module.
- `models: { LineItem }` takes the user's Standard JSON Schema values (zod, valibot,
  arktype): `sync` imports the module, reads `~standard.jsonSchema.output({ target:
  "draft-2020-12" })` and writes a Lean structure `LeanTsModels.<module>.LineItem`
  (opened in the block). `integer` is `Nat` when its minimum is at least 0 and `Int`
  otherwise, `number` `Float`, `array` `List`, a property that is not required an
  `x? : Option α` field, a string `enum` an inductive type in `LeanTsEnums.<module>`, an
  object equal to another model that model; `minimum`, `maximum`, the exclusive
  bounds, `minLength`, `maxLength`, `minItems` and `maxItems` become proof fields
  (`qty_ge : 1 ≤ qty`) the Lean proofs can assume, and `pattern`, `format`,
  `multipleOf` are listed in the structure's docstring as not assumed. Other JSON
  Schema stops `sync` with 254 and the model and property. A model must be an
  exported variable, a named import or a property of a namespace import: the
  functions take and return `StandardSchemaV1.InferOutput<typeof LineItem>` (a
  type-only import), run the model's `~standard.validate` on the arguments and return
  plain objects.
- `output: { tagKey, option }` of a block and the `"lean-ts"` field of `package.json`
  (`{ "lean-ts": { "tagKey": "kind", "option": "undefined" } }`, overridden by the
  block) are the generation settings; a block and the blocks it uses must have the
  same settings.
- A generated module registers its block and its settings when imported;
  `lean(...)` throws `LeanBlockStale` when no registered module was generated from the
  same name, source, options, model JSON Schemas and generator version, or (in Node,
  where it reads the `package.json` above the generated module) with the current
  settings. With `LEAN_TS_AUTO_SYNC=1` it runs
  `lean-ts sync` instead, and the regenerated module is used from the next start.
- `lean-ts status` compares the keys (which also cover the module path and the
  `"lean-ts"` field of `package.json`) with `.lean-ts/blocks.json` without Lean and
  exits with 254 when a block is stale.
- Commit `_lean/` and `.lean-ts/blocks.json`; ignore `.lean-ts/workspace/`. The
  package then runs without Lean.

## Values

| Lean                                | TypeScript                                                                     |
| ----------------------------------- | ------------------------------------------------------------------------------ |
| `Nat`, `Int`                        | `bigint` (arguments also take a safe-integer `number`)                         |
| `UInt8`..`UInt32`, `Int8`..`Int32`  | `number`                                                                       |
| `UInt64`, `USize`, `Int64`, `ISize` | `bigint`                                                                       |
| `Bool`                              | `boolean`                                                                      |
| `Char`                              | `string` of one code point                                                     |
| `String`                            | `string`                                                                       |
| `Float`, `Float32`                  | `number`                                                                       |
| `Unit`                              | `void` / `undefined`                                                           |
| `Option α`                          | `α \| null`, or `α \| undefined` with `--option undefined`                     |
| `List α`, `Array α`                 | `readonly α[]` (arguments), `α[]` (results)                                    |
| `α × β`                             | `readonly [α, β]`                                                              |
| `Except ε α`                        | `{ ok: true; value: α } \| { ok: false; error: ε }`                            |
| `IO α`                              | `α`; an `IO.Error` is thrown as `LeanIOError` (`code` is the constructor name) |
| `Fin n`                             | `number` (`bigint` when `n > 2^32`)                                            |
| structures                          | plain objects (`{ readonly lo: bigint; readonly hi: bigint }`)                 |
| enumerations                        | string literal unions (`"red" \| "green"`)                                     |
| other inductive types               | unions on the `--tag-key` (`{ ctor: "percent"; p: bigint } \| ...`)            |
| `{x : α // p x}`                    | `α`, checked by `p`                                                            |

Arguments are checked while they are converted: a value that does not fit throws
`LeanValidationError`, whose `issues` (`{ message, path }`) name every place that
does not fit. A definition without arguments becomes a function evaluated on the
first call. Names are the Lean names under `--namespace` (default: the module) in
lowerCamelCase (`?` → `Q`, `!` → `Bang`, `'` → `Prime`); a name with more components
is a member of a namespace object (`Calc.add` is `export const Calc = { add }`).

### Structures, inductive types and Standard Schema

```lean
structure Range where
  lo : Nat
  hi : Nat
  ok : lo ≤ hi

inductive Discount where
  | none
  | percent (p : Nat) (h : p ≤ 100)
  | fixed (amount : Nat)
```

```ts
export type Range = { readonly lo: bigint; readonly hi: bigint }
export type RangeInput = {
  readonly lo: bigint | number | string
  readonly hi: bigint | number | string
}
export const Range: L.LeanSchema<RangeInput, Range> = L.schema<RangeInput, Range>($tRange)

Range["~standard"].validate({ lo: 3, hi: 1 }) // { issues: [{ message: "Range.ok: lo ≤ hi", path: [] }] }
Discount["~standard"].validate({ percent: { p: 10 } }) // { value: { ctor: "percent", p: 10n } }
```

- Every type is a `LeanSchema<Input, Output>`: a `StandardSchemaV1` and
  `StandardJSONSchemaV1` (`@standard-schema/spec` 1.1.0, vendor `lean-ts`) with the
  descriptor in `desc`. Hono's `sValidator("json", Range)`, tRPC, TanStack Form and
  zod's `z.custom` take it as it is. `Input` is the JSON of Lean's
  `deriving ToJson`: a structure is an object (the fields of a parent flat, an `x?`
  field omitted when `none`), a constructor without arguments is `"none"`, named
  arguments are `{ "percent": { "p": 10 } }`, one unnamed argument `{ "tag": v }`, several
  `{ "pair": [a, b] }`, `UInt64`/`USize` are strings. `validate` takes the JSON and the
  TypeScript form and returns the TypeScript form; it is synchronous.
- A proof field (`ok : lo ≤ hi`) or the property of a subtype is checked by the
  decision procedure Lean compiles from the proposition (`LeanTsGen.Range.mk.ok_decide`),
  both in `validate` and in the arguments of the public functions, so the values that
  reach Lean satisfy the propositions. A comparison with a constant is also in the
  JSON Schema (`maximum`, `exclusiveMinimum`, `maxLength`, `maxItems`, ...).
- `jsonSchema.input` and `.output` take `draft-2020-12`, `draft-07` and `openapi-3.0`;
  recursive types use `$defs`/`definitions`.
- `lean-ts/schema` has the scalar schemas (`Nat`, `Int`, `UInt8`.., `String`, `Float`,
  ...), `toJSON` (safe integers as numbers, the others as strings), `fromJSON`,
  `stringify` (`bigint` as JSON numbers) and `parse` (integer literals read without
  loss through the `JSON.parse` reviver's source text).
- A structure with type parameters is a type per instance (`Pair Nat Bool` is
  `PairNatBool`). A namespace of functions named as a type is merged into its schema
  (`Point.sum` is a member of the schema `Point`).
- The generation settings change the TypeScript form only:

  | setting  | values                    | default  | effect                                                                       |
  | -------- | ------------------------- | -------- | ---------------------------------------------------------------------------- |
  | `tagKey` | a JavaScript identifier   | `"ctor"` | the discriminant of the inductive types (`{ kind: "percent"; p: bigint }`)   |
  | `option` | `"null"` or `"undefined"` | `"null"` | `Option α` is `α \| null`, or `α \| undefined` and an optional field `x?: α` |

## Verifying TypeScript functions

```ts
// src/calc.ts
import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/calc.ts"

export const specBlock = lean(
  "spec",
  String.raw`
def clampSpec (x lo hi : Int) : Int := max lo (min hi x)
def ordered (_x lo hi : Int) : Bool := lo ≤ hi
def inRange (_x lo hi : Int) (r : Int) : Bool := lo ≤ r && r ≤ hi
`,
)

export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo
  if (x > hi) return hi
  return x
}

model(clamp, {
  refines: spec.clampSpec,
  requires: spec.ordered,
  ensures: { inRange: spec.inRange },
})
```

```lean
-- lean/Proofs/Calc.lean (next to package.json)
import LeanTsModel.calc

namespace LeanTsModel.calc

theorem clamp.proof.refines : clamp.obligation.refines := by
  intro x lo hi h
  simp only [LeanTsEmbed.calc.spec.ordered, decide_eq_true_eq] at h
  simp only [clamp, LeanTsEmbed.calc.spec.clampSpec]
  split <;> (try split) <;> simp_all <;> omega
```

```
lean-ts check --package <dir> [--lean-typescript <path>] [--require proved]
lean-ts status --package <dir>
```

- `model(fn, { refines?, requires?, ensures? })` (`lean-ts/verify`) returns the function
  and records it; the specifications are public functions of `lean(...)` blocks (each
  generated function carries its Lean name as `__leanName`).
- `lean-ts check` syncs the package, reads the `model(...)` calls with oxc-parser,
  translates each function (a `function` declaration or a `const` arrow function) into
  `LeanTsModel.<module>.<function>` in Lean `do` notation over `LeanTsLib.Ts`
  (`src/lean/LeanTsLib/Ts.lean`), states `<function>.obligation.refines`
  (`∀ x, requires x = true → f x = s x`, `= Except.ok (s x)` for a function that may
  throw), `.obligation.<label>` for each `ensures` (partial correctness for a function
  that may throw) and `.obligation.returnsNat` for a function returning `Nat`, builds
  the proofs of `<dir>/lean/Proofs/` one file at a time and prints each obligation as
  `proved`, `sorry`, `axioms` (an axiom outside `propext`, `Quot.sound`,
  `Classical.choice`), `failed` (its proof file does not build), `missing` or
  `mismatch` (the theorem's type is not the obligation). It writes
  `<dir>/lean-ts.lock` (with a `spec_hash` of each function's AST without positions
  and of the keys of its specification blocks); `--require proved` exits with 254
  unless every obligation is proved. A construct outside the subset stops `check` with
  254 and the file, line and column. Commit `lean-ts.lock` with `_lean/`; `status` and the
  replaced specifications read it.
- `lean-ts status` also prints the obligations of the lock and marks a function whose
  hash changed `stale` (exit code 254) without Lean.
- The subset: parameters and results annotated with `number`, `bigint`, `boolean`,
  `string`, `T[]`, `readonly T[]`, `[A, B]`, `T | null`, `T | undefined`, `Nat` and `Int`
  of `lean-ts/schema`, the structures, inductive types and enums generated from a block
  and `z.infer<typeof X>` (any type taking `typeof X`) of a model `X` of a block;
  `const`/`let` and reassignment, compound assignment, `++`, `if`, `switch` on a string,
  an enum or the tag of an inductive value, early `return`, `for ... of`,
  `for (let i = a; i < b; i++)`, `while`, `break`, `continue`, `throw new Error(...)`
  (and the built-in errors), `push` to a local array, destructuring of tuples and
  structures; `+ - * %`, `Math.floor(a / b)`, `Math.trunc(a / b)`, bigint `/`,
  comparisons, `===`, `!==`, `&&`, `||`, `!`, `??`, `?:`, `xs[i]`, `xs[i]!`, `.length`,
  tuple indices, properties, object and array literals, `map`, `filter`, `reduce`,
  `some`, `every`, `includes`, `startsWith`, `endsWith`, template literals,
  `Math.max`/`min`/`abs`, `BigInt`, `Number`, `String` and calls of the module's model
  functions. A `x === null` test on a parameter narrows it as in TypeScript.
- Loops: `for (const x of xs)` is `for x in xs` over the list, which `simp` turns into
  `List.foldl` when the body only updates variables; a body with an early `return` or a `push`
  under `if` is proved by induction on the list (the `forIn` equations of `List.cons`).
  `for (let i = a; i < b; i++)` iterates `Ts.range a b`, and `Ts.range_succ` splits off the
  last index for an induction on the bound (`sumTo` in `samples/verified-typescript`). A
  `while` loop is Lean's partial `Loop` and cannot be unfolded in a proof.
- `checkModel(fn, { numRuns?, seed?, range? })` runs the specifications as a fast-check
  property test (fast-check is an optional peer dependency): it reads the parameter
  types from the source of the `model(...)` call, discards arguments that fail
  `requires` and results that are not safe integers, and throws `PropertyFailure` with
  the counterexample. `checkModule(m)` runs it for every model function of a module.
  `arbitrary(schema, fc)` of `lean-ts/schema` generates the values of a descriptor.
- A proved `refines` without `requires` replaces the specification: the lock records
  it, `sync` writes `LeanTsCsimp/<module>.lean` (`@[extern "ts:src/calc.ts#addOne(n)"]
  def addOne := @spec.succ` and an `rfl` `@[csimp]` theorem), and the emitter makes the
  public function of the specification and every Lean function of the block that calls
  it call the TypeScript function (the arguments pass through `toTs`, and `tsNumbers`
  for `number` parameters, the result through `toLean`). The generated module then
  imports the user's module; it registers its block in `<module>__<name>.block.ts`
  first so that either module can be imported first.
- The proofs hold for the translation of the function and assume that `number`
  arguments and intermediate values are safe integers (`bigint` needs no assumption),
  that the arguments have their annotated types (`tsc --strict`, `validate` at the
  boundary), and that the translation and `LeanTsLib.Ts` keep the meaning of
  TypeScript, which `checkModel` and `test/verify/ts-model.test.ts` test.

## Examples

[`samples/`](https://github.com/conao3/lean-ts/tree/master/samples) holds packages with Lean blocks
and verified TypeScript functions. `make samples` syncs each one, runs it, compares the output with
its `expected.txt`, checks the proofs of the verified ones with `lean-ts check --require proved`,
and fails when a committed generated module is out of date.

| sample                                                                                           | shows                                                                                                                      |
| ------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- |
| [word-count](https://github.com/conao3/lean-ts/tree/master/samples/word-count)                   | strings and lists, a proof by induction                                                                                    |
| [roman-numerals](https://github.com/conao3/lean-ts/tree/master/samples/roman-numerals)           | a lake project compiled with `lean-ts generate`, a round-trip theorem checked for every number below 1000                  |
| [todo-cli](https://github.com/conao3/lean-ts/tree/master/samples/todo-cli)                       | an invariant over a list kept by every operation, JSON storage, tampered JSON rejected                                     |
| [generic-search](https://github.com/conao3/lean-ts/tree/master/samples/generic-search)           | polymorphic functions proved for every type, called through monomorphic definitions                                        |
| [pricing-api](https://github.com/conao3/lean-ts/tree/master/samples/pricing-api)                 | Hono with a zod model and a Lean inductive type as request body, 400 for invalid input, OpenAPI                            |
| [verified-typescript](https://github.com/conao3/lean-ts/tree/master/samples/verified-typescript) | a `for (let i ...)` loop proved equal to a recursive spec, which it then replaces; an insertion that keeps an array sorted |
| [sorted-search](https://github.com/conao3/lean-ts/tree/master/samples/sorted-search)             | `refines` under `requires` (a scan of a sorted array)                                                                      |
| [inventory](https://github.com/conao3/lean-ts/tree/master/samples/inventory)                     | a block's structure and enum in the signatures of verified functions                                                       |

[`samples/steps/`](https://github.com/conao3/lean-ts/tree/master/samples/steps) introduces one
feature at a time, from functions on `Nat` (01) to types shared between blocks with `uses` (09)
and the verification of TypeScript functions (10 to 14).

## The CLI

```
lean-typescript module generate --module-name Foo.Bar [--roots <Name> ...] [--main <Name>]
  [--namespace <Name>] [--import <Name> ...] [--search-path <dir> ...] [--output-file <path>]
  [--runtime-path <specifier>] [--type-module <Name>=<specifier> ...] [--model-module <Name>=<key> ...]
  [--tag-key <key>] [--option null|undefined] [--ts-root <specifier>] [--batch <file>]
  [--internal-only] [--output json|text]
lean-typescript project generate --lake-dir <dir> --output-dir <dir> [--modules <Name> ...]
lean-typescript obligations check --modules <Name> ... --obligations <file> [--search-path <dir> ...]
lean-typescript help | --version | --generator-version
```

The roots default to the module's public definitions with IR. Each root becomes a
public function that takes and returns TypeScript values; the internal functions it
calls are not exported. `--internal-only` exports the internal functions instead
(the diff-test calls them with runtime values). `--main` also emits the module's
`@[init]` chain and a call running the given function as `main`. A root whose type
cannot cross the boundary (type parameters, instance or proof arguments, function
values, nested `Option`, types without a Lean form such as a proposition without
`Decidable`) is listed in the summary's `skipped` with the reason. The structures and
inductive types of the module (and those the public functions use) are exported as
types and schemas (summary `types`). Exit codes: 0 success, 252 invalid parameters,
254 input that cannot be converted (an extern the runtime does not provide, a name
without IR, a constructor field named as the `--tag-key`, an invalid `--tag-key` or
`--option`), 255 other errors. `--batch` runs a JSON array of jobs against one environment (`lean-ts sync`
uses it); `project generate` builds a lake project and writes `<A>/<B>.ts` per module
`A.B`.

```ts
// Generated by lean-typescript (generator 4) from LeanTsTest.Public. Do not edit.
import * as L from "lean-ts/runtime"
import type { Obj } from "lean-ts/runtime"

function l_LeanTsTest_Public_double(x_1: Obj): Obj {
  const x_2: Obj = L.lean_nat_add(x_1, x_1)
  return x_2
}

const $d0: L.TypeDesc<bigint> = L.natDesc

/** Lean `LeanTsTest.Public.double : Nat → Nat`. */
export function double(n: bigint | number): bigint {
  return L.toTs($d0, l_LeanTsTest_Public_double(L.toLean($d0, n, "n")))
}
```

## Layout

- `LeanTs/EmitTs.lean` — the emitter: IR walk, transitive decl collection, extern
  mapping, trampoline TCO, typed TypeScript output.
- `LeanTs/Marshal.lean` — the TypeScript types and descriptors of the Lean types at the
  boundary (structures, inductive types and subtypes with their constructor layouts and
  the deciders compiled from their proof fields) and the signatures of the public
  functions; `LeanTs/Generate.lean` — the type aliases, descriptors and schemas, the
  public functions, namespace objects and the skipped roots.
- `LeanTs/RuntimeExterns.lean` — the runtime functions the generated code may call
  (generated from `src/runtime` by `make gen-externs`).
- `LeanTs/Check.lean` — `obligations check`: the state of each obligation from the type and the axioms of its proof.
- `Main.lean` — the CLI `lean-typescript`.
- `src/verify/` — `lean-ts/verify` (`model`, `checkModel`, `checkModule`), the translation of TypeScript functions to Lean (`translate.ts`) and `lean-ts check` and `status` with `lean-ts.lock` (`check.ts`); `src/lean/LeanTsLib/Ts.lean` — the meaning of the TypeScript operations; `src/schema/arbitrary.ts` — fast-check arbitraries of the descriptors.
- `src/index.ts`, `src/embed.ts` — `lean(...)`, `LeanBlockStale` and the block keys;
  `src/scan.ts`, `src/sync.ts`, `src/cli.ts` — the CLI `lean-ts` (`sync`, `status`,
  `generate`); `src/runtime/block.ts` — the registry the generated modules register in;
  `src/models.ts` — the Lean structures of the user's models (`lean(..., { models })`).
- `src/schema/` — `lean-ts/schema`: `LeanSchema` (Standard Schema and Standard JSON
  Schema), the scalar schemas, `toJSON`, `fromJSON`, `stringify`, `parse` and the JSON
  Schema of a descriptor (`desc.ts`).
- `src/runtime/` — the runtime (npm package `lean-ts`, export `./runtime`):
  `object.ts` (the `Obj` type, constructors, closures, `lean_apply`,
  `lean_trampoline`), `nat.ts`/`int.ts`/`uint.ts`/`float.ts` (numeric tower),
  `string.ts`, `array.ts` (Array, ByteArray, FloatArray), `io.ts` (`IO.Error`,
  streams, panic, init chain, `main`), `marshal.ts` (the boundary: `TypeDesc`,
  `toLean`, `toTs`, the validation of `validate`, `LeanValidationError`, `LeanIOError`), `node.ts` (the Node platform),
  `index.ts` (re-exports; installs the Node platform when `process.getBuiltinModule`
  exists, otherwise OS operations return `IO.Error.unsupportedOperation`).
- `LeanTsTest/` — the diff-test programs (`Vectors`, `HigherOrder`, `Io`, `Init`,
  `Stress`..`Stress4`, `Verify`, `Fuzz`) and their native oracles (`*Main.lean`,
  executables `oracle-*`), `Public` (called through the public functions) and `Json`
  (values with `deriving ToJson, FromJson`; `oracle-json` prints their JSON).
- `test/difftest/` — node harnesses for the function-level diff, fuzz, deep TCO and
  the 32-bit profile; `test/*.test.ts` — Vitest tests of the runtime and of the
  public functions and schemas with both generation settings (`test/public.test.ts`),
  the JSON against Lean's `ToJson` (`test/json.test.ts`), Standard Schema with Hono and
  zod (`test/standard.test.ts`); `test/embed.test.ts` — `lean-ts sync`,
  `status` and `generate` on the fixtures `test/embed/app/` (with its committed
  `src/_lean/` and `.lean-ts/blocks.json`) and `test/project/`.
- `samples/` — the samples (pnpm workspace packages that link `lean-ts`), `samples/run.sh` and
  `samples/Makefile` (`test`, `verify`).
- `scripts/bump-version.sh` — sets the version of `package.json`, `Main.lean` and `flake.nix`;
  the `Release` workflow runs it, tags `vX.Y.Z` and starts the `Publish` workflow, which packs and
  publishes the tag to npm with trusted publishing.

## How it works

1. Target functions are defined in library modules so their IR is persisted in the
   `.olean` and visible to `Lean.IR.findEnvDecl`.
2. From the roots, `LeanTs.collectTransitive` does a worklist DFS over
   `findEnvDecl`, walking `fap`/`pap` callees; `.fdecl` are emitted as TS functions,
   `.extern` map to runtime functions by their C symbol, `none` (e.g. `Nat.rec`) is
   the boundary. Functions nothing references are not emitted.
3. The emitter walks `FnBody` / `Expr`, mirroring `EmitC`'s match arms. Parameters
   and `const`s are typed from the IR types (`object`/`tobject`/erased → `Obj`,
   `uint8`..`uint32`/`float`/`float32` → `number`, `uint64`/`usize` → `bigint`),
   and only bindings the code reads are emitted.

### GC target

The JS engine has a tracing GC, so all Lean reference-counting nodes are no-ops:

- `FnBody.inc` / `dec` / `del` -> emit nothing
- `Expr.reset` -> `null` (unused reuse token)
- `Expr.reuse` -> a fresh ctor allocation (== `Expr.ctor`)
- `Expr.box` -> identity; `Expr.unbox` -> `L.lean_unbox` (a checked narrowing)
- `Expr.isShared` -> `1` ("always shared"), forcing the compiler's
  exclusivity branch to take the copying path; in-place `set`/`reuse` would corrupt
  shared JS references since there is no refcount.

### Object / value model

- `Nat` / `Int` / `UInt64` / `USize` / `Int64` / `ISize` -> `bigint`;
  `UInt8`/`UInt16`/`UInt32`/`Int8`/`Int16`/`Int32`/`Float`/`Float32`/`Char` -> JS
  number (the signed ones hold the unsigned bit pattern, as `lean.h` does).
- ctor with fields -> `L.lean_ctor(cidx, size, usize, ssize, ...objs)` producing
  `{ tag, fields, sdata }`: object pointers and `USize` slots are word-indexed in
  `fields` (proj/uproj/set/uset), packed scalars live in a byte-addressed `DataView`
  `sdata` (sproj/sset), mirroring `lean_alloc_ctor`'s three regions. Nullary ctor /
  enum -> `cidx`. `lean_tag(x)` recovers the tag for both forms.
- `Bool` -> scalar `0`/`1`; extern `decEq`/`decLt`/`decLe` return `0`/`1` so the
  emitted `switch` matches.
- `String` -> JS string; `String.Pos` is a UTF-8 byte offset (`get`/`next`/`prev`/
  `extract`/`atEnd` index bytes, `utf8ByteSize` counts bytes, `length` counts code
  points).
- `Array` -> JS array; setters (`set`/`uset`/`push`/`pop`/`swap`) return a fresh
  array so the compiler's assumed-unique in-place paths cannot corrupt aliases.
- `case` on scalar -> `switch (x)`; on object -> `switch (L.lean_tag(x))`.
- self-tail-recursion -> `for (;;)` loop with staged param rebind + `continue`
  (join points are inlined at each jump, so `continue` stays lexically inside the loop).

## Checks

```
nix develop -c make check
```

`make check` runs `treefmt --ci`, `./test-diff.sh` (generates the `LeanTsTest`
modules into `test-out/` and diffs them against the native oracles), `./test-public.sh`
(generates `test-out/public.ts` with the default settings, `test-out/public-alt.ts`
with `--tag-key _tag --option undefined` and `test-out/json.ts`, and runs
`test/public.test.ts` and `test/json.test.ts` against `oracle-json`), `./fuzz.sh`,
the type check of every generated module (`vp lint test-out/**/*.ts`), `lean-ts
status` of the embedding and verification fixtures, `test/verify/test.sh` (copies
`test/verify/app/` to `test-out/verify/<scene>/` and checks the states proved, sorry,
axioms, missing, mismatch, failed and stale, `--require proved`, the TypeScript functions
called through their specifications, an untranslatable function and a wrong
implementation that `checkModel` rejects with a counterexample), `make samples` (`lean-ts check
--require proved` on the verified samples, `samples/run.sh` on every sample, and no difference in
the committed generated modules), and `vp run check` (`vp check && vp test`, which
includes `test/embed.test.ts`). `test-diff.sh` covers: 136 function-level
value assertions (numeric tower, UTF-8 `String` and its order, `Array`/`List`, packed ctors, a
`TodoList` sequence, closures); deep TCO (incl. closure-boundary tail `.ap`) at
N=1e6; a 32-bit `USize` profile; the fail-loud extern link check; runnable IO /
stdin / error / panic / module-init programs; four `stress` programs
(parser/sort/HashMap/TreeMap/numeric/monadic; ByteArray+UTF-8 + derived `Repr` +
`a[i]!`; HashMap/HashSet order; FloatArray + dbgTrace); and a verifier-authored
`verify` program (JSON printer, RLE, matrix multiply exercising borrowed `a[i]!`
indexing, HashMap Dijkstra). Every program must match the native binary in stdout,
stderr and exit code.

## Parity vs the C backend

The oracle for every diff-test is the **native C-compiled Lean binary** (each test
program built through `lake build` → `leanc`), not `lean --run` (the interpreter
shares the same naive stack behaviour as JS and would mask divergences). Every claim
below is enforced by `test-diff.sh` diffing node output against that native binary.

### Covered and native-verified

- **Object / value model**: constructor three-region layout (pointer/USize words +
  packed-scalar `DataView`), nullary-ctor/enum lowering, `case`/`switch` tagging.
- **Numeric tower**: `Nat`/`Int` bignum (`bigint`, Euclidean div/mod), `UInt8/16/32/64`,
  `USize`, `Float`/`Float32` (IEEE add/sub/mul/div/sqrt/cmp bit-exact; transcendentals
  within ≤1 ULP, compared via the C `%f` 6-digit `toString`), signed fixed-width
  `Int8..Int64`/`ISize` (unsigned storage + `asIntN` recovery, as in EmitC).
- **String**: UTF-8 byte-positioned `String.Pos`, get/next/prev/extract/atEnd/posOf,
  `length` (code points) vs `utf8ByteSize` (bytes), `String.hash` (MurmurHash64A,
  seed 11 — bit-identical so `Std.HashMap String _` iteration order matches native).
- **Collections**: `Array`/`List` operations (setters return a fresh array — the
  compiler's assumed-unique in-place paths cannot corrupt JS aliases), `ByteArray`
  (`Uint8Array`), **`FloatArray`** (`Float64Array`: push/get!/set!/get/uget/fold/toList
  with native OOB conventions — `get!`→`0.0`, `set!`→unchanged), `Std.HashMap`/
  `HashSet` with native-matching bucket-order iteration.
- **Owned/borrowed externs**: Lean 4.35.0 emits four borrowed `@[extern]`
  variants — three for array element access (`lean_array_get_borrowed`,
  `lean_array_fget_borrowed`, `lean_array_uget_borrowed`) and `lean_panic_fn_borrowed`
  (`panicCore`, borrowed default). All four are mapped as runtime aliases of their
  owned twins, because the only C-level difference is a refcount `inc`, which is a
  no-op under JS GC. So `a[i]!` and borrowed
  indexing/projection work **uniformly** (verified by the matrix-multiply inner loop
  in the `verify` diff-test, which lowers to `lean_array_get_borrowed`).
- **Control flow**: self- and mutual-recursion plus non-cyclic tail chains are loop-ified
  through a unified trampoline (`__tc` cores returning `tc` thunks); join points are inlined so
  `continue` stays lexically valid.
- **IO**: stdout/stderr/stdin (real fd, sync read), `IO.Error` formatting + entry-point
  `uncaught exception:` reporting, `@[init]`/`initialize` module-init chain, `panic!`
  semantics (print to stderr, return the `Inhabited` default, continue), `dbgTrace`/
  `dbgTraceIfShared`/`dbgSleep`.

### Where lean-ts is _more_ robust than the C backend

- **Closure-boundary TCO.** The native C backend does not TCO tail calls that cross a
  closure application (CPS/continuation loops), so programs like `cpsCount`/`cpsSum`
  abort with `Stack overflow detected` around N≈1e5. lean-ts lowers tail `.ap` to an
  apply-thunk and runs them in constant JS stack. The diff-tests therefore check value
  equality at a native-safe N, and the no-overflow property at N=1e6 on the node side only.

### Fail-loud invariant

Any extern the runtime does not provide is a **hard generation error** (exit 254,
no output written) — never a silent wrong answer or a dangling runtime call. The
error names the exact missing C symbols so they can be implemented and retried. The
CLI checks the symbols against `LeanTs/RuntimeExterns.lean`, which `make gen-externs`
generates from the runtime's exports. `test-diff.sh` asserts an unmapped extern
(`lean_io_get_random_bytes`) is rejected while a mapped root generates.

### Out of scope (intentionally left fail-loud) and why

These cannot be matched byte-for-byte against the native oracle, so mapping them would
trade an honest hard error for a silent divergence:

- **Task / `IO.asTask` / `IO.Promise` concurrency** (`lean_task_*`, `lean_io_*_task`,
  `lean_io_promise_*`): native runs a real OS thread pool with genuine parallelism and
  scheduler-dependent interleaving/`waitAny`/cancellation timing; Node is single-threaded,
  so any emulation observes a _different_ ordering wherever ordering is observable.
- **Filesystem metadata / enumeration** (`lean_io_metadata`, `lean_io_symlink_metadata`,
  `lean_io_read_dir`, `lean_io_realpath`): `accessed`/`modified` timestamps, `numLinks`,
  directory order and symlink canonicalization are host/OS state, not program state, so
  they vary between runs and machines.
- **`IO.getRandomBytes`** (`lean_io_get_random_bytes`): by definition nondeterministic
  CSPRNG output; can never equal a fixed oracle run (used as the negative-test sentinel).
- **Raw-mode interactive TTY** (`lean_io_prim_handle_is_tty` and termios raw mode):
  depends on a live terminal device and real-time keystrokes; there is no reproducible
  input stream to diff. (Pipe/redirect/file stdin is supported and tested.)
- **Unsafe pointer identity** (`ptrAddrUnsafe`/`isExclusiveUnsafe`/`ptrEq` used to _distinguish_
  defeq values): real addresses are nondeterministic. The **safe** wrappers (`withPtrAddr`/
  `withPtrEq`/`withPtrEqDecEq`) are proven address-independent and are pure Lean (they do
  not even reach the extern), so they are faithful; the raw `lean_ptr_addr`/
  `lean_is_exclusive_obj` are mapped to address-independent constants (`0n` / non-exclusive)
  for the safe surface only.

## Remaining honest gaps vs EmitC

- The closure-boundary TCO divergence above is the one place lean-ts and native cannot
  agree at large N (lean-ts is the more robust side); value equality holds at native-safe N.
- `Float32` transcendentals use double-precision `Math.*` narrowed via `Math.fround`,
  whose rounding path differs from single-precision libm (`sinf`), so they can differ by
  more than 1 ULP at f32; the `%f` 6-digit `toString` comparison absorbs this but direct
  bit comparison is not claimed. `Float.scaleb` uses a `Math.pow(2,e)` approximation
  untested at extreme exponents.
- The 32-bit `USize` profile is covered by a literal-comparison test only (a 64-bit host
  cannot produce a native 32-bit reference); the default 64-bit profile is native-verified.

## License

Apache-2.0. See [LICENSE](LICENSE).
