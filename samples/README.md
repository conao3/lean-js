# Samples

Each sample is a package of the repository's pnpm workspace that depends on `lean-ts` through
`link:` (the packed `dist/`, so run `vp pack` first). `samples/run.sh <dir>` runs `lean-ts sync`
on it (checking the proofs and regenerating `src/_lean/`), runs `node src/main.ts` and compares
the output with `expected.txt`. The samples that verify TypeScript functions also have
`lean/Proofs/` and a committed `lean-ts.lock`; `make -C samples verify` runs
`lean-ts check --require proved` on them. `make samples` in the repository root runs both and
checks that the committed generated modules are up to date. Run them inside `nix develop` of the
repository root.

## Writing functions in Lean

| sample                           | shows                                                                                                                                                                          |
| -------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| [word-count](word-count)         | strings and lists, a structure as a result, a proof by induction                                                                                                               |
| [roman-numerals](roman-numerals) | an ordinary lake project (`lean/`) compiled with `lean-ts generate` to a committed module, a round-trip theorem checked for every number below 1000 (`decide +kernel`)         |
| [todo-cli](todo-cli)             | an invariant over a list (`∀ t ∈ items, t.id < nextId`) kept by every operation, JSON storage, tampered JSON rejected                                                          |
| [generic-search](generic-search) | polymorphic functions proved once for every type, called through monomorphic definitions (the polymorphic ones are skipped)                                                    |
| [pricing-api](pricing-api)       | Hono with a Lean structure holding a user's zod model and a Lean inductive type as request body (`@hono/standard-validator`), 400 for invalid input, OpenAPI from `jsonSchema` |

## Verifying TypeScript functions

| sample                                     | shows                                                                                                                                                                                                                |
| ------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [verified-typescript](verified-typescript) | `refines` of a `for (let i ...)` loop (`sumTo`), proved by induction over `Ts.range`, which then runs in place of the recursive spec; `ensures` of an insertion into a sorted array (`insertSorted` keeps it sorted) |
| [sorted-search](sorted-search)             | `refines` under `requires`: a scan that stops at the first larger element equals `List.contains` on sorted lists only                                                                                                |
| [inventory](inventory)                     | a block's structure and enum in the signatures, `ensures` about how `restock` and `discard` change the stock                                                                                                         |

## Steps

`steps/` introduces one feature at a time:

| step                                     | feature                                                                                    |
| ---------------------------------------- | ------------------------------------------------------------------------------------------ |
| [01-functions](steps/01-functions)       | functions on `Nat`, `String`, `Bool`                                                       |
| [02-theorems](steps/02-theorems)         | theorems next to the code                                                                  |
| [03-structures](steps/03-structures)     | structures as schemas, a proof field checked by `parse`                                    |
| [04-inductives](steps/04-inductives)     | enums, inductive types, JSON, narrowing on `ctor`                                          |
| [05-collections](steps/05-collections)   | `List`, `Array`, `Option`, loops with in-place updates                                     |
| [06-imports](steps/06-imports)           | `imports: [...]` (`Std.HashMap`)                                                           |
| [07-io](steps/07-io)                     | `IO`: file handles, environment variables, `LeanIOError`                                   |
| [08-user-schemas](steps/08-user-schemas) | `models: { ... }`: a user's zod schema in Lean, its constraints in proofs                  |
| [09-uses](steps/09-uses)                 | `uses: [...]`: types shared between blocks                                                 |
| [10-ensures](steps/10-ensures)           | `ensures`: a condition on the result of a TypeScript function                              |
| [11-requires](steps/11-requires)         | `requires`: an assumption on the arguments, a function that may fail (`Math.floor(a / b)`) |
| [12-refines](steps/12-refines)           | `refines`: equal to a spec, which then runs the TypeScript function                        |
| [13-loops](steps/13-loops)               | `for (let i ...)` and `for ... of` loops proved by induction                               |
| [14-schemas](steps/14-schemas)           | the constraints of a zod schema as assumptions of a proof                                  |
