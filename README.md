# lean-js (proof of concept)

A Lean-to-TypeScript backend that mirrors Lean's C backend (`Lean.Compiler.IR.EmitC`),
driven by `Lean.Compiler.IR`. From the IR `Decl` of a Lean function it transitively
collects every IR dependency, emits an equivalent self-contained TypeScript module,
then diff-tests it against Lean's own execution.

## Layout

- `LeanJs/EmitJS.lean` — the emitter library (`lean_lib LeanJs`): IR walk, transitive
  decl collection, self-tail-call loop lowering, extern mapping.
- `LeanJs/Demo.lean`   — demo target functions (double / mkShifted / sumTo / fact).
- `Main.lean`          — thin CLI (`lean_exe lean-js`): imports targets, collects from
  root names, writes `prelude.ts` + generated code to `out.ts`.
- `prelude.ts`         — hand-written runtime (Nat/Int/String/Array/List/Bool/Char).
- `expected.lean`      — Lean reference execution.
- `test.mjs` / `test.sh` — diff-test harness (Lean `#eval` vs `node`).

## How it works

1. Target functions are defined in library modules so their IR is persisted in the
   `.olean` and visible to `Lean.IR.findEnvDecl`.
2. From a set of root names, `LeanJs.collectTransitive` does a worklist DFS over
   `findEnvDecl`, walking `fap`/`pap` callees; `.fdecl` are emitted as TS functions,
   `.extern` map to the prelude, `none` (e.g. `Nat.rec`) is the boundary. Output is
   ordered callee-before-caller.
3. The emitter walks `FnBody` / `Expr`, mirroring `EmitC`'s match arms.

### GC target

The JS engine has a tracing GC, so all Lean reference-counting nodes are no-ops:

- `FnBody.inc` / `dec` / `del`  -> emit nothing
- `Expr.reset`                  -> `null` (unused reuse token)
- `Expr.reuse`                  -> a fresh ctor allocation (== `Expr.ctor`)
- `Expr.box` / `unbox`          -> identity
- `Expr.isShared`               -> `1` ("always shared"), forcing the compiler's
  exclusivity branch to take the copying path; in-place `set`/`reuse` would corrupt
  shared JS references since there is no refcount.

### Object / value model

- `Nat` / `Int` / `UInt64` / `USize` -> `bigint`; `u8`/`u16`/`u32`/`Float`/`Float32`
  -> plain JS number (matching scalar literal emission and `switch`).
- ctor with fields -> `lean_ctor(cidx, size, usize, ssize, ...objs)` producing
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
- `case` on scalar -> `switch (x)`; on object -> `switch (lean_tag(x))`.
- self-tail-recursion -> `while (true)` loop with staged param rebind + `continue`
  (join points inlined so `continue` stays lexically inside the loop).

## Run the diff-test

```
nix develop . --command bash -c "./test.sh"
```

Covers `double`, `mkShifted`, `sumTo` (incl. `100000`, exercising TCO), `fact`; a
`Mixed` ctor mixing a pointer field with packed sub-word scalars; the numeric tower
(`UInt32`/`UInt8` wrap, `Int` Euclidean div/mod, `Float`); multibyte UTF-8 `String`
get/next/extract/length/byteSize; `Array` foldl/map/range/getD/append and `List`
foldl/length/reverse/map; and a multi-step `LeanTodo.TodoList` sequence. All cases
must be identical between Lean and `node`, ending in `DIFF-TEST PASS`.

## Dependency

`lakefile.toml` requires `lean_todo` at `path = "../lean-todo-app/backend"`, so the
sibling checkout `conao3/lean-todo-app` must be present alongside this repo for the
`LeanTodo.Basic` diff-tests to build.

## Status / remaining gaps vs EmitC

- Constructor layout, the numeric tower (`UInt8/16/32/64`, `USize`, `Int` Euclidean
  div/mod, `Float`/`Float32`), UTF-8 byte-position `String` externs, and common
  `Array`/`List` operations are mapped. `IO`, `Float`/`Float32` transcendental
  `toString` formatting, and signed fixed-width ints (`Int8`..`Int64`) are not yet
  mapped.
- TCO handles self-`fap` tail recursion; mutual tail recursion and join-point tail
  edges across functions are not loop-ified.
- `USize` width is hardcoded to 64-bit; a 32-bit target would need `numBits = 32`.
- `Float.toString` matches Lean's C `%f` (6 decimal places) for finite values; `NaN`
  / `Inf` formatting is not reconciled.
