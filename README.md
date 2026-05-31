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

- `Nat` / `Int` -> `bigint`; scalar literals (`u8`/`u32`/...) -> plain JS number.
- ctor with fields -> `{ tag: cidx, fields: [...] }`; nullary ctor / enum -> `cidx`.
  `lean_tag(x)` recovers the tag for both forms (mirrors `lean_obj_tag` on a boxed
  scalar).
- `Bool` -> scalar `0`/`1`; extern `decEq`/`decLt`/`decLe` return `0`/`1` so the
  emitted `switch` matches.
- `String` -> JS string with code-point semantics; `proj`/`set` -> `x.fields[i]`.
- `case` on scalar -> `switch (x)`; on object -> `switch (lean_tag(x))`.
- self-tail-recursion -> `while (true)` loop with staged param rebind + `continue`
  (join points inlined so `continue` stays lexically inside the loop).

## Run the diff-test

```
nix develop . --command bash -c "./test.sh"
```

Covers `double`, `mkShifted`, `sumTo` (incl. `100000`, exercising TCO), `fact`, and a
multi-step `LeanTodo.TodoList` sequence (add / toggle / remove / step over a 3-element
list). All cases must be identical between Lean and `node`, ending in `DIFF-TEST PASS`.

## Status / remaining gaps vs EmitC

- Externs cover Nat/Int/String/Array/List/Bool/Char basics; UTF-8 byte-offset `String`
  position externs, `Float`, full `UInt`/`USize` families, and `IO` are not yet mapped.
- TCO handles self-`fap` tail recursion; mutual tail recursion and join-point tail
  edges across functions are not loop-ified.
- `sproj`/`uproj`/`sset`/`uset` index the same `fields[]` as object projections;
  correct for the exercised ctors, fragile for ctors mixing pointer and packed-scalar
  fields at colliding indices.
