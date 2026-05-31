# lean2ts (proof of concept)

A Lean-to-TypeScript backend that mirrors Lean's C backend (`Lean.Compiler.IR.EmitC`),
driven by `Lean.Compiler.IR`. From the IR `Decl` of a Lean function it emits an
equivalent TypeScript/JavaScript function, then diff-tests it against Lean's own
execution.

## How it works

1. `def double` / `def mkShifted` are defined in `Main.lean`; elaboration triggers
   `Lean.compileDecl`, so their IR lands in the environment.
2. `Lean.IR.findEnvDecl env name` returns the traversable `Lean.IR.Decl`.
3. The emitter (`namespace Lean2ts` in `Main.lean`) walks `FnBody` / `Expr` and
   emits TS, mirroring `EmitC`'s match arms.

### Key simplification: GC target

The JS engine has a tracing GC, so all Lean reference-counting nodes are no-ops:

- `FnBody.inc` / `dec` / `del`            -> emit nothing
- `Expr.reset`                            -> `null` (unused reuse token)
- `Expr.reuse`                            -> a fresh ctor allocation (== `Expr.ctor`)
- `Expr.box` / `unbox`                    -> identity
- `Expr.isShared`                         -> `0` (Bool.false; nothing is "shared")

### Object / value model

- `Nat` -> `bigint` (arbitrary precision; no UInt32 boundary needed)
- ctor with fields -> `{ tag: cidx, fields: [...] }`
- nullary ctor / enum -> the integer `cidx` (mirrors `lean_box(cidx)`)
- `proj i x` -> `x.fields[i]`; `ctor` set -> `x.fields[i] = y`
- `Nat.add/sub/mul/...` externs -> inlined bigint ops (truncated sub, etc.)
- `case` on scalar -> `switch (x)`; on object -> `switch (x.tag)`
- join points -> local arrow-function closures; `jmp` -> `return j(args)`

## Run the diff-test

```
nix develop ../lean-todo-app --command bash -c "cd $(pwd) && ./test.sh"
```

Expected output: all 6 cases (3 `double`, 3 `mkShifted`) identical between Lean
`#eval` and `node`, ending in `DIFF-TEST PASS`.

## Files

- `Main.lean`    — emitter + target defs + `run_meta` dump + `main` (writes `out.ts`)
- `out.ts`       — generated TypeScript (committed for inspection)
- `expected.lean`— Lean reference execution
- `test.mjs`     — runs `out.ts` under node with the same inputs
- `test.sh`      — end-to-end diff-test

## Status / limitations (PoC scope)

Works end-to-end for `double` (Nat arithmetic) and `mkShifted` (ctor / proj /
record return, including the in-place-mutation branch under `isShared`). Not yet
handled: closures/`pap`/`ap` beyond a minimal runtime, `String` codepoint/byte
semantics, tail-call `while(true)` wrapping, and automatic transitive emission of
helper decls. The emitter only emits explicitly-named decls.
