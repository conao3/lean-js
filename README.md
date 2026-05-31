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

`test.sh` runs, against the native C-backend oracle: 135 function-level value
assertions (numeric tower, UTF-8 `String`, `Array`/`List`, `Mixed` packed ctor, a
`LeanTodo.TodoList` sequence); deep TCO (incl. closure-boundary tail `.ap`) at N=1e6;
a 32-bit `USize` profile; the fail-loud extern link check; runnable IO / stdin / error
/ panic / module-init programs; four `stress` programs (parser/sort/HashMap/TreeMap/
numeric/monadic; ByteArray+UTF-8 + derived `Repr` + `a[i]!`; HashMap/HashSet order;
**FloatArray + dbgTrace**); a verifier-authored `verify` program (JSON printer, RLE,
matrix multiply exercising **borrowed `a[i]!` indexing**, HashMap Dijkstra); and a
seeded property-fuzz pass. Every program must be byte-identical to the native binary.

## Dependency

`lakefile.toml` requires `lean_todo` at `path = "../lean-todo-app/backend"`, so the
sibling checkout `conao3/lean-todo-app` must be present alongside this repo for the
`LeanTodo.Basic` diff-tests to build.

## Parity vs the C backend

The oracle for every diff-test is the **native C-compiled Lean binary** (each test
program built through `lake build` → `leanc`), not `lean --run` (the interpreter
shares the same naive stack behaviour as JS and would mask divergences). Every claim
below is enforced by `test.sh` diffing node output against that native binary.

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
- **Owned/borrowed externs**: Lean 4.29.1 emits exactly three borrowed `@[extern]`
  variants, all for array element access — `lean_array_get_borrowed`,
  `lean_array_fget_borrowed`, `lean_array_uget_borrowed`. All three are mapped as
  prelude aliases of their owned twins, because the only C-level difference is a
  refcount `inc` on the result, which is a no-op under JS GC. So `a[i]!` and borrowed
  indexing/projection work **uniformly** (verified by the matrix-multiply inner loop
  in the `verify` diff-test, which lowers to `lean_array_get_borrowed`).
- **Control flow**: self- and mutual-recursion plus non-cyclic tail chains are loop-ified
  through a unified trampoline (`__tc` thunk targets); join points are inlined so
  `continue` stays lexically valid.
- **IO**: stdout/stderr/stdin (real fd, sync read), `IO.Error` formatting + entry-point
  `uncaught exception:` reporting, `@[init]`/`initialize` module-init chain, `panic!`
  semantics (print to stderr, return the `Inhabited` default, continue), `dbgTrace`/
  `dbgTraceIfShared`/`dbgSleep`.

### Where lean-js is *more* robust than the C backend

- **Closure-boundary TCO.** The native C backend does not TCO tail calls that cross a
  closure application (CPS/continuation loops), so programs like `cpsCount`/`cpsSum`
  abort with `Stack overflow detected` around N≈1e5. lean-js lowers tail `.ap` to an
  apply-thunk and runs them in constant JS stack. The diff-tests therefore check value
  equality at a native-safe N, and the no-overflow property at N=1e6 on the node side only.

### Fail-loud invariant

Any extern with no prelude mapping is a **hard extraction error** (`renderChecked`/
`renderProgramChecked` return `Except.error`, `Main` throws, non-zero exit) — never a
silent wrong answer or a dangling runtime call. The error names the exact missing C
symbol so it can be implemented and retried. A negative test (`test-extern.lean`)
asserts an unmapped extern (`lean_io_get_random_bytes`) is rejected while a mapped
root renders.

### Out of scope (intentionally left fail-loud) and why

These cannot be matched byte-for-byte against the native oracle, so mapping them would
trade an honest hard error for a silent divergence:

- **Task / `IO.asTask` / `IO.Promise` concurrency** (`lean_task_*`, `lean_io_*_task`,
  `lean_io_promise_*`): native runs a real OS thread pool with genuine parallelism and
  scheduler-dependent interleaving/`waitAny`/cancellation timing; Node is single-threaded,
  so any emulation observes a *different* ordering wherever ordering is observable.
- **Filesystem metadata / enumeration** (`lean_io_metadata`, `lean_io_symlink_metadata`,
  `lean_io_read_dir`, `lean_io_realpath`): `accessed`/`modified` timestamps, `numLinks`,
  directory order and symlink canonicalization are host/OS state, not program state, so
  they vary between runs and machines.
- **`IO.getRandomBytes`** (`lean_io_get_random_bytes`): by definition nondeterministic
  CSPRNG output; can never equal a fixed oracle run (used as the negative-test sentinel).
- **Raw-mode interactive TTY** (`lean_io_prim_handle_is_tty` and termios raw mode):
  depends on a live terminal device and real-time keystrokes; there is no reproducible
  input stream to diff. (Pipe/redirect/file stdin is supported and tested.)
- **Unsafe pointer identity** (`ptrAddrUnsafe`/`isExclusiveUnsafe`/`ptrEq` used to *distinguish*
  defeq values): real addresses are nondeterministic. The **safe** wrappers (`withPtrAddr`/
  `withPtrEq`/`withPtrEqDecEq`) are proven address-independent and are pure Lean (they do
  not even reach the extern), so they are faithful; the raw `lean_ptr_addr`/
  `lean_is_exclusive_obj` are mapped to address-independent constants (`0n` / non-exclusive)
  for the safe surface only.

## Remaining honest gaps vs EmitC

- The closure-boundary TCO divergence above is the one place lean-js and native cannot
  agree at large N (lean-js is the more robust side); value equality holds at native-safe N.
- `Float32` transcendentals use double-precision `Math.*` narrowed via `Math.fround`,
  whose rounding path differs from single-precision libm (`sinf`), so they can differ by
  >1 ULP at f32; the `%f` 6-digit `toString` comparison absorbs this but direct bit
  comparison is not claimed. `Float.scaleb` uses a `Math.pow(2,e)` approximation untested
  at extreme exponents.
- The 32-bit `USize` profile is covered by a literal-comparison test only (a 64-bit host
  cannot produce a native 32-bit reference); the default 64-bit profile is native-verified.
- The `lean_todo` dependency is referenced by sibling path (`../lean-todo-app/backend`).
