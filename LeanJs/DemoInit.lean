/-! `@[init]` action + `initialize` value-global coverage for the lean-js CLI.
Kept in a library module so the init metadata (`getInitFnNameFor?` /
`isIOUnitInitFn`) and the IR persist in the `.olean` and are visible on
re-import. The module-init chain must run both before `main`: the `@[init]`
banners for effect (in reverse-decl order) and the `initialize` ref bound once at
startup, then read/mutated by `main`. -/

namespace LeanJs.DemoInit

/-- An `@[init]` action: runs before `main`, for effect only.
    `getInitFnNameFor? = none`, `isIOUnitInitFn = true`. -/
@[init] def banner : IO Unit := IO.println "init: banner ran"

/-- An initialized value global: bound once at startup, then read/mutated by
    `main`. `getInitFnNameFor? = some initFn`, IR body `⊥`, params 0. -/
initialize gcounter : IO.Ref Nat ← IO.mkRef 100

/-- A second `@[init]` to prove reverse-decl ordering vs `banner`. -/
@[init] def banner2 : IO Unit := IO.println "init: banner2 ran"

def main : IO Unit := do
  let v0 ← gcounter.get
  IO.println s!"gcounter start = {v0}"
  gcounter.set (v0 + 11)
  let v1 ← gcounter.get
  IO.println s!"gcounter after set = {v1}"

end LeanJs.DemoInit
