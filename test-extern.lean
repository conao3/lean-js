import LeanJs.EmitJS
open Lean Lean.IR LeanJs

/-! # Fail-loud link-check test (negative test)

Asserts that the lean-js emitter REJECTS an unmapped extern at extraction time —
the analogue of a C linker failing to resolve a symbol — instead of silently
emitting a dangling `funRef` call that ReferenceErrors at runtime under node.

`IO.getRandomBytes` carries `@[extern "lean_io_get_random_bytes"]`, a C symbol the
runtime `prelude.ts` does not define and which `emitKnownFap` does not
special-case. The checked renderer must therefore return `.error` naming that
symbol. We also assert a positive control (a fully-mapped root renders `.ok`). -/

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {} (loadExts := true)
  -- Negative: an extern with no prelude symbol must be a hard error.
  let badDecls := collectTransitive env #[``IO.getRandomBytes]
  match renderChecked env badDecls with
  | .ok _ =>
    throw (IO.userError "EXTERN-CHECK FAIL: unmapped extern IO.getRandomBytes was NOT rejected")
  | .error e =>
    unless (e.splitOn "lean_io_get_random_bytes").length > 1 do
      throw (IO.userError s!"EXTERN-CHECK FAIL: error did not name the symbol: {e}")
    IO.println "EXTERN-CHECK PASS: unmapped extern rejected (lean_io_get_random_bytes)"
  -- Positive control: a fully-mapped root renders ok.
  let goodDecls := collectTransitive env #[``Nat.repr]
  match renderChecked env goodDecls with
  | .ok _ => IO.println "EXTERN-CHECK PASS: mapped root (Nat.repr) renders ok"
  | .error e =>
    throw (IO.userError s!"EXTERN-CHECK FAIL: mapped root rejected: {e}")
