import Std.Data.HashMap

/-! Higher-order / closure / typeclass / exception coverage targets for the
lean-js CLI. Kept in a library module so their IR is persisted in the `.olean`
and visible to `Lean.IR.findEnvDecl` on re-import. These exercise emitter paths
that the first-order Demo functions never reach: `pap`/`ap`/closure capture
(`lean_apply`), monomorphized higher-order `List`/`Array` combinators, Monad
dictionary passing, the `Except` error channel, and `Std.HashMap`. -/

namespace LeanJs.DemoHO

-- C1 higher-order + lambdas: forces a `pap` closure constant + `ap`/lean_apply.
def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def hofApply : Nat := applyTwice (fun n => n * 2 + 1) 5
def listMapLam (xs : List Nat) : List Nat := xs.map (fun n => n + 10)
def listFilterLam (xs : List Nat) : List Nat := xs.filter (fun n => n % 2 == 0)
def listFoldlLam (xs : List Nat) : Nat := xs.foldl (fun a b => a * 10 + b) 0
def arrMapLam (xs : Array Nat) : Array Nat := xs.map (fun n => n * n)

-- C2 escaping nested closure capturing an outer var: a real captured `pap` that
-- is returned, stored in a list, and applied later through a variable. This is
-- the under/over-application-sensitive path: each `makeAdder n` is a 1-arg
-- closure (arity 2 worker, 1 captured), applied with exactly 1 arg later.
def makeAdder (n : Nat) : Nat → Nat := fun m => m + n
def applyAdders (x : Nat) : Nat :=
  let fs := [makeAdder 1, makeAdder 10, makeAdder 100]
  (fs.map (fun f => f x)).foldl (· + ·) 0

-- Curried application split across calls: `g` is the result of a partial app,
-- applied separately. Forces under-application (build a closure) then a second
-- application (saturate). `add3` is arity 3; `add3 a` under-applies.
def add3 (a b c : Nat) : Nat := a + b + c
def currySplit (x : Nat) : Nat :=
  let g := add3 x          -- under-application: closure capturing x, needs 2 more
  let h := g 100           -- under-application again: closure needs 1 more
  h 7                      -- saturate

-- C3 typeclass / Monad dictionary: one generic fn instantiated at two monads
-- forces a real dictionary ctor + projection + `lean_apply` on the bind field.
def twiceM {m : Type → Type} [Monad m] (act : m Nat) : m Nat := do
  let a ← act; let b ← act; pure (a + b)
def optSeq : Option Nat := twiceM (some 21)
def exSeq : Except String Nat := twiceM (.ok 21)
def fmapList (xs : List Nat) : List Nat := Functor.map (· + 1) xs

-- C5 exceptions / Except: clean ok/error ctors and a closed-term error string.
def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "div0" else .ok (a / b)
def safeDivStr (a b : Nat) : String :=
  match safeDiv a b with | .ok v => s!"ok {v}" | .error e => s!"err {e}"

-- C6 closure-boundary tail calls: a worker passed an indirect "step" function it
-- applies in tail position. `runWith` applies its `f` argument in tail position
-- (an `.ap`, not a statically-known `.fap`), and `f` here is a self-recursive
-- closure, so the loop drives a deep tail `.ap` chain. The non-trampolined apply
-- path stacks one JS frame per step and overflows; the apply-thunk flattens it.
partial def cpsLoop (f : Nat → Nat → Nat) (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | m+1 => f m acc
partial def runStep (n acc : Nat) : Nat :=
  cpsLoop (fun m a => runStep m (a + 1)) n acc
def cpsCount (n : Nat) : Nat := runStep n 0

-- Continuation-passing accumulator: the tail position is `k v` (a closure
-- application). Each recursion extends the continuation, then the final `k` call
-- unwinds the whole chain — a deep tail `.ap`.
partial def cpsSumK (n acc : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k acc
  | m+1 => cpsSumK m (acc + m + 1) k
def cpsSum (n : Nat) : Nat := cpsSumK n 0 (fun v => v)

-- C4 Std.HashMap: insert/find/size pulls in hashing externs and bucket ctors.
def hmDemo : Nat :=
  let m : Std.HashMap Nat Nat := (Std.HashMap.emptyWithCapacity.insert 1 10).insert 2 20
  (m.getD 1 0) + (m.getD 2 0) + m.size

end LeanJs.DemoHO
