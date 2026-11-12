/-! Coverage-breadth probes (round 8): Group-A reproducible externs the prior
suite did not reach -- FloatArray (packed doubles) and the debug-trace helpers.
Each program prints deterministic output (FloatArray via Float.toString = C %f,
6 fixed digits; dbgTrace writes to stderr then returns the forced thunk). -/

namespace LeanTsTest.Stress4

/-! FloatArray: push / get! / set! / get / uget / size / toList. The `*!`
accessors exercise the OOB conventions (get! -> 0.0, set! -> unchanged). -/

def faProg : IO Unit := do
  let fa0 := FloatArray.empty
  let fa := (((fa0.push 1.5).push 2.25).push 4.125).push (-0.5)
  IO.println s!"fa size = {fa.size}"
  IO.println s!"fa get! 0 = {fa.get! 0}"
  IO.println s!"fa get! 2 = {fa.get! 2}"
  IO.println s!"fa get! oob = {fa.get! 9}"          -- OOB -> 0.0
  let fa2 := fa.set! 1 10.0
  IO.println s!"fa2 get! 1 = {fa2.get! 1}"
  IO.println s!"fa unchanged get! 1 = {fa.get! 1}"  -- copy-on-write: orig intact
  let fa3 := fa.set! 99 7.0                          -- OOB set! -> unchanged
  IO.println s!"fa3 size = {fa3.size} get! 0 = {fa3.get! 0}"
  -- in-bounds get (proof-carrying) and a fold over the contents.
  let mut acc := 0.0
  for x in fa do
    acc := acc + x
  IO.println s!"fa sum = {acc}"
  IO.println s!"fa toList = {fa.toList}"

/-! dbgTrace / dbgTraceIfShared: write a message to stderr (dbgTrace) then return
the value produced by forcing the thunk. dbgTraceIfShared never prints under JS
GC (no RC), matching the project's no-shared-only-path convention; its observable
behaviour is just to return its argument, identical to native here. -/

def traced (n : Nat) : Nat :=
  dbgTrace s!"trace: computing for {n}" (fun _ => n * n + 1)

def dbgProg : IO Unit := do
  IO.println s!"traced 6 = {traced 6}"
  let v := dbgTraceIfShared "should-not-print" (41 + 1)
  IO.println s!"ifShared = {v}"

def tracedThunk (n : Nat) : Thunk Nat :=
  Thunk.mk fun _ => dbgTrace s!"thunk: forcing {n}" fun _ => n * 10 + 1

def sumGets (t : Thunk Nat) (k : Nat) : Nat :=
  (List.range k).foldl (fun acc _ => acc + t.get) 0

def thunkProg (n : Nat) : IO Unit := do
  let t := tracedThunk n
  IO.println s!"thunk sum of 3 gets = {sumGets t 3}"
  let _unforced := tracedThunk (n + 100)
  IO.println s!"thunk pure = {(Thunk.pure (n + 2)).get}"
  let m := (tracedThunk (n + 1)).map (· * 2)
  IO.println s!"thunk map = {sumGets m 2}"
  let b := (tracedThunk (n + 2)).bind fun x => Thunk.pure (x + 1000)
  IO.println s!"thunk bind = {sumGets b 2}"
  let c : Thunk String := s!"coe {n}"
  IO.println s!"thunk coe = {c.get}"
  let ts := (List.range 3).map fun i => tracedThunk (n + 10 + i)
  IO.println s!"thunk list = {ts.map (·.get)} {ts.map (·.get)}"

def stress4Main : IO Unit := do
  faProg; dbgProg
  thunkProg 6

end LeanTsTest.Stress4
