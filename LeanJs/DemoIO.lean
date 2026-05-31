import LeanTodo.Basic

/-! IO demo program extracted by the lean-js CLI to prove end-to-end effectful
programs run under node and match Lean. Kept in a library module so its IR is
persisted and visible to `findEnvDecl` on re-import. -/

namespace LeanJs.DemoIO

open LeanTodo

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

def showTodo (t : Todo) : String :=
  let mark := if t.done then "x" else " "
  s!"{t.id}:{t.title}:{mark}"

def showList (l : TodoList) : String :=
  "[" ++ String.intercalate "," (l.items.map showTodo) ++ "]@" ++ toString l.nextId

/-- IO try/catch over a thrown `IO.userError`: the throw lands in the io_result
    error arm and `tryCatch` recovers it, proving the EST/EIO error channel. -/
def tryCatchIO : IO String := do
  try
    throw (IO.userError "boom")
  catch e =>
    pure s!"caught: {e.toString}"

def main : IO Unit := do
  IO.println "lean-js IO demo"
  IO.println s!"fib 10 = {fib 10}"
  IO.println s!"2 + 3 = {2 + 3}"
  -- Large Nat printed via the COMPILED path (Nat.reprFast). 10^18 sits in the
  -- reprFast "mid" range [reprArray.size, 2^64): it takes the slow path through
  -- USize.ofNatLT / USize.repr, which previously emitted a dangling call.
  IO.println s!"big1 = {(1000000000000000000 : Nat)}"
  -- A computed mid-range Nat (still < 2^64) also exercises that USize path.
  IO.println s!"big2 = {(2 : Nat) ^ 60}"
  -- A Nat >= 2^64 takes reprFast's Nat.toDigits (pure) slow path.
  IO.println s!"huge = {(123456789012345678901234567890 : Nat)}"
  let r ← IO.mkRef (0 : Nat)
  r.set 41
  r.modify (· + 1)
  let v ← r.get
  IO.println s!"ref = {v}"
  let l0 := TodoList.empty
  let l1 := l0.add "buy milk"
  let l2 := l1.add "walk dog"
  let l3 := l2.toggle 0
  IO.println s!"todo = {showList l3}"
  let caught ← tryCatchIO
  IO.println s!"trycatch = {caught}"
  IO.eprintln "diagnostic to stderr"

/-- Stdin-echo program: reads all lines from stdin (IO.getStdin / Stream.getLine)
    and echoes each prefixed, until EOF. Exercises the real fd-0 stdin wiring. -/
partial def echoLoop (stdin : IO.FS.Stream) (n : Nat) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    IO.println s!"EOF after {n} lines"
  else
    -- getLine keeps the trailing newline; drop a single trailing '\n' for echo.
    let trimmed := if line.back == '\n' then line.dropEnd 1 else line
    IO.println s!"line {n}: {trimmed}"
    echoLoop stdin (n + 1)

def stdinEcho : IO Unit := do
  let stdin ← IO.getStdin
  echoLoop stdin 1

/-- Error program: throws a userError so the process prints the Lean-format
    "uncaught exception: ..." to stderr and exits 1. -/
def errMain : IO Unit := do
  IO.println "before error"
  throw (IO.userError "boom from lean-js")

end LeanJs.DemoIO
