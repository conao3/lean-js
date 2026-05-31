import Std.Data.HashMap
import Std.Data.TreeMap

/-! Candidate stress programs for lean-js extraction + native diff-test.
Each `*Prog : IO Unit` prints deterministic results. Definitions are written
non-exponentially so the native C-backend oracle runs fast. -/

namespace LeanJs.DemoStress

/-! ===========================================================================
    P1. Recursive-descent parser / tokenizer over String.
    A tiny arithmetic-expression evaluator: tokenize a string into numbers and
    operator chars, then a recursive-descent parser with precedence (+,-,*) and
    parentheses. Exercises String.toList, Char predicates, List-based parser
    state threading, and Except error reporting. =========================== -/

inductive Tok where
  | num (n : Nat)
  | plus | minus | star | lparen | rparen
  deriving Inhabited

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

partial def lexNum (cs : List Char) (acc : Nat) : Nat × List Char :=
  match cs with
  | c :: rest =>
    if isDigit c then lexNum rest (acc * 10 + (c.toNat - '0'.toNat))
    else (acc, c :: rest)
  | [] => (acc, [])

partial def tokenize (cs : List Char) : List Tok :=
  match cs with
  | [] => []
  | c :: rest =>
    if c == ' ' then tokenize rest
    else if c == '+' then .plus :: tokenize rest
    else if c == '-' then .minus :: tokenize rest
    else if c == '*' then .star :: tokenize rest
    else if c == '(' then .lparen :: tokenize rest
    else if c == ')' then .rparen :: tokenize rest
    else if isDigit c then
      let (n, rest') := lexNum (c :: rest) 0
      .num n :: tokenize rest'
    else tokenize rest  -- skip unknown

mutual
  -- factor := num | '(' expr ')'
  partial def parseFactor : List Tok → Except String (Int × List Tok)
    | .num n :: ts => .ok (Int.ofNat n, ts)
    | .lparen :: ts => do
        let (v, ts') ← parseExpr ts
        match ts' with
        | .rparen :: ts'' => .ok (v, ts'')
        | _ => .error "expected )"
    | _ => .error "expected factor"
  -- term := factor ('*' factor)*
  partial def parseTerm (ts : List Tok) : Except String (Int × List Tok) := do
    let (lhs, ts1) ← parseFactor ts
    parseTermRest lhs ts1
  partial def parseTermRest (lhs : Int) : List Tok → Except String (Int × List Tok)
    | .star :: ts => do
        let (rhs, ts') ← parseFactor ts
        parseTermRest (lhs * rhs) ts'
    | ts => .ok (lhs, ts)
  -- expr := term (('+'|'-') term)*
  partial def parseExpr (ts : List Tok) : Except String (Int × List Tok) := do
    let (lhs, ts1) ← parseTerm ts
    parseExprRest lhs ts1
  partial def parseExprRest (lhs : Int) : List Tok → Except String (Int × List Tok)
    | .plus :: ts => do
        let (rhs, ts') ← parseTerm ts
        parseExprRest (lhs + rhs) ts'
    | .minus :: ts => do
        let (rhs, ts') ← parseTerm ts
        parseExprRest (lhs - rhs) ts'
    | ts => .ok (lhs, ts)
end

def eval (s : String) : Except String Int := do
  let (v, rest) ← parseExpr (tokenize s.toList)
  if rest.isEmpty then .ok v else .error "trailing input"

def showRes : Except String Int → String
  | .ok v => s!"ok {v}"
  | .error e => s!"error {e}"

def parserProg : IO Unit := do
  for s in ["1+2*3", "(1+2)*3", "10-2-3", "2*(3+4)*5", "7", "1+", "1 + 2 +  30"] do
    IO.println s!"{s} = {showRes (eval s)}"

/-! ===========================================================================
    P2. Sorting + data structures: List insertion sort, Array via List.toArray,
    a binary search tree (insert/inorder), Std.HashMap word counting, and
    Std.TreeMap (ordered map) accumulation. ================================ -/

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (isort xs)

inductive BST where
  | leaf
  | node (l : BST) (v : Nat) (r : BST)
  deriving Inhabited

def bstInsert (t : BST) (x : Nat) : BST :=
  match t with
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x < v then .node (bstInsert l x) v r
    else if x > v then .node l v (bstInsert r x)
    else t

def bstOfList (xs : List Nat) : BST := xs.foldl bstInsert .leaf

def bstInorder : BST → List Nat
  | .leaf => []
  | .node l v r => bstInorder l ++ [v] ++ bstInorder r

def wordCount (ws : List String) : Std.HashMap String Nat :=
  ws.foldl (fun m w => m.insert w ((m.getD w 0) + 1)) Std.HashMap.emptyWithCapacity

def treeSum (xs : List Nat) : Std.TreeMap Nat Nat :=
  xs.foldl (fun m x => m.insert x (x * x)) (Std.TreeMap.empty)

def dsProg : IO Unit := do
  let xs := [5, 3, 8, 1, 9, 2, 7, 4, 6, 0, 3, 5]
  IO.println s!"isort = {isort xs}"
  IO.println s!"bst inorder = {bstInorder (bstOfList xs)}"
  let wc := wordCount ["a", "b", "a", "c", "b", "a"]
  IO.println s!"wc a={wc.getD "a" 0} b={wc.getD "b" 0} c={wc.getD "c" 0} size={wc.size}"
  let tm := treeSum [3, 1, 2, 1, 4]
  -- ordered fold: keys ascending
  let pairs := tm.toList
  IO.println s!"treemap = {pairs}"

/-! ===========================================================================
    P3. Heavier String processing: split / intercalate / map toUpper / filter /
    padding / reverse. Exercises pure-Lean String combinators over Char ops. == -/

def strProg : IO Unit := do
  let line := "the quick brown fox jumps"
  let words := line.splitOn " "
  IO.println s!"nwords = {words.length}"
  IO.println s!"upper = {(words.map String.toUpper) |>.foldr (· ++ "-" ++ ·) ""}"
  IO.println s!"joined = {String.intercalate ", " words}"
  IO.println s!"rev = {String.intercalate " " words.reverse}"
  let csv := "1,22,333,4444"
  let parts := csv.splitOn ","
  IO.println s!"lens = {parts.map String.length}"
  IO.println s!"caps = {(words.filter (fun w => w.length > 4)).map String.capitalize}"

/-! ===========================================================================
    P4. Numeric algorithms: gcd/lcm, prime sieve over Array, bignum factorial,
    Fibonacci (iterative), integer sqrt. ==================================== -/

def gcd (a b : Nat) : Nat := Nat.gcd a b
def lcm (a b : Nat) : Nat := a * b / Nat.gcd a b

-- Sieve of Eratosthenes over an Array Bool, returning the prime list.
partial def sieveMark (a : Array Bool) (p i : Nat) : Array Bool :=
  if i < a.size then sieveMark (a.set! i false) p (i + p) else a

partial def sieveLoop (a : Array Bool) (p : Nat) : Array Bool :=
  if p * p < a.size then
    let a := if a.getD p false then sieveMark a p (p * p) else a
    sieveLoop a (p + 1)
  else a

def primesUpTo (n : Nat) : List Nat :=
  let init := (Array.range n).map (fun i => decide (i ≥ 2))
  let sieved := sieveLoop init 2
  (List.range n).filter (fun i => sieved.getD i false)

def factBig : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factBig n

partial def fibIter (n a b : Nat) : Nat :=
  match n with
  | 0 => a
  | m+1 => fibIter m b (a + b)

partial def isqrtGo (n x : Nat) : Nat :=
  let x' := (x + n / x) / 2
  if x' < x then isqrtGo n x' else x

def isqrt (n : Nat) : Nat := if n == 0 then 0 else isqrtGo n n

def numProg : IO Unit := do
  IO.println s!"gcd 462 1071 = {gcd 462 1071}"
  IO.println s!"lcm 21 6 = {lcm 21 6}"
  IO.println s!"primes<50 = {primesUpTo 50}"
  IO.println s!"fact 30 = {factBig 30}"
  IO.println s!"fact 50 = {factBig 50}"
  IO.println s!"fib 90 = {fibIter 90 0 1}"
  IO.println s!"isqrt 1000000 = {isqrt 1000000}"
  IO.println s!"isqrt 1234567890 = {isqrt 1234567890}"

/-! ===========================================================================
    P5. Monadic code: StateM counter, ExceptT over StateM, Option/Except chains
    with do-notation and bind. ============================================== -/

-- StateM: a stack-machine interpreter accumulating into state.
def push (n : Nat) : StateM (List Nat) Unit := modify (n :: ·)
def pop : StateM (List Nat) Nat := do
  let s ← get
  match s with
  | [] => pure 0
  | x :: xs => set xs; pure x

def runMachine : StateM (List Nat) Nat := do
  push 10
  push 20
  push 30
  let a ← pop
  let b ← pop
  push (a + b)
  let s ← get
  pure (s.foldl (· + ·) 0)

-- ExceptT String (StateM Nat): increment a counter, fail if it exceeds a bound.
def step (bound : Nat) : ExceptT String (StateM Nat) Unit := do
  let n ← get
  if n ≥ bound then throw s!"overflow at {n}"
  set (n + 1)

def runSteps (bound k : Nat) : String × Nat :=
  let prog : ExceptT String (StateM Nat) Unit := do
    for _ in [0:k] do step bound
  let (r, n) := (prog.run).run 0
  let msg := match r with | .ok _ => "ok" | .error e => e
  (msg, n)

-- Option chain: safe nested lookups.
def safeDivOpt (a b : Nat) : Option Nat := if b == 0 then none else some (a / b)
def optChain (a b c : Nat) : Option Nat := do
  let x ← safeDivOpt a b
  let y ← safeDivOpt x c
  pure (y + 1)

-- Except chain across multiple fallible steps.
def parsePos (n : Int) : Except String Nat :=
  if n < 0 then .error s!"neg {n}" else .ok n.toNat
def exChain (a b : Int) : Except String Nat := do
  let x ← parsePos a
  let y ← parsePos b
  if y == 0 then .error "div0" else .ok (x / y)

def showOpt : Option Nat → String
  | some v => s!"some {v}"
  | none => "none"

def monadProg : IO Unit := do
  IO.println s!"machine = {runMachine.run' []}"
  let (m1, n1) := runSteps 5 3
  IO.println s!"steps 5 3 = ({m1}, {n1})"
  let (m2, n2) := runSteps 3 5
  IO.println s!"steps 3 5 = ({m2}, {n2})"
  IO.println s!"optChain 100 5 2 = {showOpt (optChain 100 5 2)}"
  IO.println s!"optChain 100 0 2 = {showOpt (optChain 100 0 2)}"
  IO.println s!"exChain 10 3 = {showRes (exChain 10 3)}"
  IO.println s!"exChain -1 3 = {showRes (exChain (-1) 3)}"
  IO.println s!"exChain 10 0 = {showRes (exChain 10 0)}"

/-! ===========================================================================
    P6. Combined "everything" program kept small, driving a couple of the above
    plus Array fold / List zip for extra surface. =========================== -/

def comboProg : IO Unit := do
  let xs := List.range 10
  let ys := xs.map (· * 3)
  let zipped := xs.zip ys
  IO.println s!"zip = {zipped}"
  IO.println s!"sum = {(zipped.map (fun p => p.1 * p.2) |>.foldl (· + ·) 0)}"
  IO.println s!"arr = {(Array.range 6).map (fun i => i * i)}"

def stressMain : IO Unit := do
  parserProg; dsProg; strProg; numProg; monadProg; comboProg

end LeanJs.DemoStress
