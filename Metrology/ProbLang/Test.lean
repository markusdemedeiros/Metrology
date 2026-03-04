import Metrology.ProbLang.Notation
import Metrology.ProbLang.Eval

open ProbLang ProbLang.Eval

/-! Tests for the ProbLang interpreter.

Each test calls `run` and asserts the result equals an expected `Exp`.
A failing assertion throws an IO error naming the test. -/

private def check (name : String) (prog : Exp) (expected : Exp) : IO Unit := do
  let v ← run prog
  if v.1 != expected then
    throw (IO.userError s!"FAIL [{name}]: got {repr v.1}, expected {repr expected}")

-- ---------------------------------------------------------------------------
-- Literals
-- ---------------------------------------------------------------------------

#eval check "int literal"  pl(#1)      (.lit (.int 1))
#eval check "bool literal" pl(#true)   (.lit (.bool true))
#eval check "unit literal" pl(#.unit)  (.lit .unit)

-- ---------------------------------------------------------------------------
-- Arithmetic and boolean operators
-- ---------------------------------------------------------------------------

#eval check "1 + 2 = 3"    pl(#1 + #2)          (.lit (.int 3))
#eval check "5 - 3 = 2"    pl(#5 - #3)          (.lit (.int 2))
#eval check "3 * 4 = 12"   pl(#3 * #4)          (.lit (.int 12))
#eval check "neg"           pl(- #5)             (.lit (.int (-5)))
#eval check "not true"      pl(~ #true)          (.lit (.bool false))
#eval check "and"           pl(#true && #false)  (.lit (.bool false))
#eval check "or"            pl(#false || #true)  (.lit (.bool true))
#eval check "xor"           pl(#true ^^ #true)   (.lit (.bool false))
#eval check "eq ints"       pl(#3 = #3)          (.lit (.bool true))
#eval check "neq ints"      pl(#3 = #4)          (.lit (.bool false))

-- ---------------------------------------------------------------------------
-- Conditionals
-- ---------------------------------------------------------------------------

#eval check "if true"  pl(if #true  then #1 else #2) (.lit (.int 1))
#eval check "if false" pl(if #false then #1 else #2) (.lit (.int 2))

-- ---------------------------------------------------------------------------
-- Functions and let (written using raw Exp to avoid parsing ambiguity)
-- ---------------------------------------------------------------------------

-- (fun x => x) 42
#eval check "identity" (Exp.app (Exp.letrec .anon (.named "x") (.var "x")) (.lit (.int 42)))
  (.lit (.int 42))

-- f = x = "x": (rec x x := x) applied to 99.
-- HeadStep substitutes f first: body "x" becomes the letrec itself.
-- Then substitutes x → 99 in the letrec, but "x" doesn't appear free in the
-- letrec body (the binding shadows it), so the result is the letrec value.
-- This is a value, so evaluation returns the letrec, not 99.
#eval check "f=x binder coincidence"
  (Exp.app (Exp.letrec (.named "x") (.named "x") (.var "x")) (.lit (.int 99)))
  (.letrec (.named "x") (.named "x") (.var "x"))

-- let x := 7; x + 3
#eval check "let"
  (Exp.app (Exp.letrec .anon (.named "x") (.binop .plus (.var "x") (.lit (.int 3))))
           (.lit (.int 7)))
  (.lit (.int 10))

-- (fun x => fun y => x + y) 3 4
#eval check "closure"
  (Exp.app
    (Exp.app
      (Exp.letrec .anon (.named "x")
        (Exp.letrec .anon (.named "y")
          (.binop .plus (.var "x") (.var "y"))))
      (.lit (.int 3)))
    (.lit (.int 4)))
  (.lit (.int 7))

-- ---------------------------------------------------------------------------
-- Recursion: factorial 5 = 120
-- ---------------------------------------------------------------------------

-- rec fact n := if n = 0 then 1 else n * fact(n-1), applied to 5
private def factExp : Exp :=
  Exp.letrec (.named "fact") (.named "n")
    (.cond
      (.binop .eq (.var "n") (.lit (.int 0)))
      (.lit (.int 1))
      (.binop .mult (.var "n")
        (.app (.var "fact") (.binop .minus (.var "n") (.lit (.int 1))))))

#eval check "factorial 5"
  (Exp.app factExp (.lit (.int 5)))
  (.lit (.int 120))

-- ---------------------------------------------------------------------------
-- Pairs
-- ---------------------------------------------------------------------------

#eval check "fst"  pl(fst((#1, #2)))   (.lit (.int 1))
#eval check "snd"  pl(snd((#1, #2)))   (.lit (.int 2))

-- let (a, b) := (10, 20); a + b  — using raw Exp
#eval check "let pair"
  (Exp.app
    (Exp.letrec .anon (.named "a")
      (Exp.app
        (Exp.letrec .anon (.named "b")
          (.binop .plus (.var "a") (.var "b")))
        (.lit (.int 20))))
    (.lit (.int 10)))
  (.lit (.int 30))

-- ---------------------------------------------------------------------------
-- Sums
-- ---------------------------------------------------------------------------

-- case inl(1) | x => x + 10 | _ => 0
#eval check "case inl"
  (Exp.case
    (.inl (.lit (.int 1)))
    (Exp.letrec .anon (.named "x") (.binop .plus (.var "x") (.lit (.int 10))))
    (Exp.letrec .anon .anon (.lit (.int 0))))
  (.lit (.int 11))

-- case inr(2) | _ => 0 | y => y + 20
#eval check "case inr"
  (Exp.case
    (.inr (.lit (.int 2)))
    (Exp.letrec .anon .anon (.lit (.int 0)))
    (Exp.letrec .anon (.named "y") (.binop .plus (.var "y") (.lit (.int 20)))))
  (.lit (.int 22))

-- ---------------------------------------------------------------------------
-- Heap
-- ---------------------------------------------------------------------------

-- let r := alloc(0); !r
#eval check "alloc/load"
  (Exp.app
    (Exp.letrec .anon (.named "r") (.load (.var "r")))
    (.alloc (.lit (.int 0))))
  (.lit (.int 0))

-- let r := alloc(0); r ← 42; !r
#eval check "alloc/store/load"
  (Exp.app
    (Exp.letrec .anon (.named "r")
      (Exp.app
        (Exp.letrec .anon .anon (.load (.var "r")))
        (.store (.var "r") (.lit (.int 42)))))
    (.alloc (.lit (.int 0))))
  (.lit (.int 42))

-- let r1 := alloc(1); let r2 := alloc(2); !r1 + !r2
#eval check "two refs"
  (Exp.app
    (Exp.letrec .anon (.named "r1")
      (Exp.app
        (Exp.letrec .anon (.named "r2")
          (.binop .plus (.load (.var "r1")) (.load (.var "r2"))))
        (.alloc (.lit (.int 2)))))
    (.alloc (.lit (.int 1))))
  (.lit (.int 3))

-- ---------------------------------------------------------------------------
-- Failure
-- ---------------------------------------------------------------------------

#eval do
  try
    let _ ← run pl(fail)
    throw (IO.userError "FAIL [fail]: expected error, got value")
  catch _ => pure ()

#eval do
  try
    let _ ← run pl(assert(#false))
    throw (IO.userError "FAIL [assert false]: expected error, got value")
  catch _ => pure ()

#eval check "assert true" pl(assert(#true)) (.lit .unit)

-- ---------------------------------------------------------------------------
-- Rand (result is in [0, 5] since IO.rand 0 n returns [0, n] inclusive)
-- ---------------------------------------------------------------------------

#eval do
  let v ← run pl(rand(#6, #.unit))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected ≥ 0")
    if n > 5 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected ≤ 5")
  | e => throw (IO.userError s!"FAIL [rand type]: got {repr e}")
