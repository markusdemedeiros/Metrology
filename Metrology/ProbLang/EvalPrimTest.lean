import Metrology.ProbLang.Notation
import Metrology.ProbLang.EvalPrim

open ProbLang ProbLang.EvalPrim

/-! Tests for the context-decomposing ProbLang interpreter (`EvalPrim`).

Each test calls `run` and asserts the result equals an expected `Exp`.
A failing assertion throws an IO error naming the test. -/

private def check (name : String) (prog : Exp) (expected : Exp) : IO Unit := do
  let v ← run prog
  if v.1 != expected then
    throw (IO.userError s!"FAIL [{name}]: got {repr v.1}, expected {repr expected}")

private def checkError (name : String) (prog : Exp) : IO Unit := do
  try
    let v ← run prog
    throw (IO.userError s!"FAIL [{name}]: expected error, got {repr v.1}")
  catch _ => pure ()

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
-- Context decomposition: the redex is found deep inside a larger expression.
-- These specifically exercise `primStep`'s use of `Exp.decomp`.
-- ---------------------------------------------------------------------------

-- Redex in the right argument of binop
#eval check "binop: redex in right arg"
  pl(#1 + fst((#2, #3)))
  (.lit (.int 3))

-- Redex in the left argument of binop (right is already a value)
#eval check "binop: redex in left arg"
  pl(fst((#1, #2)) + fst((#3, #4)))
  (.lit (.int 4))

-- Nested: fst inside the argument of snd
#eval check "snd of nested fst"
  pl(snd((fst((#1, #2)), #3)))
  (.lit (.int 3))

-- Redex under inl / inr
#eval check "inl of redex"  pl(inl(#1 + #2))  (.inl (.lit (.int 3)))
#eval check "inr of redex"  pl(inr(#3 * #4))  (.inr (.lit (.int 12)))

-- Condition expression contains a redex
#eval check "redex in condition"
  pl(if fst((#true, #false)) then #1 else #2)
  (.lit (.int 1))

-- ---------------------------------------------------------------------------
-- Conditionals
-- ---------------------------------------------------------------------------

#eval check "if true"  pl(if #true  then #1 else #2) (.lit (.int 1))
#eval check "if false" pl(if #false then #1 else #2) (.lit (.int 2))

-- ---------------------------------------------------------------------------
-- Functions and let
-- ---------------------------------------------------------------------------

-- (fun x => x) 42
#eval check "identity"
  (Exp.app (Exp.letrec .anon (.named "x") (.var "x")) (.lit (.int 42)))
  (.lit (.int 42))

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

#eval check "fst"  pl(fst((#1, #2)))  (.lit (.int 1))
#eval check "snd"  pl(snd((#1, #2)))  (.lit (.int 2))

-- let a := 10; let b := 20; a + b
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

-- case with a non-value scrutinee (redex is inside the scrutinee position)
#eval check "case: scrutinee is redex"
  (Exp.case
    (.inl (.binop .plus (.lit (.int 1)) (.lit (.int 2))))
    (Exp.letrec .anon (.named "x") (.var "x"))
    (Exp.letrec .anon .anon (.lit (.int 0))))
  (.lit (.int 3))

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
-- Failure and unsupported
-- ---------------------------------------------------------------------------

#eval checkError "fail"         pl(fail)
#eval checkError "assert false" pl(assert(#false))
#eval checkError "tape"         pl(tape(#10))
#eval checkError "rand with tape label"
  (.rand (.lit (.int 5)) (.lit (.lbl (0 : Int))))

#eval check "assert true" pl(assert(#true)) (.lit .unit)

-- ---------------------------------------------------------------------------
-- Rand (IO.rand 0 n returns values in [0, n] inclusive, so bound is z+1)
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
