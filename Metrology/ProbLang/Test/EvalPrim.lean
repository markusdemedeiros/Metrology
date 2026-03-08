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

#eval check "int literal"  pl(#1)      pl(#1)
#eval check "bool literal" pl(#true)   pl(#true)
#eval check "unit literal" pl(#.unit)  pl(#.unit)

-- ---------------------------------------------------------------------------
-- Arithmetic and boolean operators
-- ---------------------------------------------------------------------------

#eval check "1 + 2 = 3"   pl(#1 + #2)         pl(#3)
#eval check "5 - 3 = 2"   pl(#5 - #3)         pl(#2)
#eval check "3 * 4 = 12"  pl(#3 * #4)         pl(#12)
#eval check "neg"          pl(- #5)            pl(#(.int (-5)))
#eval check "not true"     pl(~ #true)         pl(#false)
#eval check "and"          pl(#true && #false) pl(#false)
#eval check "or"           pl(#false || #true) pl(#true)
#eval check "xor"          pl(#true ^^ #true)  pl(#false)
#eval check "eq ints"      pl(#3 = #3)         pl(#true)
#eval check "neq ints"     pl(#3 = #4)         pl(#false)

-- ---------------------------------------------------------------------------
-- Context decomposition: the redex is found deep inside a larger expression.
-- These specifically exercise `primStep`'s use of `Exp.decomp`.
-- ---------------------------------------------------------------------------

-- Redex in the right argument of binop
#eval check "binop: redex in right arg"
  pl(#1 + fst((#2, #3)))
  pl(#3)

-- Redex in the left argument of binop (right is already a value)
#eval check "binop: redex in left arg"
  pl(fst((#1, #2)) + fst((#3, #4)))
  pl(#4)

-- Nested: fst inside the argument of snd
#eval check "snd of nested fst"
  pl(snd((fst((#1, #2)), #3)))
  pl(#3)

-- Redex under inl / inr
#eval check "inl of redex"  pl(inl(#1 + #2))  pl(inl(#3))
#eval check "inr of redex"  pl(inr(#3 * #4))  pl(inr(#12))

-- Condition expression contains a redex
#eval check "redex in condition"
  pl(if fst((#true, #false)) then #1 else #2)
  pl(#1)

-- ---------------------------------------------------------------------------
-- Conditionals
-- ---------------------------------------------------------------------------

#eval check "if true"  pl(if #true  then #1 else #2) pl(#1)
#eval check "if false" pl(if #false then #1 else #2) pl(#2)

-- ---------------------------------------------------------------------------
-- Functions and let
-- ---------------------------------------------------------------------------

#eval check "identity"  pl((fun x, x) #42)      pl(#42)
#eval check "let"       pl(let x := #7; x + #3) pl(#10)
#eval check "closure"   pl((fun x y, x + y) #3 #4) pl(#7)

-- ---------------------------------------------------------------------------
-- Recursion: factorial 5 = 120
-- ---------------------------------------------------------------------------

private def factExp : Exp := pl(rec fact n := if n = #0 then #1 else n * fact (n - #1))

#eval check "factorial 5"  pl({factExp} #5)  pl(#120)

-- ---------------------------------------------------------------------------
-- Pairs
-- ---------------------------------------------------------------------------

#eval check "fst"  pl(fst((#1, #2)))  pl(#1)
#eval check "snd"  pl(snd((#1, #2)))  pl(#2)

#eval check "let pair"
  pl(let a := #10; let b := #20; a + b)
  pl(#30)

-- ---------------------------------------------------------------------------
-- Sums
-- ---------------------------------------------------------------------------

#eval check "case inl"
  pl(case inl(#1) | x => x + #10 | _ => #0)
  pl(#11)

#eval check "case inr"
  pl(case inr(#2) | _ => #0 | y => y + #20)
  pl(#22)

-- case with a non-value scrutinee (redex is inside the scrutinee position)
#eval check "case: scrutinee is redex"
  pl(case inl(#1 + #2) | x => x | _ => #0)
  pl(#3)

-- ---------------------------------------------------------------------------
-- Heap
-- ---------------------------------------------------------------------------

#eval check "alloc/load"
  pl(let r := alloc(#0); !r)
  pl(#0)

#eval check "alloc/store/load"
  pl(let r := alloc(#0); r ← #42; !r)
  pl(#42)

#eval check "two refs"
  pl(let r1 := alloc(#1); let r2 := alloc(#2); !r1 + !r2)
  pl(#3)

-- ---------------------------------------------------------------------------
-- Failure and unsupported
-- ---------------------------------------------------------------------------

#eval checkError "fail"         pl(fail)
#eval checkError "assert false" pl(assert(#false))
#eval checkError "tape"         pl(tape(#10))
#eval checkError "rand with tape label"
  pl(rand(#5, #(BaseLit.lbl (0 : Int))))

#eval check "assert true" pl(assert(#true)) pl(#.unit)

-- ---------------------------------------------------------------------------
-- Rand (IO.rand 0 n returns values in [0, n] inclusive, so bound is z+1)
-- ---------------------------------------------------------------------------

#eval do
  let v ← run pl(rand(#6, #.unit))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected ≥ 0")
    if n > 6 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected ≤ 6")
  | e => throw (IO.userError s!"FAIL [rand type]: got {repr e}")
