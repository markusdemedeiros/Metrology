import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

open ProbLang Exp Ty

/-! # Tests for the LN surface-syntax elaborator.

Atoms are allocated from a per-`pl(...)` counter starting at 0, in
walk order. So `pl(x)` gives `fvar 0`, `pl(fun x, x)` gives
`lamN "x" none (close (fvar 0) 0)`, etc.

This file sanity-checks every surface form in the grammar. It's less
exhaustive than the pre-LN version (see `Notation.lean.bak`); the old
per-expression `#expect` asserts haven't been ported yet because they
need every RHS rewritten to LN form. -/

/-- Check that a ProbLang expression elaborates to the expected AST. -/
macro "#elabpl " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : $lhs = $rhs := by rfl)

/-! ## Reserved-keyword errors -/

/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fst) : Exp)
/-- error: 'snd' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(snd) : Exp)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(inl) : Exp)
/-- error: 'inr' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(inr) : Exp)
/-- error: 'alloc' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(alloc) : Exp)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rand) : Exp)
/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun fst, x) : Exp)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun inl, x) : Exp)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rec f rand := x) : Exp)

variable (e e1 e2 : Exp)

/-! ## Literals -/

#elabpl pl(#(.int 1))
#expect lit (.int 1)

#elabpl pl(#1)
#expect lit (.int 1)

#elabpl pl(#true)
#expect lit (.bool true)

#elabpl pl(#false)
#expect lit (.bool false)

#elabpl pl(#.unit)
#expect lit .unit

/-! ## Free variables: counter starts at 0 per `pl(...)` -/

#elabpl pl(x)
#expect .fvar 0

#elabpl pl(x + y)
#expect binop .plus (.fvar 0) (.fvar 1)

#elabpl pl(x + x)
#expect binop .plus (.fvar 0) (.fvar 0)

/-! ## Arithmetic and precedence -/

#elabpl pl(#1 + #2)
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#1 + #2 * #3)
#expect binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

#elabpl pl(#1 + #2 + #3)
#expect binop .plus (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl((#1 + #2) * #3)
#expect binop .mult (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

/-! ## Unary operators -/

#elabpl pl(~x)
#expect unop .neg (.fvar 0)

#elabpl pl(-x)
#expect unop .minus (.fvar 0)

#elabpl pl(-x + y)
#expect binop .plus (unop .minus (.fvar 0)) (.fvar 1)

/-! ## Booleans -/

#elabpl pl(x && y || z)
#expect binop .or (binop .and (.fvar 0) (.fvar 1)) (.fvar 2)

/-! ## Conditionals -/

#elabpl pl(if x then y else z)
#expect cond (.fvar 0) (.fvar 1) (.fvar 2)

/-! ## Sequencing and let -/

#elabpl pl(e1; e2)
#expect app (lamN "_" none (.fvar 1)) (.fvar 0)

#elabpl pl(let x := #1; x)
#expect app (lamN "x" none (close (.fvar 0) 0)) (lit (.int 1))

/-! ## Functions -/

#elabpl pl(fun x, x)
#expect lamN "x" none (close (.fvar 0) 0)

#elabpl pl(fun _, x)
#expect lamN "_" none (.fvar 0)

#elabpl pl(fun x y, x)
#expect lamN "x" none (close (lamN "y" none (close (.fvar 0) 1)) 0)

#elabpl pl(rec f x := f x)
#expect fixN "f" none (close (lamN "x" none (close (app (.fvar 0) (.fvar 1)) 1)) 0)

/-! ## Pairs and sums -/

#elabpl pl((x, y))
#expect pair (.fvar 0) (.fvar 1)

#elabpl pl((x, y, z))
#expect pair (.fvar 0) (pair (.fvar 1) (.fvar 2))

#elabpl pl(fst(x))
#expect fst (.fvar 0)

#elabpl pl(snd(x))
#expect snd (.fvar 0)

#elabpl pl(inl(x))
#expect inl (.fvar 0)

#elabpl pl(inr(x))
#expect inr (.fvar 0)

/-! ## Heap and state -/

#elabpl pl(alloc(#0))
#expect alloc (lit (.int 0))

#elabpl pl(!x)
#expect load (.fvar 0)

#elabpl pl(x ← #1)
#expect store (.fvar 0) (lit (.int 1))

/-! ## Random -/

#elabpl pl(tape(#10))
#expect .tape (lit (.int 10))

#elabpl pl(rand(#10, #.unit))
#expect rand (lit (.int 10)) (lit .unit)

/-! ## Failure and assertions -/

#elabpl pl(fail)
#expect Exp.fail

#elabpl pl(assert(b))
#expect cond (.fvar 0) (lit .unit) Exp.fail

/-! ## Type syntax -/

#elabpl pl_ty(int)
#expect Ty.int

#elabpl pl_ty(bool)
#expect Ty.bool

#elabpl pl_ty(unit)
#expect Ty.unit

#elabpl pl_ty(int × bool)
#expect Ty.prod .int .bool

#elabpl pl_ty(int + bool)
#expect Ty.sum .int .bool

#elabpl pl_ty(int → bool)
#expect Ty.arrow .int .bool

#elabpl pl_ty(ref(int))
#expect Ty.ref .int

#elabpl pl_ty(tape)
#expect Ty.tape

/-! ## Type annotations (phantom) -/

#elabpl pl((x : int))
#expect Exp.annotated .int (.fvar 0)

#elabpl pl((#1 : int))
#expect Exp.annotated .int (lit (.int 1))

/-! ## Typed binders -/

#elabpl pl(fun (x : int), x)
#expect lamN "x" (some .int) (close (.fvar 0) 0)

#elabpl pl(rec f (x : int) := f x)
#expect fixN "f" none (close (lamN "x" (some .int) (close (app (.fvar 0) (.fvar 1)) 1)) 0)

/-! ## Scrut -/

#elabpl pl(scrut x with y)
#expect Exp.scrut (.fvar 0) Pat.wildcard

#elabpl pl(scrut inl(#1) with inl(x))
#expect Exp.scrut (inl (lit (.int 1))) (.inl .wildcard)

/-! ## Patterns -/

#elabpl pl_pat(_)
#expect Pat.wildcard

#elabpl pl_pat(x)
#expect Pat.wildcard

#elabpl pl_pat(#(.int 1))
#expect Pat.lit (.int 1)

#elabpl pl_pat((x, y))
#expect Pat.pair .wildcard .wildcard

#elabpl pl_pat(inl(x))
#expect Pat.inl .wildcard

#elabpl pl_pat(inr(x))
#expect Pat.inr .wildcard

/-! ## Escape hatch -/

#elabpl pl({e})
#expect e

#elabpl pl({e1} + {e2})
#expect binop .plus e1 e2
