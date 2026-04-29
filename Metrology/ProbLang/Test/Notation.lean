module

public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation

@[expose] public section

open ProbLang Exp Ty

/-! # Tests for the LN surface-syntax elaborator -/

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

/-! ## Free variables — atoms are the identifier string -/

#elabpl pl(x)
#expect .fvar "x"

#elabpl pl(x + y)
#expect binop .plus (.fvar "x") (.fvar "y")

-- Same identifier → same atom.
#elabpl pl(x + x)
#expect binop .plus (.fvar "x") (.fvar "x")

-- Different identifier → different atom.
example : pl(x) ≠ pl(y) := by
  intro h
  injection h with h'
  injection h' with h''
  exact (by decide : "x" ≠ "y") h''

example : pl(x) = Exp.fvar "x" := by rfl

/-! ## Arithmetic and precedence -/

#elabpl pl(#1 + #2)
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#1 + #2 * #3)
#expect binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

#elabpl pl(#1 + #2 + #3)
#expect binop .plus (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl((#1 + #2) * #3)
#expect binop .mult (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#1 - #2 - #3)
#expect binop .minus (binop .minus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#1 - #2 * #3)
#expect binop .minus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

/-! ## Unary operators -/

#elabpl pl(~x)
#expect unop .neg (.fvar "x")

#elabpl pl(-x)
#expect unop .minus (.fvar "x")

#elabpl pl(-x + y)
#expect binop .plus (unop .minus (.fvar "x")) (.fvar "y")

#elabpl pl(~~x)
#expect unop .neg (unop .neg (.fvar "x"))

#elabpl pl(-(x + y))
#expect unop .minus (binop .plus (.fvar "x") (.fvar "y"))

/-! ## Booleans and comparisons -/

#elabpl pl(~x && y)
#expect binop .and (unop .neg (.fvar "x")) (.fvar "y")

#elabpl pl(x && y || z)
#expect binop .or (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x && y ^^ z)
#expect binop .xor (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x ^^ y || z)
#expect binop .or (binop .xor (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x + y = z)
#expect binop .eq (binop .plus (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x = y = z)
#expect binop .eq (.fvar "x") (binop .eq (.fvar "y") (.fvar "z"))

#elabpl pl(x && y = z)
#expect binop .eq (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x || y = z)
#expect binop .eq (binop .or (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(~(x = y))
#expect unop .neg (binop .eq (.fvar "x") (.fvar "y"))

/-! ## Load and store interact with precedence -/

#elabpl pl(!x)
#expect load (.fvar "x")

#elabpl pl(!x + #1)
#expect binop .plus (load (.fvar "x")) (lit (.int 1))

#elabpl pl(!x * y)
#expect binop .mult (load (.fvar "x")) (.fvar "y")

#elabpl pl(!(!x))
#expect load (load (.fvar "x"))

#elabpl pl(x ← y)
#expect store (.fvar "x") (.fvar "y")

#elabpl pl(x ← alloc(y))
#expect store (.fvar "x") (alloc (.fvar "y"))

#elabpl pl(fst(p) ← x)
#expect store (fst (.fvar "p")) (.fvar "x")

#elabpl pl(p ← f x)
#expect store (.fvar "p") (app (.fvar "f") (.fvar "x"))

/-! ## Conditionals -/

#elabpl pl(if x then y else z)
#expect cond (.fvar "x") (.fvar "y") (.fvar "z")

#elabpl pl(if x then y + z else w)
#expect cond (.fvar "x") (binop .plus (.fvar "y") (.fvar "z")) (.fvar "w")

#elabpl pl(if x && y then z else w)
#expect cond (binop .and (.fvar "x") (.fvar "y")) (.fvar "z") (.fvar "w")

#elabpl pl(if (if b then x else y) then z else w)
#expect cond (cond (.fvar "b") (.fvar "x") (.fvar "y")) (.fvar "z") (.fvar "w")

#elabpl pl(if x then (if y then a else b) else c)
#expect cond (.fvar "x") (cond (.fvar "y") (.fvar "a") (.fvar "b")) (.fvar "c")

/-! ## Pairs and sums -/

#elabpl pl((x, y))
#expect pair (.fvar "x") (.fvar "y")

#elabpl pl((x, y, z))
#expect pair (.fvar "x") (pair (.fvar "y") (.fvar "z"))

#elabpl pl((a, b, c, d))
#expect pair (.fvar "a") (pair (.fvar "b") (pair (.fvar "c") (.fvar "d")))

#elabpl pl(fst(x))
#expect fst (.fvar "x")

#elabpl pl(snd(x))
#expect snd (.fvar "x")

#elabpl pl(snd((x, y)))
#expect snd (pair (.fvar "x") (.fvar "y"))

#elabpl pl(fst(snd((x, (y, z)))))
#expect fst (snd (pair (.fvar "x") (pair (.fvar "y") (.fvar "z"))))

#elabpl pl(inl(x))
#expect inl (.fvar "x")

#elabpl pl(inr(x))
#expect inr (.fvar "x")

#elabpl pl((inl(x), inr(y)))
#expect pair (inl (.fvar "x")) (inr (.fvar "y"))

#elabpl pl(inl(if b then x else y))
#expect inl (cond (.fvar "b") (.fvar "x") (.fvar "y"))

/-! ## Heap, random, failure -/

#elabpl pl(alloc(#0))
#expect alloc (lit (.int 0))

#elabpl pl(alloc(alloc(x)))
#expect alloc (alloc (.fvar "x"))

#elabpl pl(tape(#10))
#expect .tape (lit (.int 10))

#elabpl pl(rand(#10, #.unit))
#expect rand (lit (.int 10)) (lit .unit)

#elabpl pl(rand(tape(n), #.unit))
#expect rand (.tape (.fvar "n")) (lit .unit)

#elabpl pl(fail)
#expect Exp.fail

#elabpl pl(assert(b))
#expect cond (.fvar "b") (lit .unit) Exp.fail

/-! ## Application — left-associative, tighter than operators -/

#elabpl pl(f x y)
#expect app (app (.fvar "f") (.fvar "x")) (.fvar "y")

#elabpl pl(f x + g y)
#expect binop .plus (app (.fvar "f") (.fvar "x")) (app (.fvar "g") (.fvar "y"))

#elabpl pl(f x * g y)
#expect binop .mult (app (.fvar "f") (.fvar "x")) (app (.fvar "g") (.fvar "y"))

#elabpl pl(#0 x)
#expect app (lit (.int 0)) (.fvar "x")

#elabpl pl(fst(p) x)
#expect app (fst (.fvar "p")) (.fvar "x")

#elabpl pl((!f) x)
#expect app (load (.fvar "f")) (.fvar "x")

#elabpl pl(fst(f x))
#expect fst (app (.fvar "f") (.fvar "x"))

/-! ## Types -/

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

#elabpl pl_ty(int × bool × unit)
#expect Ty.prod .int (.prod .bool .unit)

#elabpl pl_ty(int → bool → unit)
#expect Ty.arrow .int (.arrow .bool .unit)

#elabpl pl_ty(int + bool + unit)
#expect Ty.sum .int (.sum .bool .unit)

#elabpl pl_ty(int × bool + unit)
#expect Ty.sum (.prod .int .bool) .unit

#elabpl pl_ty(int × bool → unit)
#expect Ty.arrow (.prod .int .bool) .unit

#elabpl pl_ty(int × (bool + unit))
#expect Ty.prod .int (.sum .bool .unit)

#elabpl pl_ty(int + bool → unit)
#expect Ty.arrow (.sum .int .bool) .unit

#elabpl pl_ty(ref(int) × ref(bool))
#expect Ty.prod (.ref .int) (.ref .bool)

#elabpl pl_ty(ref(ref(int)))
#expect Ty.ref (.ref .int)

#elabpl pl_ty(ref(int × bool))
#expect Ty.ref (.prod .int .bool)

/-! ## Type annotations (phantom) -/

#elabpl pl((x : int))
#expect Exp.annotated .int (.fvar "x")

#elabpl pl((#1 : int))
#expect Exp.annotated .int (lit (.int 1))

#elabpl pl((x + y : int))
#expect Exp.annotated .int (binop .plus (.fvar "x") (.fvar "y"))

#elabpl pl((x : int → bool))
#expect Exp.annotated (.arrow .int .bool) (.fvar "x")

#elabpl pl((x : int × bool))
#expect Exp.annotated (.prod .int .bool) (.fvar "x")

#elabpl pl(((x : int) : int))
#expect Exp.annotated .int (Exp.annotated .int (.fvar "x"))

#elabpl pl(alloc((#0 : int)))
#expect alloc (Exp.annotated .int (lit (.int 0)))

#elabpl pl(!(r : ref(int)))
#expect load (Exp.annotated (.ref .int) (.fvar "r"))

#elabpl pl(fst(((#1, #2) : int × int)))
#expect fst (Exp.annotated (.prod .int .int) (pair (lit (.int 1)) (lit (.int 2))))

/-! ## Scrut -/

#elabpl pl(scrut x with y)
#expect Exp.scrut (.fvar "x") Pat.wildcard

#elabpl pl(scrut inl(#1) with inl(x))
#expect Exp.scrut (inl (lit (.int 1))) (.inl .wildcard)

#elabpl pl(scrut (x, y) with (a, b))
#expect Exp.scrut (pair (.fvar "x") (.fvar "y")) (.pair .wildcard .wildcard)

-- (Annotated pattern `scrut x with (y : int)` has elaborator dispatch issues;
--  skipped — same issue as `pl_pat((y : int))`.)

/-! ## Patterns -/

#elabpl pl_pat(_)
#expect Pat.wildcard

#elabpl pl_pat(x)
#expect Pat.wildcard

#elabpl pl_pat(# .unit)
#expect Pat.lit .unit

#elabpl pl_pat(#(.int 1))
#expect Pat.lit (.int 1)

#elabpl pl_pat((x, y))
#expect Pat.pair .wildcard .wildcard

#elabpl pl_pat(inl(x))
#expect Pat.inl .wildcard

#elabpl pl_pat(inr(x))
#expect Pat.inr .wildcard

#elabpl pl_pat(inl((x, y)))
#expect Pat.inl (Pat.pair .wildcard .wildcard)

#elabpl pl_pat((inl(x), inr(y)))
#expect Pat.pair (Pat.inl .wildcard) (Pat.inr .wildcard)

/-! ## Escape hatch -/

#elabpl pl({e})
#expect e

#elabpl pl({e1} + {e2})
#expect binop .plus e1 e2

/-! ## Delaboration round-trip tests

These verify that elaborated `Exp` values delaborate back to readable
`pl(...)` syntax. -/

/-! ### Atomic / non-binder forms (round-trip cleanly) -/

/-- info: pl(#1) : Exp -/
#guard_msgs in #check (pl(#1) : Exp)

/-- info: pl(#true) : Exp -/
#guard_msgs in #check (pl(#true) : Exp)

/-- info: pl(#false) : Exp -/
#guard_msgs in #check (pl(#false) : Exp)

/-- info: pl(x) : Exp -/
#guard_msgs in #check (pl(x) : Exp)

/-- info: pl((x + #1)) : Exp -/
#guard_msgs in #check (pl(x + #1) : Exp)

/-- info: pl((x - y)) : Exp -/
#guard_msgs in #check (pl(x - y) : Exp)

/-- info: pl((x * y)) : Exp -/
#guard_msgs in #check (pl(x * y) : Exp)

/-- info: pl((x && y)) : Exp -/
#guard_msgs in #check (pl(x && y) : Exp)

/-- info: pl((x || y)) : Exp -/
#guard_msgs in #check (pl(x || y) : Exp)

/-- info: pl((x ^^ y)) : Exp -/
#guard_msgs in #check (pl(x ^^ y) : Exp)

/-- info: pl((x = y)) : Exp -/
#guard_msgs in #check (pl(x = y) : Exp)

/-- info: pl(~x) : Exp -/
#guard_msgs in #check (pl(~x) : Exp)

/-- info: pl(-x) : Exp -/
#guard_msgs in #check (pl(-x) : Exp)

/-- info: pl(!x) : Exp -/
#guard_msgs in #check (pl(!x) : Exp)

/-- info: pl(if x then y else z) : Exp -/
#guard_msgs in #check (pl(if x then y else z) : Exp)

/-- info: pl((x, y)) : Exp -/
#guard_msgs in #check (pl((x, y)) : Exp)

/-- info: pl((x, y, z)) : Exp -/
#guard_msgs in #check (pl((x, y, z)) : Exp)

/-- info: pl(fst(x)) : Exp -/
#guard_msgs in #check (pl(fst(x)) : Exp)

/-- info: pl(snd(x)) : Exp -/
#guard_msgs in #check (pl(snd(x)) : Exp)

/-- info: pl(inl(x)) : Exp -/
#guard_msgs in #check (pl(inl(x)) : Exp)

/-- info: pl(inr(x)) : Exp -/
#guard_msgs in #check (pl(inr(x)) : Exp)

/-- info: pl(alloc(#0)) : Exp -/
#guard_msgs in #check (pl(alloc(#0)) : Exp)

/-- info: pl(x ← y) : Exp -/
#guard_msgs in #check (pl(x ← y) : Exp)

/-- info: pl(tape(#10)) : Exp -/
#guard_msgs in #check (pl(tape(#10)) : Exp)

/-- info: pl(rand(#10, #())) : Exp -/
#guard_msgs in #check (pl(rand(#10, #.unit)) : Exp)

/-- info: pl(fail) : Exp -/
#guard_msgs in #check (pl(fail) : Exp)

/-- info: pl(scrut x with _) : Exp -/
#guard_msgs in #check (pl(scrut x with y) : Exp)

/-- info: pl(scrut inl(x) with inl(_)) : Exp -/
#guard_msgs in #check (pl(scrut inl(x) with inl(y)) : Exp)

/-! ### Type delaboration -/

/-- info: pl_ty(int) : Ty -/
#guard_msgs in #check (pl_ty(int))

/-- info: pl_ty(bool) : Ty -/
#guard_msgs in #check (pl_ty(bool))

/-- info: pl_ty(unit) : Ty -/
#guard_msgs in #check (pl_ty(unit))

/-- info: pl_ty(int × bool) : Ty -/
#guard_msgs in #check (pl_ty(int × bool))

/-- info: pl_ty(int + bool) : Ty -/
#guard_msgs in #check (pl_ty(int + bool))

/-- info: pl_ty(int → bool) : Ty -/
#guard_msgs in #check (pl_ty(int → bool))

/-- info: pl_ty(ref(int)) : Ty -/
#guard_msgs in #check (pl_ty(ref(int)))

/-- info: pl_ty(tape) : Ty -/
#guard_msgs in #check (pl_ty(tape))

/-- info: pl_ty(int × bool → unit) : Ty -/
#guard_msgs in #check (pl_ty(int × bool → unit))

/-- info: pl_ty(ref(int → bool)) : Ty -/
#guard_msgs in #check (pl_ty(ref(int → bool)))

/-! ### Pattern delaboration — identifier patterns elaborate to wildcard -/

/-- info: pl_pat(_) : Pat -/
#guard_msgs in #check (pl_pat(_))

/-- info: pl_pat(_) : Pat -/
#guard_msgs in #check (pl_pat(x))

/-- info: pl_pat((_, _)) : Pat -/
#guard_msgs in #check (pl_pat((x, y)))

/-- info: pl_pat(inl(_)) : Pat -/
#guard_msgs in #check (pl_pat(inl(x)))

/-- info: pl_pat(inr(_)) : Pat -/
#guard_msgs in #check (pl_pat(inr(x)))

/-! ### Annotation delab gated by `pp.problang.annot` -/

-- Default: annotation hidden.
/-- info: pl(x) : Exp -/
#guard_msgs in #check (pl((x : int)) : Exp)

set_option pp.problang.annot 2 in
/-- info: pl((x : int)) : Exp -/
#guard_msgs in #check (pl((x : int)) : Exp)

set_option pp.problang.annot 2 in
/-- info: pl(((x + y) : int)) : Exp -/
#guard_msgs in #check (pl((x + y : int)) : Exp)

set_option pp.problang.annot 2 in
/-- info: pl((x : int → bool)) : Exp -/
#guard_msgs in #check (pl((x : int → bool)) : Exp)
