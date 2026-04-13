import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

open ProbLang Exp Ty

/-! # Tests for the LN surface-syntax elaborator.

Atoms are allocated from a per-`pl(...)` counter starting at 0, in
walk order. So `pl(x)` gives `fvar 0`, `pl(fun x, x)` gives
`Exp.lam (close (fvar 0) 0)`, etc.

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
#expect app (Exp.lam (.fvar 1)) (.fvar 0)

#elabpl pl(let x := #1; x)
#expect app (Exp.lam (close (.fvar 0) 0)) (lit (.int 1))

/-! ## Functions -/

#elabpl pl(fun x, x)
#expect Exp.lam (close (.fvar 0) 0)

#elabpl pl(fun _, x)
#expect Exp.lam (.fvar 0)

#elabpl pl(fun x y, x)
#expect Exp.lam (close (Exp.lam (close (.fvar 0) 1)) 0)

#elabpl pl(rec f x := f x)
#expect Exp.fix (close (Exp.lam (close (app (.fvar 0) (.fvar 1)) 1)) 0)

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
#expect Exp.lam (close (.fvar 0) 0)

#elabpl pl(rec f (x : int) := f x)
#expect Exp.fix (close (Exp.lam (close (app (.fvar 0) (.fvar 1)) 1)) 0)

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

/-! ## Precedence and associativity -/

-- + is left-associative
#elabpl pl(#1 - #2 - #3)
#expect binop .minus (binop .minus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

-- * binds tighter than -
#elabpl pl(#1 - #2 * #3)
#expect binop .minus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

-- ~ binds tighter than &&
#elabpl pl(~x && y)
#expect binop .and (unop .neg (.fvar 0)) (.fvar 1)

-- && binds tighter than ||
#elabpl pl(x && y || z)
#expect binop .or (binop .and (.fvar 0) (.fvar 1)) (.fvar 2)

-- = has lower precedence than +
#elabpl pl(x + y = z)
#expect binop .eq (binop .plus (.fvar 0) (.fvar 1)) (.fvar 2)

-- load binds tighter than +
#elabpl pl(!x + #1)
#expect binop .plus (load (.fvar 0)) (lit (.int 1))

-- load binds tighter than *
#elabpl pl(!x * y)
#expect binop .mult (load (.fvar 0)) (.fvar 1)

-- application is left-associative
#elabpl pl(f x y)
#expect app (app (.fvar 0) (.fvar 1)) (.fvar 2)

-- application binds tighter than +
#elabpl pl(f x + g y)
#expect binop .plus (app (.fvar 0) (.fvar 1)) (app (.fvar 2) (.fvar 3))

-- application binds tighter than *
#elabpl pl(f x * g y)
#expect binop .mult (app (.fvar 0) (.fvar 1)) (app (.fvar 2) (.fvar 3))

-- xor precedence: ^^ binds tighter than ||, looser than &&
#elabpl pl(x && y ^^ z)
#expect binop .xor (binop .and (.fvar 0) (.fvar 1)) (.fvar 2)

#elabpl pl(x ^^ y || z)
#expect binop .or (binop .xor (.fvar 0) (.fvar 1)) (.fvar 2)

-- unary minus vs binary minus
#elabpl pl(-x - y)
#expect binop .minus (unop .minus (.fvar 0)) (.fvar 1)

#elabpl pl(x - -y)
#expect binop .minus (.fvar 0) (unop .minus (.fvar 1))

-- ~ applied to equality
#elabpl pl(~(x = y))
#expect unop .neg (binop .eq (.fvar 0) (.fvar 1))

-- = lower precedence than &&
#elabpl pl(x && y = z)
#expect binop .eq (binop .and (.fvar 0) (.fvar 1)) (.fvar 2)

-- = lower precedence than ||
#elabpl pl(x || y = z)
#expect binop .eq (binop .or (.fvar 0) (.fvar 1)) (.fvar 2)

-- = is right-associative
#elabpl pl(x = y = z)
#expect binop .eq (.fvar 0) (binop .eq (.fvar 1) (.fvar 2))

-- unary minus binds tighter than binary +
#elabpl pl(-x + y)
#expect binop .plus (unop .minus (.fvar 0)) (.fvar 1)

-- double negation
#elabpl pl(~~x)
#expect unop .neg (unop .neg (.fvar 0))

-- unary minus on compound
#elabpl pl(-(x + y))
#expect unop .minus (binop .plus (.fvar 0) (.fvar 1))

/-! ## Store, load, alloc combinations -/

-- store into a computed address
#elabpl pl(fst(p) ← x)
#expect store (fst (.fvar 0)) (.fvar 1)

-- load of a load
#elabpl pl(!(!x))
#expect load (load (.fvar 0))

-- alloc of an alloc
#elabpl pl(alloc(alloc(x)))
#expect alloc (alloc (.fvar 0))

-- store into an allocated reference
#elabpl pl(x ← alloc(y))
#expect store (.fvar 0) (alloc (.fvar 1))

-- apply a load
#elabpl pl((!f) x)
#expect app (load (.fvar 0)) (.fvar 1)

-- store the result of an application
#elabpl pl(p ← f x)
#expect store (.fvar 0) (app (.fvar 1) (.fvar 2))

-- fst of an application
#elabpl pl(fst(f x))
#expect fst (app (.fvar 0) (.fvar 1))

/-! ## Conditionals with compound subs -/

-- if with arithmetic in branch
#elabpl pl(if x then y + z else w)
#expect cond (.fvar 0) (binop .plus (.fvar 1) (.fvar 2)) (.fvar 3)

-- if condition contains boolean op
#elabpl pl(if x && y then z else w)
#expect cond (binop .and (.fvar 0) (.fvar 1)) (.fvar 2) (.fvar 3)

-- if condition is itself an if
#elabpl pl(if (if b then x else y) then z else w)
#expect cond (cond (.fvar 0) (.fvar 1) (.fvar 2)) (.fvar 3) (.fvar 4)

-- if branches are ifs
#elabpl pl(if x then (if y then a else b) else c)
#expect cond (.fvar 0) (cond (.fvar 1) (.fvar 2) (.fvar 3)) (.fvar 4)

-- inl of an if
#elabpl pl(inl(if b then x else y))
#expect inl (cond (.fvar 0) (.fvar 1) (.fvar 2))

/-! ## Multi-arg functions -/

-- three-arg rec
#elabpl pl(rec f x y z := f x y z)
#expect Exp.fix (close
          (Exp.lam (close
            (Exp.lam (close
              (Exp.lam (close
                (app (app (app (.fvar 0) (.fvar 1)) (.fvar 2)) (.fvar 3))
                3))
              2))
            1))
          0)

-- rec with multiple args desugars to rec + inner fun
#elabpl pl(rec f x y := f x y)
#expect Exp.fix (close
          (Exp.lam (close
            (Exp.lam (close
              (app (app (.fvar 0) (.fvar 1)) (.fvar 2))
              2))
            1))
          0)

-- rec with anon arg
#elabpl pl(rec f _ := f)
#expect Exp.fix (close (Exp.lam (.fvar 0)) 0)

-- fun with _ applied
#elabpl pl((fun _, fail) #1)
#expect app (Exp.lam Exp.fail) (lit (.int 1))

-- fun body is itself a fun (currying spelled out)
#elabpl pl(fun x, fun y, x)
#expect Exp.lam (close (Exp.lam (close (.fvar 0) 1)) 0)

-- application of a fun (immediate invocation)
#elabpl pl((fun x, x) y)
#expect app (Exp.lam (close (.fvar 0) 0)) (.fvar 1)

-- application of a rec
#elabpl pl((rec f x := f x) y)
#expect app (Exp.fix (close (Exp.lam (close (app (.fvar 0) (.fvar 1)) 1)) 0)) (.fvar 2)

/-! ## Sequencing combinations -/

-- e1; e2; e3 is right-associative
#elabpl pl(e1; e2; e3)
#expect app (Exp.lam (app (Exp.lam (.fvar 2)) (.fvar 1))) (.fvar 0)

-- store into address then seq
#elabpl pl(x ← y; z)
#expect app (Exp.lam (.fvar 2)) (store (.fvar 0) (.fvar 1))

-- sequencing with fail
#elabpl pl(fail; x)
#expect app (Exp.lam (.fvar 0)) Exp.fail

/-! ## Let combinations -/

-- let x := e1; (e2; e3) — let binds tighter than ;
#elabpl pl(let x := e1; e2; e3)
#expect app
          (Exp.lam (close
            (app (Exp.lam (.fvar 3)) (.fvar 2))
            1))
          (.fvar 0)

-- nested let
#elabpl pl(let x := e1; let y := e2; x + y)
#expect app
          (Exp.lam (close
            (app
              (Exp.lam (close (binop .plus (.fvar 0) (.fvar 1)) 1))
              (.fvar 2))
            0))
          (.fvar 0)

-- let with escape-hatch value
#elabpl pl(let x := {e}; x)
#expect app (Exp.lam (close (.fvar 0) 0)) e

-- if-then-else inside a let
#elabpl pl(if x then let y := e; y else z)
#expect cond (.fvar 0)
          (app (Exp.lam (close (.fvar 2) 2)) (.fvar 1))
          (.fvar 3)

-- let binding a fun
#elabpl pl(let f := fun x, x; f)
#expect app (Exp.lam (close (.fvar 0) 0)) (Exp.lam (close (.fvar 0) 0))

-- let binding a pair
#elabpl pl(let p := (x, y); fst(p))
#expect app (Exp.lam (close (fst (.fvar 2)) 2)) (pair (.fvar 0) (.fvar 1))

-- deeply nested lets
#elabpl pl(let x := (let y := #1; y); x)
#expect app (Exp.lam (close (.fvar 0) 0))
            (app (Exp.lam (close (.fvar 0) 0)) (lit (.int 1)))

-- fun body is an escape-hatch Lean term
#elabpl pl(fun x, {e})
#expect Exp.lam (close e 0)

/-! ## Shadowing — bodies reuse outermost binder's atom since names go
     through the `NameEnv` which is reassigned. -/

#elabpl pl(let x := e; let x := x; x)
#expect app
          (Exp.lam (close
            (app (Exp.lam (close (.fvar 1) 1)) (.fvar 0)) 0))
          (.fvar 0)

#elabpl pl(fun x, fun x, x)
#expect Exp.lam (close (Exp.lam (close (.fvar 1) 1)) 0)

#elabpl pl(rec f x := rec f x := f x)
#expect Exp.fix (close
          (Exp.lam (close
            (Exp.fix (close
              (Exp.lam (close
                (app (.fvar 2) (.fvar 3)) 3))
              2))
            1))
          0)

-- rec self-name and arg name the same identifier
#elabpl pl(rec x x := x x)
#expect Exp.fix (close (Exp.lam (close (app (.fvar 1) (.fvar 1)) 1)) 0)

/-! ## Deep pairs -/

-- 4-tuple
#elabpl pl((a, b, c, d))
#expect pair (.fvar 0) (pair (.fvar 1) (pair (.fvar 2) (.fvar 3)))

-- pair of sums
#elabpl pl((inl(x), inr(y)))
#expect pair (inl (.fvar 0)) (inr (.fvar 1))

-- snd of a nested triple
#elabpl pl(snd((x, y, z)))
#expect snd (pair (.fvar 0) (pair (.fvar 1) (.fvar 2)))

-- fst/snd of pair-of-pairs
#elabpl pl(fst(snd((x, (y, z)))))
#expect fst (snd (pair (.fvar 0) (pair (.fvar 1) (.fvar 2))))

-- alloc of a fun value
#elabpl pl(alloc(fun x, x))
#expect alloc (Exp.lam (close (.fvar 0) 0))

-- rand on a tape
#elabpl pl(rand(tape(n), #.unit))
#expect rand (.tape (.fvar 0)) (lit .unit)

-- tape-in-let sequenced with rand
#elabpl pl(let t := tape(n); rand(t, #.unit))
#expect app
          (Exp.lam (close (rand (.fvar 1) (lit .unit)) 1))
          (.tape (.fvar 0))

/-! ## Type precedence -/

-- × is right-associative
#elabpl pl_ty(int × bool × unit)
#expect Ty.prod .int (.prod .bool .unit)

-- → is right-associative
#elabpl pl_ty(int → bool → unit)
#expect Ty.arrow .int (.arrow .bool .unit)

-- + is right-associative
#elabpl pl_ty(int + bool + unit)
#expect Ty.sum .int (.sum .bool .unit)

-- × binds tighter than +
#elabpl pl_ty(int × bool + unit)
#expect Ty.sum (.prod .int .bool) .unit

-- × binds tighter than →
#elabpl pl_ty(int × bool → unit)
#expect Ty.arrow (.prod .int .bool) .unit

-- parentheses override precedence
#elabpl pl_ty(int × (bool + unit))
#expect Ty.prod .int (.sum .bool .unit)

-- + binds tighter than →
#elabpl pl_ty(int + bool → unit)
#expect Ty.arrow (.sum .int .bool) .unit

-- ref inside compounds
#elabpl pl_ty(ref(int) × ref(bool))
#expect Ty.prod (.ref .int) (.ref .bool)

-- nested ref
#elabpl pl_ty(ref(ref(int)))
#expect Ty.ref (.ref .int)

#elabpl pl_ty(ref(int × bool))
#expect Ty.ref (.prod .int .bool)

/-! ## Annotation on compound expressions -/

#elabpl pl((x + y : int))
#expect Exp.annotated .int (binop .plus (.fvar 0) (.fvar 1))

#elabpl pl((x : int → bool))
#expect Exp.annotated (.arrow .int .bool) (.fvar 0)

#elabpl pl((x : int × bool))
#expect Exp.annotated (.prod .int .bool) (.fvar 0)

-- nested annotation
#elabpl pl(((x : int) : int))
#expect Exp.annotated .int (Exp.annotated .int (.fvar 0))

-- typed binder in let
#elabpl pl(let (x : int) := #1; x)
#expect app (Exp.lam (close (.fvar 0) 0)) (lit (.int 1))

-- Mixed typed/untyped binders
#elabpl pl(fun (x : int) y, x + y)
#expect Exp.lam (close
          (Exp.lam (close (binop .plus (.fvar 0) (.fvar 1)) 1))
          0)

-- Multi-arg rec with all typed binders
#elabpl pl(rec f (x : int) (y : bool) := f x y)
#expect Exp.fix (close
          (Exp.lam (close
            (Exp.lam (close
              (app (app (.fvar 0) (.fvar 1)) (.fvar 2))
              2))
            1))
          0)

-- annotation inside let body
#elabpl pl(let (x : int) := #1; (x : int))
#expect app
          (Exp.lam (close (Exp.annotated .int (.fvar 0)) 0))
          (lit (.int 1))

-- annotated value in operational position
#elabpl pl(fst(((#1, #2) : int × int)))
#expect fst (Exp.annotated (.prod .int .int) (pair (lit (.int 1)) (lit (.int 2))))

#elabpl pl((fun x, x : int → int) #1)
#expect app
          (Exp.annotated (.arrow .int .int)
            (Exp.lam (close (.fvar 0) 0)))
          (lit (.int 1))

-- store/load with annotations
#elabpl pl(alloc((#0 : int)))
#expect alloc (Exp.annotated .int (lit (.int 0)))

#elabpl pl(!(r : ref(int)))
#expect load (Exp.annotated (.ref .int) (.fvar 0))

/-! ## Fresh literal-application and edge cases -/

-- application where function position is a literal
#elabpl pl(#0 x)
#expect app (lit (.int 0)) (.fvar 0)

-- pair-projection-then-application
#elabpl pl(fst(p) x)
#expect app (fst (.fvar 0)) (.fvar 1)

-- shorthands compose with operators
#elabpl pl(#true && #false)
#expect binop .and (lit (.bool true)) (lit (.bool false))

-- store binds tighter than sequencing
#elabpl pl(x ← #1; e2)
#expect app (Exp.lam (.fvar 1)) (store (.fvar 0) (lit (.int 1)))

/-! ## `let!` destructuring — bindings allocate atoms via `projectPattern` -/

-- simple variable pattern: bindAtom=0, patAtom(x)=1, body(x)=fvar 1; rhs #1 no fvars
#elabpl pl(let! x := #1; x)
#expect Exp.case
          (Exp.scrut (lit (.int 1)) Pat.wildcard)
          (Exp.lam
            (close
              (app (Exp.lam (close (.fvar 1) 1)) (.fvar 0))
              0))
          (Exp.lam Exp.fail)

-- wildcard: bindAtom=0, body x=fvar 1, rhs e=fvar 2
#elabpl pl(let! _ := e; x)
#expect Exp.case
          (Exp.scrut (.fvar 2) Pat.wildcard)
          (Exp.lam (close (.fvar 1) 0))
          (Exp.lam Exp.fail)

-- literal pattern: bindAtom=0, body x=fvar 1, rhs e=fvar 2
#elabpl pl(let! #(.int 1) := e; x)
#expect Exp.case
          (Exp.scrut (.fvar 2) (Pat.lit (.int 1)))
          (Exp.lam (close (.fvar 1) 0))
          (Exp.lam Exp.fail)

-- inl pattern: bindAtom=0, patAtom(x)=1, body x=fvar 1, rhs e=fvar 2
#elabpl pl(let! inl(x) := e; x)
#expect Exp.case
          (Exp.scrut (.fvar 2) (Pat.inl .wildcard))
          (Exp.lam
            (close
              (app (Exp.lam (close (.fvar 1) 1)) (.fvar 0))
              0))
          (Exp.lam Exp.fail)

-- Scrut with annotated pattern (annotation discarded)
#elabpl pl(scrut x with (y : int))
#expect Exp.scrut (.fvar 0) Pat.wildcard

/-! ## `case` chain — each arm allocates a fresh __bind atom -/

-- single-arm case: scrutAtom=0, bindAtom=1, patAtom(x)=2, rhs e=fvar 3
#elabpl pl(case e | inl(x) => x)
#expect app
          (Exp.lam (close
            (Exp.case
              (Exp.scrut (.fvar 0) (Pat.inl .wildcard))
              (Exp.lam (close
                (app (Exp.lam (close (.fvar 2) 2)) (.fvar 1))
                1))
              (Exp.lam Exp.fail))
            0))
          (.fvar 3)
