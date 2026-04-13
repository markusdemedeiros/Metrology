import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation
/-
open ProbLang Exp Ty

/-! # Test harness for the LN surface-syntax elaborator.

Checks that every `pl(...)` form produces the expected LN `Exp` AST. To
keep the expected RHSs readable we use a small set of helpers:

* `varN s` : free variable whose atom is `(hash s).toNat`.
* `lamBody s body` : `lamN s none (close body (varN-atom s))`.
* `fixBody s body` : `fixN s none (close body (varN-atom s))`.
* `lamBodyTy s τ body` / `fixBodyTy s τ body` : typed variants.
* `lamAnon body` / `fixAnon body` : anonymous (`_`) binders — no close.

Tests in this file rely on the **top-level free-var** convention: any
identifier that's not captured by a surrounding `fun`/`rec`/`let`
binding maps to `fvar ((hash name).toNat)`. Internally bound identifiers
are closed via `close`, so shape-matching via these helpers works.
-/

/-- Macro that expands `nameAtom!"x"` to the concrete `Nat` atom for `"x"`.
    `hash` on `Lean.Name` is an `@[extern]` primitive that does NOT reduce
    via `rfl`/`simp`, so we evaluate it at macro-expansion time and emit a
    concrete `Nat` literal. Must match `atomOf` in `Notation.lean`. -/
macro "nameAtom!" s:str : term => do
  let n := (hash (Lean.Name.mkSimple s.getString)).toNat
  return Lean.Syntax.mkNatLit n

/-- Free-variable shorthand: `varN! "x"` = `Exp.fvar <atom>` with the atom inlined. -/
macro "varN!" s:str : term => `(Exp.fvar (nameAtom! $s))

/-- Lambda with name hint and close over the atom for `s`. -/
macro "lamBody!" s:str body:term : term =>
  `(Exp.lamN $s none (Exp.close $body (nameAtom! $s)))

macro "fixBody!" s:str body:term : term =>
  `(Exp.fixN $s none (Exp.close $body (nameAtom! $s)))

macro "lamBodyTy!" s:str τ:term body:term : term =>
  `(Exp.lamN $s (some $τ) (Exp.close $body (nameAtom! $s)))

macro "fixBodyTy!" s:str τ:term body:term : term =>
  `(Exp.fixN $s (some $τ) (Exp.close $body (nameAtom! $s)))

macro "lamAnon!" body:term : term => `(Exp.lamN "_" none $body)

/-- Check that a ProbLang expression elaborates to the expected AST. -/
macro "#elabpl " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : $lhs = $rhs := by rfl)

-- Reserved keywords are rejected in expression position
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
-- Reserved keywords are rejected in binder position
/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun fst, x) : Exp)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun inl, x) : Exp)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rec f rand := x) : Exp)

variable (e e1 e2 : Exp)

-- Literals
#elabpl pl(#(.int 1))
#expect lit (.int 1)

#elabpl pl(x)
#expect varN "x"

-- Arithmetic: * binds tighter than +
#elabpl pl(#(.int 1) + #(.int 2))
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#(.int 1) + #(.int 2) * #(.int 3))
#expect binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

-- Load binds tighter than +
#elabpl pl(!x + #(.int 1))
#expect binop .plus (load (varN "x")) (lit (.int 1))

-- Functions
#elabpl pl(fun f, f)
#expect lamBody "f" (varN "f")

#elabpl pl(fun f x, f x)
#expect lamBody "f" (lamBody "x" (app (varN "f") (varN "x")))

#elabpl pl(rec f x := f x)
#expect fixBody "f" (lamBody "x" (app (varN "f") (varN "x")))

-- Heap
#elabpl pl(alloc(#(.int 0)))
#expect alloc (lit (.int 0))

#elabpl pl(!x)
#expect load (varN "x")

#elabpl pl(x ← #(.int 1))
#expect store (varN "x") (lit (.int 1))

-- Probabilistic
#elabpl pl(tape(#(.int 10)))
#expect .tape (lit (.int 10))

#elabpl pl(rand(#(.int 10), #.unit))
#expect rand (lit (.int 10)) (lit .unit)

-- Pairs and sums
#elabpl pl((x, y))
#expect pair (varN "x") (varN "y")

#elabpl pl(fst((x, y)))
#expect fst (pair (varN "x") (varN "y"))

#elabpl pl(inl(x))
#expect inl (varN "x")

-- Operator associativity and precedence
#elabpl pl(#(.int 1) + #(.int 2) + #(.int 3))
#expect binop .plus (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#(.int 1) - #(.int 2) - #(.int 3))
#expect binop .minus (binop .minus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#(.int 1) - #(.int 2) * #(.int 3))
#expect binop .minus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

#elabpl pl((#(.int 1) + #(.int 2)) * #(.int 3))
#expect binop .mult (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(-x + y)
#expect binop .plus (unop .minus (varN "x")) (varN "y")

#elabpl pl(~x && y)
#expect binop .and (unop .neg (varN "x")) (varN "y")

#elabpl pl(x && y || z)
#expect binop .or (binop .and (varN "x") (varN "y")) (varN "z")

#elabpl pl(x + y = z)
#expect binop .eq (binop .plus (varN "x") (varN "y")) (varN "z")

-- Escape hatch {}
#elabpl pl({e})
#expect e

#elabpl pl({e1} + {e2})
#expect binop .plus e1 e2

-- Literals
#elabpl pl(#(.bool true))
#expect lit (.bool true)

#elabpl pl(#.unit)
#expect lit .unit

#elabpl pl(#1)
#expect lit (.int 1)

#elabpl pl(#0)
#expect lit (.int 0)

#elabpl pl(#42)
#expect lit (.int 42)

#elabpl pl(#true)
#expect lit (.bool true)

#elabpl pl(#false)
#expect lit (.bool false)

#elabpl pl(#1 + #2)
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#true && #false)
#expect binop .and (lit (.bool true)) (lit (.bool false))

-- Unary operators
#elabpl pl(~x)
#expect unop .neg (varN "x")

#elabpl pl(-x)
#expect unop .minus (varN "x")

-- Conditional
#elabpl pl(if x then y else z)
#expect cond (varN "x") (varN "y") (varN "z")

#elabpl pl(if x then y + z else w)
#expect cond (varN "x") (binop .plus (varN "y") (varN "z")) (varN "w")

-- Sequencing
#elabpl pl(e1; e2)
#expect app (lamAnon (varN "e2")) (varN "e1")

#elabpl pl(let x := e; x)
#expect app (lamBody "x" (varN "x")) (varN "e")

#elabpl pl(let x := #(.int 1); x + x)
#expect app (lamBody "x" (binop .plus (varN "x") (varN "x"))) (lit (.int 1))

-- Application is left-associative
#elabpl pl(f x y)
#expect app (app (varN "f") (varN "x")) (varN "y")

#elabpl pl(f x + g y)
#expect binop .plus (app (varN "f") (varN "x")) (app (varN "g") (varN "y"))

-- multi-arg fun desugars to nested lam
#elabpl pl(fun x y z, x)
#expect lamBody "x" (lamBody "y" (lamBody "z" (varN "x")))

-- Pairs
#elabpl pl(snd((x, y)))
#expect snd (pair (varN "x") (varN "y"))

#elabpl pl((x, y, z))
#expect pair (varN "x") (pair (varN "y") (varN "z"))

-- Sums
#elabpl pl(inr(x))
#expect inr (varN "x")

-- Store binds tighter than sequencing
#elabpl pl(x ← #(.int 1); e2)
#expect app (lamAnon (varN "e2")) (store (varN "x") (lit (.int 1)))

-- rec with multiple args
#elabpl pl(rec f x y := f x y)
#expect fixBody "f" (lamBody "x" (lamBody "y" (app (app (varN "f") (varN "x")) (varN "y"))))

#elabpl pl(rec f x y z := f x y z)
#expect fixBody "f" (lamBody "x" (lamBody "y" (lamBody "z"
           (app (app (app (varN "f") (varN "x")) (varN "y")) (varN "z")))))

-- fun vs rec
#elabpl pl(fun x, x)
#expect lamBody "x" (varN "x")

#elabpl pl(rec f x := x)
#expect fixBody "f" (lamBody "x" (varN "x"))

-- anonymous argument binder _
#elabpl pl(fun _, x)
#expect lamAnon (varN "x")

#elabpl pl(rec f _ := f)
#expect fixBody "f" (lamAnon (varN "f"))

-- snd with nested triple
#elabpl pl(snd((x, y, z)))
#expect snd (pair (varN "x") (pair (varN "y") (varN "z")))

-- let + sequencing
#elabpl pl(let x := e1; e2; e3)
#expect app (lamBody "x" (app (lamAnon (varN "e3")) (varN "e2"))) (varN "e1")

-- xor precedence
#elabpl pl(x && y ^^ z)
#expect binop .xor (binop .and (varN "x") (varN "y")) (varN "z")

#elabpl pl(x ^^ y || z)
#expect binop .or (binop .xor (varN "x") (varN "y")) (varN "z")

#elabpl pl(!x * y)
#expect binop .mult (load (varN "x")) (varN "y")

#elabpl pl(f x * g y)
#expect binop .mult (app (varN "f") (varN "x")) (app (varN "g") (varN "y"))

#elabpl pl(x ← y; z)
#expect app (lamAnon (varN "z")) (store (varN "x") (varN "y"))

-- nested let scoping
#elabpl pl(let x := e1; let y := e2; x + y)
#expect app
          (lamBody "x"
            (app
              (lamBody "y" (binop .plus (varN "x") (varN "y")))
              (varN "e2")))
          (varN "e1")

-- escape hatch inside compound expressions
#elabpl pl(let x := {e}; x)
#expect app (lamBody "x" (varN "x")) e

#elabpl pl(if {e} then x else y)
#expect cond e (varN "x") (varN "y")

-- Note: `pl(fun x, {e})` escapes to Lean-level `e`; since we don't know that
-- `e` refers to no Lean-level `x`, we simply close over the atom. The result
-- is `lamBody "x" e` which may be a no-op close (if `e` has no `fvar <atom>`).
#elabpl pl(fun x, {e})
#expect lamBody "x" e

-- Variable shadowing — NOTE: under the current elaborator both binders use
-- the same atom (see Task #14), so the outer close captures both binder
-- occurrences in the body. This test records current behavior.
#elabpl pl(let x := e; let x := x; x)
#expect app (lamBody "x" (app (lamBody "x" (varN "x")) (varN "x"))) (varN "e")

#elabpl pl(fun x, fun x, x)
#expect lamBody "x" (lamBody "x" (varN "x"))

#elabpl pl(rec f x := rec f x := f x)
#expect fixBody "f" (lamBody "x" (fixBody "f" (lamBody "x" (app (varN "f") (varN "x")))))

-- rec self-name and arg name same identifier
#elabpl pl(rec x x := x x)
#expect fixBody "x" (lamBody "x" (app (varN "x") (varN "x")))

-- if branches contain let/fun
#elabpl pl(if x then let y := e; y else z)
#expect cond (varN "x") (app (lamBody "y" (varN "y")) (varN "e")) (varN "z")

-- application of literals and computed things
#elabpl pl(#(.int 0) x)
#expect app (lit (.int 0)) (varN "x")

#elabpl pl(fst(p) x)
#expect app (fst (varN "p")) (varN "x")

#elabpl pl(-(x + y))
#expect unop .minus (binop .plus (varN "x") (varN "y"))

#elabpl pl(~~x)
#expect unop .neg (unop .neg (varN "x"))

#elabpl pl(fst(p) ← x)
#expect store (fst (varN "p")) (varN "x")

#elabpl pl(!(!x))
#expect load (load (varN "x"))

#elabpl pl(alloc(alloc(x)))
#expect alloc (alloc (varN "x"))

#elabpl pl((inl(x), inr(y)))
#expect pair (inl (varN "x")) (inr (varN "y"))

#elabpl pl(fst(snd((x, (y, z)))))
#expect fst (snd (pair (varN "x") (pair (varN "y") (varN "z"))))

-- = is right-associative
#elabpl pl(x = y = z)
#expect binop .eq (varN "x") (binop .eq (varN "y") (varN "z"))

#elabpl pl(if x && y then z else w)
#expect cond (binop .and (varN "x") (varN "y")) (varN "z") (varN "w")

#elabpl pl(e1; e2; e3)
#expect app (lamAnon (app (lamAnon (varN "e3")) (varN "e2"))) (varN "e1")

#elabpl pl(-x - y)
#expect binop .minus (unop .minus (varN "x")) (varN "y")

#elabpl pl(x - -y)
#expect binop .minus (varN "x") (unop .minus (varN "y"))

#elabpl pl(~(x = y))
#expect unop .neg (binop .eq (varN "x") (varN "y"))

#elabpl pl(x && y = z)
#expect binop .eq (binop .and (varN "x") (varN "y")) (varN "z")

#elabpl pl(x || y = z)
#expect binop .eq (binop .or (varN "x") (varN "y")) (varN "z")

#elabpl pl((fun x, x) y)
#expect app (lamBody "x" (varN "x")) (varN "y")

#elabpl pl((rec f x := f x) y)
#expect app (fixBody "f" (lamBody "x" (app (varN "f") (varN "x")))) (varN "y")

#elabpl pl(fun x, fun y, x)
#expect lamBody "x" (lamBody "y" (varN "x"))

-- let binding of a fun
#elabpl pl(let f := fun x, x; f)
#expect app (lamBody "f" (varN "f")) (lamBody "x" (varN "x"))

-- let binding of a pair
#elabpl pl(let p := (x, y); fst(p))
#expect app (lamBody "p" (fst (varN "p"))) (pair (varN "x") (varN "y"))

-- nested ifs
#elabpl pl(if (if b then x else y) then z else w)
#expect cond (cond (varN "b") (varN "x") (varN "y")) (varN "z") (varN "w")

#elabpl pl(if x then (if y then a else b) else c)
#expect cond (varN "x") (cond (varN "y") (varN "a") (varN "b")) (varN "c")

#elabpl pl(x ← alloc(y))
#expect store (varN "x") (alloc (varN "y"))

#elabpl pl(alloc(fun x, x))
#expect alloc (lamBody "x" (varN "x"))

#elabpl pl(rand(tape(n), #.unit))
#expect rand (.tape (varN "n")) (lit .unit)

-- Failure
#elabpl pl(fail)
#expect Exp.fail

-- Assert
#elabpl pl(assert(b))
#expect cond (varN "b") (lit .unit) Exp.fail

-- tape and rand in a let
#elabpl pl(let t := tape(n); rand(t, #.unit))
#expect app (lamBody "t" (rand (varN "t") (lit .unit))) (.tape (varN "n"))

#elabpl pl((!f) x)
#expect app (load (varN "f")) (varN "x")

#elabpl pl(p ← f x)
#expect store (varN "p") (app (varN "f") (varN "x"))

#elabpl pl(fst(f x))
#expect fst (app (varN "f") (varN "x"))

#elabpl pl(inl(if b then x else y))
#expect inl (cond (varN "b") (varN "x") (varN "y"))

-- deeply nested pairs
#elabpl pl((a, b, c, d))
#expect pair (varN "a") (pair (varN "b") (pair (varN "c") (varN "d")))

-- Type syntax
#elabpl pl_ty(int)
#expect .int

#elabpl pl_ty(bool)
#expect .bool

#elabpl pl_ty(unit)
#expect .unit

#elabpl pl_ty(int × bool)
#expect .prod .int .bool

#elabpl pl_ty(int + bool)
#expect .sum .int .bool

#elabpl pl_ty(int → bool)
#expect .arrow .int .bool

#elabpl pl_ty(ref(int))
#expect .ref .int

#elabpl pl_ty(int × bool × unit)
#expect .prod .int (.prod .bool .unit)

#elabpl pl_ty(int → bool → unit)
#expect .arrow .int (.arrow .bool .unit)

#elabpl pl_ty(int + bool + unit)
#expect .sum .int (.sum .bool .unit)

#elabpl pl_ty(int × bool + unit)
#expect .sum (.prod .int .bool) .unit

#elabpl pl_ty(int × bool → unit)
#expect .arrow (.prod .int .bool) .unit

#elabpl pl_ty(int × (bool + unit))
#expect .prod .int (.sum .bool .unit)

#elabpl pl_ty(ref(int × bool))
#expect .ref (.prod .int .bool)

#elabpl pl_ty(tape)
#expect Ty.tape

-- Expression type annotations (phantom)
#elabpl pl((x : int))
#expect Exp.annotated .int (varN "x")

#elabpl pl((#1 : int))
#expect Exp.annotated .int (lit (.int 1))

#elabpl pl((x + y : int))
#expect Exp.annotated .int (binop .plus (varN "x") (varN "y"))

-- Typed binders
#elabpl pl(fun (x : int), x)
#expect lamBodyTy "x" .int (varN "x")

#elabpl pl(rec f (x : int) := f x)
#expect fixBody "f" (lamBodyTy "x" .int (app (varN "f") (varN "x")))

#elabpl pl(let (x : int) := #1; x)
#expect app (lamBodyTy "x" .int (varN "x")) (lit (.int 1))

-- Mixed typed/untyped
#elabpl pl(fun (x : int) y, x + y)
#expect lamBodyTy "x" .int (lamBody "y" (binop .plus (varN "x") (varN "y")))

#elabpl pl_ty(int + bool → unit)
#expect .arrow (.sum .int .bool) .unit

#elabpl pl_ty(ref(int) × ref(bool))
#expect .prod (.ref .int) (.ref .bool)

#elabpl pl_ty(ref(ref(int)))
#expect .ref (.ref .int)

#elabpl pl((x : int → bool))
#expect Exp.annotated (.arrow .int .bool) (varN "x")

#elabpl pl((x : int × bool))
#expect Exp.annotated (.prod .int .bool) (varN "x")

#elabpl pl(((x : int) : int))
#expect Exp.annotated .int (Exp.annotated .int (varN "x"))

#elabpl pl(rec f (x : int) (y : bool) := f x y)
#expect fixBody "f" (lamBodyTy "x" .int (lamBodyTy "y" .bool
           (app (app (varN "f") (varN "x")) (varN "y"))))

-- Annotation in let body
#elabpl pl(let (x : int) := #1; (x : int))
#expect app (lamBodyTy "x" .int (Exp.annotated .int (varN "x"))) (lit (.int 1))

#elabpl pl(fst(((#1, #2) : int × int)))
#expect fst (Exp.annotated (.prod .int .int) (pair (lit (.int 1)) (lit (.int 2))))

#elabpl pl((fun x, x : int → int) #1)
#expect app (Exp.annotated (.arrow .int .int) (lamBody "x" (varN "x"))) (lit (.int 1))

#elabpl pl((fun _, fail) #1)
#expect app (lamAnon Exp.fail) (lit (.int 1))

#elabpl pl(fail; x)
#expect app (lamAnon (varN "x")) Exp.fail

#elabpl pl(let x := (let y := #1; y); x)
#expect app (lamBody "x" (varN "x")) (app (lamBody "y" (varN "y")) (lit (.int 1)))

#elabpl pl(alloc((#0 : int)))
#expect alloc (Exp.annotated .int (lit (.int 0)))

#elabpl pl(!(r : ref(int)))
#expect load (Exp.annotated (.ref .int) (varN "r"))

-- Patterns — identifier patterns lower to wildcard (bindings are handled at
-- destructure sites, not in Pat itself).
#elabpl pl_pat(x)
#expect Pat.wildcard

#elabpl pl_pat(_)
#expect Pat.wildcard

#elabpl pl_pat(#(.int 1))
#expect Pat.lit (.int 1)

#elabpl pl_pat(#.unit)
#expect Pat.lit .unit

#elabpl pl_pat((x, y))
#expect Pat.pair .wildcard .wildcard

#elabpl pl_pat(inl(x))
#expect Pat.inl .wildcard

#elabpl pl_pat(inr(y))
#expect Pat.inr .wildcard

#elabpl pl_pat((x : int))
#expect Pat.wildcard

#elabpl pl_pat(inl((x, y)))
#expect Pat.inl (.pair .wildcard .wildcard)

#elabpl pl_pat((inl(x), inr(y)))
#expect Pat.pair (.inl .wildcard) (.inr .wildcard)

#elabpl pl(scrut x with y)
#expect Exp.scrut (varN "x") .wildcard

#elabpl pl(scrut inl(#1) with inl(x))
#expect Exp.scrut (inl (lit (.int 1))) (.inl .wildcard)

#elabpl pl(scrut (x, y) with (a, b))
#expect Exp.scrut (pair (varN "x") (varN "y")) (.pair .wildcard .wildcard)

#elabpl pl(scrut x with (y : int))
#expect Exp.scrut (varN "x") Pat.wildcard

end
-/
