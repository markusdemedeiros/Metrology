import Metrology.ProbLang.Syntax
import Metrology.ProbLang.Notation

open ProbLang Exp Binder Ty Annot

/-- Check that a ProbLang expression elaborates to the expected AST.
    Usage:
      #elabpl pl(#1 + #2)
      #expect binop .plus (lit (.int 1)) (lit (.int 2))
-/
macro "#elabpl " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : $lhs = $rhs := rfl)

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

-- Literals and variables
#elabpl pl(#(.int 1))
#expect lit (.int 1)

#elabpl pl(x)
#expect var "x"

-- Arithmetic: * binds tighter than +
#elabpl pl(#(.int 1) + #(.int 2))
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#(.int 1) + #(.int 2) * #(.int 3))
#expect binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

-- Load binds tighter than +
#elabpl pl(!x + #(.int 1))
#expect binop .plus (load (var "x")) (lit (.int 1))

-- Functions
#elabpl pl(fun f, f)
#expect letrec .anon (.named "f") (var "f")

#elabpl pl(fun f x, f x)
#expect letrec .anon (.named "f") (letrec .anon (.named "x") (app (var "f") (var "x")))

#elabpl pl(rec f x := f x)
#expect letrec (.named "f") (.named "x") (app (var "f") (var "x"))

-- Heap
#elabpl pl(alloc(#(.int 0)))
#expect alloc (lit (.int 0))

#elabpl pl(!x)
#expect load (var "x")

#elabpl pl(x ← #(.int 1))
#expect store (var "x") (lit (.int 1))

-- Probabilistic
#elabpl pl(tape(#(.int 10)))
#expect .tape (lit (.int 10))

#elabpl pl(rand(#(.int 10), #.unit))
#expect rand (lit (.int 10)) (lit .unit)

-- Pairs and sums
#elabpl pl((x, y))
#expect pair (var "x") (var "y")

#elabpl pl(fst((x, y)))
#expect fst (pair (var "x") (var "y"))

#elabpl pl(inl(x))
#expect inl (var "x")

-- [commented out: case tests, to be replaced by match+case]
-- example : pl(case inl(x) | l => l | r => r) =
--     Exp.case (inl (var "x"))
--       (letrec .anon (.named "l") (var "l"))
--       (letrec .anon (.named "r") (var "r")) := rfl
-- example :
--   pl(case inl(x)
--      | l => l
--      | r => r) =
--   Exp.case (inl (var "x"))
--     (letrec .anon (.named "l") (var "l"))
--     (letrec .anon (.named "r") (var "r")) := rfl



-- Operator associativity and precedence
-- + is left-associative
#elabpl pl(#(.int 1) + #(.int 2) + #(.int 3))
#expect binop .plus (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

-- - is left-associative likewise
#elabpl pl(#(.int 1) - #(.int 2) - #(.int 3))
#expect binop .minus (binop .minus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

-- * binds tighter than -
#elabpl pl(#(.int 1) - #(.int 2) * #(.int 3))
#expect binop .minus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

-- parentheses override precedence
#elabpl pl((#(.int 1) + #(.int 2)) * #(.int 3))
#expect binop .mult (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

-- unary minus binds tighter than binary +
#elabpl pl(-x + y)
#expect binop .plus (unop .minus (var "x")) (var "y")

-- ~ binds tighter than &&
#elabpl pl(~x && y)
#expect binop .and (unop .neg (var "x")) (var "y")

-- && binds tighter than ||
#elabpl pl(x && y || z)
#expect binop .or (binop .and (var "x") (var "y")) (var "z")

-- = has lower precedence than +
#elabpl pl(x + y = z)
#expect binop .eq (binop .plus (var "x") (var "y")) (var "z")

-- Escape hatch {}: splice a Lean term directly
#elabpl pl({e})
#expect e

#elabpl pl({e1} + {e2})
#expect binop .plus e1 e2

-- Literals
#elabpl pl(#(.bool true))
#expect lit (.bool true)

#elabpl pl(#.unit)
#expect lit .unit

-- Literal shorthands
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

-- Shorthands compose with operators
#elabpl pl(#1 + #2)
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#true && #false)
#expect binop .and (lit (.bool true)) (lit (.bool false))

-- Unary operators
#elabpl pl(~x)
#expect unop .neg (var "x")

#elabpl pl(-x)
#expect unop .minus (var "x")

-- Conditional
#elabpl pl(if x then y else z)
#expect cond (var "x") (var "y") (var "z")

-- if-then-else is low precedence: body can contain operators
#elabpl pl(if x then y + z else w)
#expect cond (var "x") (binop .plus (var "y") (var "z")) (var "w")

-- Sequencing
#elabpl pl(e1; e2)
#expect app (letrec .anon .anon (var "e2")) (var "e1")

#elabpl pl(let x := e; x)
#expect (letrec anon (named "x") (var "x")).app (var "e")

#elabpl pl(let x := #(.int 1); x + x)
#expect (letrec anon (named "x") (binop BinOp.plus (var "x") (var "x"))).app (lit (BaseLit.int 1))

-- Application is left-associative
#elabpl pl(f x y)
#expect app (app (var "f") (var "x")) (var "y")

-- Application binds tighter than +
#elabpl pl(f x + g y)
#expect binop .plus (app (var "f") (var "x")) (app (var "g") (var "y"))

-- multi-arg fun desugars to nested letrec
#elabpl pl(fun x y z, x)
#expect letrec .anon (.named "x")
           (letrec .anon (.named "y")
             (letrec .anon (.named "z") (var "x")))

-- Pairs: snd and nested triples
#elabpl pl(snd((x, y)))
#expect snd (pair (var "x") (var "y"))

#elabpl pl((x, y, z))
#expect pair (var "x") (pair (var "y") (var "z"))

-- Sums
#elabpl pl(inr(x))
#expect inr (var "x")

-- Store binds tighter than sequencing
#elabpl pl(x ← #(.int 1); e2)
#expect app (letrec .anon .anon (var "e2"))
            (store (var "x") (lit (.int 1)))

-- rec with multiple args desugars to rec with single arg and inner fun
#elabpl pl(rec f x y := f x y)
#expect letrec (.named "f") (.named "x")
           (letrec .anon (.named "y")
             (app (app (var "f") (var "x")) (var "y")))

-- three-arg rec
#elabpl pl(rec f x y z := f x y z)
#expect letrec (.named "f") (.named "x")
           (letrec .anon (.named "y")
             (letrec .anon (.named "z")
               (app (app (app (var "f") (var "x")) (var "y")) (var "z"))))

-- fun uses .anon self-binder; rec uses .named
#elabpl pl(fun x, x)
#expect letrec .anon (.named "x") (var "x")

#elabpl pl(rec f x := x)
#expect letrec (.named "f") (.named "x") (var "x")

-- anonymous argument binder _
#elabpl pl(fun _, x)
#expect letrec .anon .anon (var "x")

#elabpl pl(rec f _ := f)
#expect letrec (.named "f") .anon (var "f")

-- snd with nested triple
#elabpl pl(snd((x, y, z)))
#expect snd (pair (var "x") (pair (var "y") (var "z")))

-- Sequencing with let: `let x := e1; e2; e3` parses as `let x := e1; (e2; e3)`
-- because let (prec 10) has higher precedence than ; (prec 5).
#elabpl pl(let x := e1; e2; e3)
#expect app (letrec .anon (.named "x")
               (app (letrec .anon .anon (var "e3")) (var "e2")))
             (var "e1")

-- xor precedence: ^^ binds tighter than ||, looser than &&
#elabpl pl(x && y ^^ z)
#expect binop .xor (binop .and (var "x") (var "y")) (var "z")

#elabpl pl(x ^^ y || z)
#expect binop .or (binop .xor (var "x") (var "y")) (var "z")

-- ! (load) binds tighter than *
#elabpl pl(!x * y)
#expect binop .mult (load (var "x")) (var "y")

-- application binds tighter than *
#elabpl pl(f x * g y)
#expect binop .mult (app (var "f") (var "x")) (app (var "g") (var "y"))

-- ← (store) binds tighter than ;;
#elabpl pl(x ← y; z)
#expect app (letrec .anon .anon (var "z"))
             (store (var "x") (var "y"))

-- nested let scoping: x is in scope in the body of the second let
#elabpl pl(let x := e1; let y := e2; x + y)
#expect app
           (letrec .anon (.named "x")
             (app
               (letrec .anon (.named "y")
                 (binop .plus (var "x") (var "y")))
               (var "e2")))
           (var "e1")

-- [commented out: case tests]
-- example : pl(case inr(x) | l => l | r => r) =
--     Exp.case (inr (var "x"))
--       (letrec .anon (.named "l") (var "l"))
--       (letrec .anon (.named "r") (var "r")) := rfl

-- escape hatch inside compound expressions
#elabpl pl(let x := {e}; x)
#expect app (letrec .anon (.named "x") (var "x")) e

#elabpl pl(if {e} then x else y)
#expect cond e (var "x") (var "y")

#elabpl pl(fun x, {e})
#expect letrec .anon (.named "x") e

-- [commented out: case tests]
-- example (e1 e2 : Exp) : pl(case {e1} | l => {e2} | r => r) =
--     Exp.case e1
--       (letrec .anon (.named "l") e2)
--       (letrec .anon (.named "r") (var "r")) := rfl

-- Variable shadowing: let x rebinds x; inner x refers to new binding
#elabpl pl(let x := e; let x := x; x)
#expect app
           (letrec .anon (.named "x")
             (app
               (letrec .anon (.named "x") (var "x"))
               (var "x")))
           (var "e")

#elabpl pl(fun x, fun x, x)
#expect letrec .anon (.named "x")
           (letrec .anon (.named "x") (var "x"))

#elabpl pl(rec f x := rec f x := f x)
#expect letrec (.named "f") (.named "x")
           (letrec (.named "f") (.named "x")
             (app (var "f") (var "x")))

-- rec self-name and arg name are the same identifier
#elabpl pl(rec x x := x x)
#expect letrec (.named "x") (.named "x") (app (var "x") (var "x"))

-- if branches contain let/fun (low-prec forms inside low-prec if)
#elabpl pl(if x then let y := e; y else z)
#expect cond (var "x")
           (app (letrec .anon (.named "y") (var "y")) (var "e"))
           (var "z")

-- [commented out: case tests]
-- example : pl(case inl(x) | l => e1; l | r => r) =
--     Exp.case (inl (var "x"))
--       (letrec .anon (.named "l")
--         (app (letrec .anon .anon (var "l")) (var "e1")))
--       (letrec .anon (.named "r") (var "r")) := rfl

-- application of a literal (function position need not be a variable)
#elabpl pl(#(.int 0) x)
#expect app (lit (.int 0)) (var "x")

-- applying a pair projection
#elabpl pl(fst(p) x)
#expect app (fst (var "p")) (var "x")

-- unary minus on a compound expression
#elabpl pl(-(x + y))
#expect unop .minus (binop .plus (var "x") (var "y"))

-- double negation
#elabpl pl(~~x)
#expect unop .neg (unop .neg (var "x"))

-- store into a computed address (address expression is non-trivial)
#elabpl pl(fst(p) ← x)
#expect store (fst (var "p")) (var "x")

-- load a loaded address (!(!x))
#elabpl pl(!(!x))
#expect load (load (var "x"))

-- alloc of an allocated value
#elabpl pl(alloc(alloc(x)))
#expect alloc (alloc (var "x"))

-- pair of sums
#elabpl pl((inl(x), inr(y)))
#expect pair (inl (var "x")) (inr (var "y"))

-- fst/snd of a pair of pairs (projection from nested structure)
#elabpl pl(fst(snd((x, (y, z)))))
#expect fst (snd (pair (var "x") (pair (var "y") (var "z"))))

-- = is non-associative: x = y = z should parse as x = (y = z)
-- (right-associative at same precedence 50)
#elabpl pl(x = y = z)
#expect binop .eq (var "x") (binop .eq (var "y") (var "z"))

-- if condition contains a boolean operator
#elabpl pl(if x && y then z else w)
#expect cond (binop .and (var "x") (var "y")) (var "z") (var "w")

-- sequencing three expressions: e1; e2; e3 is right-associative
#elabpl pl(e1; e2; e3)
#expect app (letrec .anon .anon
               (app (letrec .anon .anon (var "e3")) (var "e2")))
             (var "e1")

-- Unary minus vs binary minus: -x - y is ((-x) - y), not -(x - y)
#elabpl pl(-x - y)
#expect binop .minus (unop .minus (var "x")) (var "y")

-- Unary minus vs binary minus: x - -y
#elabpl pl(x - -y)
#expect binop .minus (var "x") (unop .minus (var "y"))

-- ~ applied to an equality
#elabpl pl(~(x = y))
#expect unop .neg (binop .eq (var "x") (var "y"))

-- = lower precedence than &&: x && y = z is (x && y) = z
#elabpl pl(x && y = z)
#expect binop .eq (binop .and (var "x") (var "y")) (var "z")

-- = lower precedence than ||
#elabpl pl(x || y = z)
#expect binop .eq (binop .or (var "x") (var "y")) (var "z")

-- application of a fun expression (immediately invoked lambda)
#elabpl pl((fun x, x) y)
#expect app (letrec .anon (.named "x") (var "x")) (var "y")

-- application of a rec expression
#elabpl pl((rec f x := f x) y)
#expect app (letrec (.named "f") (.named "x") (app (var "f") (var "x"))) (var "y")

-- fun body is itself a fun (currying spelled out)
#elabpl pl(fun x, fun y, x)
#expect letrec .anon (.named "x") (letrec .anon (.named "y") (var "x"))

-- let binding of a fun
#elabpl pl(let f := fun x, x; f)
#expect app (letrec .anon (.named "f") (var "f"))
             (letrec .anon (.named "x") (var "x"))

-- let binding of a pair
#elabpl pl(let p := (x, y); fst(p))
#expect app (letrec .anon (.named "p") (fst (var "p")))
             (pair (var "x") (var "y"))

-- [commented out: case tests]
-- example : pl(case (case inl(x) | l => inl(l) | r => inr(r)) | l => l | r => r) = ...
-- example : pl(case (if b then inl(x) else inr(y)) | l => l | r => r) = ...

-- if condition is itself an if
#elabpl pl(if (if b then x else y) then z else w)
#expect cond
           (cond (var "b") (var "x") (var "y"))
           (var "z") (var "w")

-- if branches are themselves ifs (dangling else resolved by grammar)
#elabpl pl(if x then (if y then a else b) else c)
#expect cond (var "x")
           (cond (var "y") (var "a") (var "b"))
           (var "c")

-- store value of a freshly allocated reference
#elabpl pl(x ← alloc(y))
#expect store (var "x") (alloc (var "y"))

-- alloc of a fun value
#elabpl pl(alloc(fun x, x))
#expect alloc (letrec .anon (.named "x") (var "x"))

-- rand applied to tape result
#elabpl pl(rand(tape(n), #.unit))
#expect rand (.tape (var "n")) (lit .unit)

-- Failure
#elabpl pl(fail)
#expect Exp.fail

-- [commented out: destructuring let tests, to be replaced by match+case]
-- example : ∃ n, pl(let (x, y) := e; x + y) = ... := ⟨_, rfl⟩
-- example : ∃ n, n ≠ "p" ∧ pl(let (x, y) := e; p) = ... := ⟨_, by decide, rfl⟩

-- [commented out: single-arm case tests, to be replaced by match+case]
-- example : pl(case inl(x) | inl(v) => v) = ... := rfl
-- example : pl(case inr(x) | inr(v) => v) = ... := rfl

-- Assert
#elabpl pl(assert(b))
#expect cond (var "b") (lit .unit) Exp.fail

-- tape and rand in a let
#elabpl pl(let t := tape(n); rand(t, #.unit))
#expect app
           (letrec .anon (.named "t")
             (rand (var "t") (lit .unit)))
           (.tape (var "n"))

-- applying the result of a load
#elabpl pl((!f) x)
#expect app (load (var "f")) (var "x")

-- storing the result of an application
#elabpl pl(p ← f x)
#expect store (var "p") (app (var "f") (var "x"))

-- fst of an application
#elabpl pl(fst(f x))
#expect fst (app (var "f") (var "x"))

-- inl of an if
#elabpl pl(inl(if b then x else y))
#expect inl (cond (var "b") (var "x") (var "y"))

-- deeply nested pairs (4-tuple)
#elabpl pl((a, b, c, d))
#expect pair (var "a")
           (pair (var "b")
             (pair (var "c") (var "d")))

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

-- × is right-associative
#elabpl pl_ty(int × bool × unit)
#expect .prod .int (.prod .bool .unit)

-- → is right-associative
#elabpl pl_ty(int → bool → unit)
#expect .arrow .int (.arrow .bool .unit)

-- + is right-associative
#elabpl pl_ty(int + bool + unit)
#expect .sum .int (.sum .bool .unit)

-- × binds tighter than +
#elabpl pl_ty(int × bool + unit)
#expect .sum (.prod .int .bool) .unit

-- × binds tighter than →
#elabpl pl_ty(int × bool → unit)
#expect .arrow (.prod .int .bool) .unit

-- parentheses override precedence
#elabpl pl_ty(int × (bool + unit))
#expect .prod .int (.sum .bool .unit)

-- ref and tape
#elabpl pl_ty(ref(int × bool))
#expect .ref (.prod .int .bool)

#elabpl pl_ty(tape)
#expect Ty.tape

-- Expression type annotations
#elabpl pl((x : int))
#expect annot (.ty .int) (var "x")

#elabpl pl((#1 : int))
#expect annot (.ty .int) (lit (.int 1))

#elabpl pl((x + y : int))
#expect annot (.ty .int) (binop .plus (var "x") (var "y"))

-- Typed binders in fun
#elabpl pl(fun (x : int), x)
#expect letrec .anon (.typed "x" .int) (var "x")

-- Typed binders in rec
#elabpl pl(rec f (x : int) := f x)
#expect letrec (.named "f") (.typed "x" .int) (app (var "f") (var "x"))

-- Typed binders in let
#elabpl pl(let (x : int) := #1; x)
#expect app (letrec .anon (.typed "x" .int) (var "x")) (lit (.int 1))

-- Mixed typed and untyped binders
#elabpl pl(fun (x : int) y, x + y)
#expect letrec .anon (.typed "x" .int)
           (letrec .anon (.named "y")
             (binop .plus (var "x") (var "y")))

-- + binds tighter than →
#elabpl pl_ty(int + bool → unit)
#expect .arrow (.sum .int .bool) .unit

-- ref inside compound types
#elabpl pl_ty(ref(int) × ref(bool))
#expect .prod (.ref .int) (.ref .bool)

-- nested ref
#elabpl pl_ty(ref(ref(int)))
#expect .ref (.ref .int)

-- Annotation with compound type
#elabpl pl((x : int → bool))
#expect annot (.ty (.arrow .int .bool)) (var "x")

-- Annotation with product type
#elabpl pl((x : int × bool))
#expect annot (.ty (.prod .int .bool)) (var "x")

-- Nested annotation
#elabpl pl(((x : int) : int))
#expect annot (.ty .int) (annot (.ty .int) (var "x"))

-- [commented out: typed binder in case arms test]
-- example : pl(case inl(#1) | (x : int) => x | (y : bool) => y) = ... := rfl

-- Multi-arg rec with all typed binders
#elabpl pl(rec f (x : int) (y : bool) := f x y)
#expect letrec (.named "f") (.typed "x" .int)
           (letrec .anon (.typed "y" .bool)
             (app (app (var "f") (var "x")) (var "y")))

-- [commented out: typed binder in single-arm case test]
-- example : pl(case inl(#1) | inl((v : int)) => v) = ... := rfl

-- Annotation inside a let body
#elabpl pl(let (x : int) := #1; (x : int))
#expect app (letrec .anon (.typed "x" .int)
               (annot (.ty .int) (var "x")))
             (lit (.int 1))


-- Annotated value in operational positions
#elabpl pl(fst(((#1, #2) : int × int)))
#expect fst (annot (.ty (.prod .int .int)) (pair (lit (.int 1)) (lit (.int 2))))

#elabpl pl((fun x, x : int → int) #1)
#expect app (annot (.ty (.arrow .int .int)) (letrec .anon (.named "x") (var "x")))
            (lit (.int 1))


-- fun with _ applied to a value
#elabpl pl((fun _, fail) #1)
#expect app (letrec .anon .anon Exp.fail) (lit (.int 1))

-- sequencing with fail
#elabpl pl(fail; x)
#expect app (letrec .anon .anon (var "x")) Exp.fail

-- [commented out: case tests]
-- example : pl(case inl(#1) | _ => #2 | _ => #3) = ... := rfl

-- deeply nested lets
#elabpl pl(let x := (let y := #1; y); x)
#expect app (letrec .anon (.named "x") (var "x"))
            (app (letrec .anon (.named "y") (var "y"))
                 (lit (.int 1)))

-- store/load with annotations
#elabpl pl(alloc((#0 : int)))
#expect alloc (annot (.ty .int) (lit (.int 0)))

#elabpl pl(!(r : ref(int)))
#expect load (annot (.ty (.ref .int)) (var "r"))

-- Variable patterns
#elabpl pl_pat(x)
#expect .var (.named "x")

#elabpl pl_pat(_)
#expect .var .anon

-- Literal patterns
#elabpl pl_pat(#(.int 1))
#expect .lit (.int 1)

#elabpl pl_pat(#.unit)
#expect .lit .unit

-- Pair patterns
#elabpl pl_pat((x, y))
#expect .pair (.var (.named "x")) (.var (.named "y"))

-- Sum patterns
#elabpl pl_pat(inl(x))
#expect .inl (.var (.named "x"))

#elabpl pl_pat(inr(y))
#expect .inr (.var (.named "y"))

-- Annotated patterns
#elabpl pl_pat((x : int))
#expect .annot (.ty .int) (.var (.named "x"))

-- Nested patterns
#elabpl pl_pat(inl((x, y)))
#expect .inl (.pair (.var (.named "x")) (.var (.named "y")))

#elabpl pl_pat((inl(x), inr(y)))
#expect .pair (.inl (.var (.named "x"))) (.inr (.var (.named "y")))

#elabpl pl(scrut x with y)
#expect Exp.scrut (var "x") (.var (.named "y"))

#elabpl pl(scrut inl(#1) with inl(x))
#expect Exp.scrut (inl (lit (.int 1))) (.inl (.var (.named "x")))

#elabpl pl(scrut (x, y) with (a, b))
#expect Exp.scrut (pair (var "x") (var "y"))
                  (.pair (.var (.named "a")) (.var (.named "b")))

-- Scrut with annotated pattern
#elabpl pl(scrut x with (y : int))
#expect Exp.scrut (var "x") (.annot (.ty .int) (.var (.named "y")))

-- Simple variable pattern: let! x := e; body
#elabpl pl(let! x := #1; x)
#expect Exp.case
           (Exp.scrut (lit (.int 1)) (.var (.named "x")))
           (letrec .anon (.named "__bind")
             (app (letrec .anon (.named "x") (var "x"))
                  (var "__bind")))
           (letrec .anon .anon Exp.fail)

-- Pair pattern: let! (x, y) := e; x + y
#elabpl pl(let! (x, y) := e; x + y)
#expect Exp.case (Exp.scrut (var "e") (.pair (.var (.named "x")) (.var (.named "y"))))
           (letrec .anon (.named "__bind")
             (app (letrec .anon (.named "x")
                    (app (letrec .anon (.named "y")
                           (binop .plus (var "x") (var "y")))
                         (snd (var "__bind"))))
                  (fst (var "__bind"))))
           (letrec .anon .anon Exp.fail)

-- Wildcard pattern: no binding
#elabpl pl(let! _ := e; x)
#expect Exp.case (Exp.scrut (var "e") (.var .anon))
           (letrec .anon (.named "__bind") (var "x"))
           (letrec .anon .anon Exp.fail)

-- inl pattern
#elabpl pl(let! inl(x) := e; x)
#expect Exp.case (Exp.scrut (var "e") (.inl (.var (.named "x"))))
           (letrec .anon (.named "__bind")
             (app (letrec .anon (.named "x") (var "x"))
                  (var "__bind")))
           (letrec .anon .anon Exp.fail)

-- Literal pattern (no bindings)
#elabpl pl(let! #(.int 1) := e; x)
#expect Exp.case (Exp.scrut (var "e") (.lit (.int 1)))
           (letrec .anon (.named "__bind") (var "x"))
           (letrec .anon .anon Exp.fail)

-- Two-arm case on a sum (binds scrutinee to __scrut, tries each arm)
#elabpl pl(case e | inl(x) => x | inr(y) => y)
#expect app
           (letrec .anon (.named "__scrut")
             (Exp.case (Exp.scrut (var "__scrut") (.inl (.var (.named "x"))))
               (letrec .anon (.named "__bind")
                 (app (letrec .anon (.named "x") (var "x"))
                      (var "__bind")))
               (letrec .anon .anon
                 (Exp.case (Exp.scrut (var "__scrut") (.inr (.var (.named "y"))))
                   (letrec .anon (.named "__bind")
                     (app (letrec .anon (.named "y") (var "y"))
                          (var "__bind")))
                   (letrec .anon .anon Exp.fail)))))
           (var "e")

-- Single-arm case
#elabpl pl(case e | inl(x) => x)
#expect app
           (letrec .anon (.named "__scrut")
             (Exp.case (Exp.scrut (var "__scrut") (.inl (.var (.named "x"))))
               (letrec .anon (.named "__bind")
                 (app (letrec .anon (.named "x") (var "x"))
                      (var "__bind")))
               (letrec .anon .anon Exp.fail)))
           (var "e")


-- Delaboration (unexpander) tests: check that Exp constructors print back as pl(...) syntax
/-- info: pl(#(BaseLit.int 1)) : Exp -/
#guard_msgs in #check (lit (.int 1) : Exp)

/-- info: pl(x) : Exp -/
#guard_msgs in #check (var "x" : Exp)

/-- info: pl((#(BaseLit.int 1) + (#(BaseLit.int 2) * #(BaseLit.int 3)))) : Exp -/
#guard_msgs in #check (binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3))) : Exp)

/-- info: pl(!x) : Exp -/
#guard_msgs in #check (load (var "x") : Exp)

/-- info: pl(fun f, f) : Exp -/
#guard_msgs in #check (letrec .anon (.named "f") (var "f") : Exp)

/-- info: pl(fun f, fun x, f x) : Exp -/
#guard_msgs in #check (letrec .anon (.named "f") (letrec .anon (.named "x") (app (var "f") (var "x"))) : Exp)

/-- info: pl(alloc(#(BaseLit.int 0))) : Exp -/
#guard_msgs in #check (alloc (lit (.int 0)) : Exp)

/-- info: pl(inl(x)) : Exp -/
#guard_msgs in #check (inl (var "x") : Exp)

/-- info: pl(inr(x)) : Exp -/
#guard_msgs in #check (inr (var "x") : Exp)

/-- info: pl(~x) : Exp -/
#guard_msgs in #check (unop .neg (var "x") : Exp)

/-- info: pl(-x) : Exp -/
#guard_msgs in #check (unop .minus (var "x") : Exp)

/-- info: pl(if x then y else z) : Exp -/
#guard_msgs in #check (cond (var "x") (var "y") (var "z") : Exp)

/-- info: pl((x, y)) : Exp -/
#guard_msgs in #check (pair (var "x") (var "y") : Exp)

/-- info: pl((x, y, z)) : Exp -/
#guard_msgs in #check (pair (var "x") (pair (var "y") (var "z")) : Exp)

/-- info: pl(fst(x)) : Exp -/
#guard_msgs in #check (fst (var "x") : Exp)

/-- info: pl(snd(x)) : Exp -/
#guard_msgs in #check (snd (var "x") : Exp)

-- [commented out: case unexpander test]
-- /-- info: pl(case inl(x) | l => l | r => r) : Exp -/
-- #guard_msgs in #check (Exp.case (inl (var "x"))
--     (letrec .anon (.named "l") (var "l"))
--     (letrec .anon (.named "r") (var "r")) : Exp)

/-- info: pl(x ← y) : Exp -/
#guard_msgs in #check (store (var "x") (var "y") : Exp)

/-- info: pl(tape(#(BaseLit.int 10))) : Exp -/
#guard_msgs in #check (.tape (lit (.int 10)) : Exp)

/-- info: pl(rand(#(BaseLit.int 10), #BaseLit.unit)) : Exp -/
#guard_msgs in #check (rand (lit (.int 10)) (lit .unit) : Exp)

/-- info: pl(fail) : Exp -/
#guard_msgs in #check (Exp.fail : Exp)

/-- info: pl(rec f x := f x) : Exp -/
#guard_msgs in #check (letrec (.named "f") (.named "x") (app (var "f") (var "x")) : Exp)

/-- info: pl(fun _, x) : Exp -/
#guard_msgs in #check (letrec .anon .anon (var "x") : Exp)

/-- info: pl(rec f _ := f) : Exp -/
#guard_msgs in #check (letrec (.named "f") .anon (var "f") : Exp)

/-- info: pl((x - y)) : Exp -/
#guard_msgs in #check (binop .minus (var "x") (var "y") : Exp)

/-- info: pl((x * y)) : Exp -/
#guard_msgs in #check (binop .mult (var "x") (var "y") : Exp)

/-- info: pl((x && y)) : Exp -/
#guard_msgs in #check (binop .and (var "x") (var "y") : Exp)

/-- info: pl((x || y)) : Exp -/
#guard_msgs in #check (binop .or (var "x") (var "y") : Exp)

/-- info: pl((x ^^ y)) : Exp -/
#guard_msgs in #check (binop .xor (var "x") (var "y") : Exp)

/-- info: pl((x = y)) : Exp -/
#guard_msgs in #check (binop .eq (var "x") (var "y") : Exp)

/-- info: pl(fun f, f x y) : Exp -/
#guard_msgs in #check (letrec .anon (.named "f")
    (app (app (var "f") (var "x")) (var "y")) : Exp)

/-- info: pl(e1; e2) : Exp -/
#guard_msgs in #check (app (letrec .anon .anon (var "e2")) (var "e1") : Exp)

-- Delaboration: let and sequencing
/-- info: pl(let x := e1; e2) : Exp -/
#guard_msgs in #check (app (letrec .anon (.named "x") (var "e2")) (var "e1") : Exp)

-- Delaboration: multi-arg rec
/-- info: pl(rec f x y := f x y) : Exp -/
#guard_msgs in #check (letrec (.named "f") (.named "x")
    (letrec .anon (.named "y")
      (app (app (var "f") (var "x")) (var "y"))) : Exp)

-- Delaboration: type annotations
/-- info: pl((x : int)) : Exp -/
#guard_msgs in #check (annot (.ty .int) (var "x") : Exp)

-- Delaboration: typed binders
/-- info: pl(fun(x : int), x) : Exp -/
#guard_msgs in #check (letrec .anon (.typed "x" .int) (var "x") : Exp)

/-- info: pl(rec f (x : int) := f x) : Exp -/
#guard_msgs in #check (letrec (.named "f") (.typed "x" .int) (app (var "f") (var "x")) : Exp)

-- Delaboration: types
/-- info: pl_ty(int × bool → unit) : Ty -/
#guard_msgs in #check (Ty.arrow (.prod .int .bool) .unit : Ty)

/-- info: pl_ty(ref(int)) : Ty -/
#guard_msgs in #check (Ty.ref .int : Ty)

-- Delaboration: compound type annotation
/-- info: pl((x : int → bool)) : Exp -/
#guard_msgs in #check (annot (.ty (.arrow .int .bool)) (var "x") : Exp)

-- Delaboration: product type
/-- info: pl_ty(int × bool) : Ty -/
#guard_msgs in #check (Ty.prod .int .bool : Ty)

-- Delaboration: sum type
/-- info: pl_ty(int + bool) : Ty -/
#guard_msgs in #check (Ty.sum .int .bool : Ty)


-- TODO: Move

-- Annotated literal is NOT a value (annotations are stripped during evaluation)
example : ¬(pl((#1 : int))).isValue := by simp [Exp.isValue_iff_isValueR]
-- Annotated pair is NOT a value
example : ¬(pl(((#1, #2) : int × int))).isValue := by simp [Exp.isValue_iff_isValueR]
-- Annotated non-value is not a value
example : ¬(pl((x + y : int))).isValue := by simp [Exp.isValue_iff_isValueR]

-- [commented out: typed binders in destructuring let test, to be replaced by match+case]
-- example : ∃ n, pl(let ((x : int), (y : bool)) := e; x + y) = ... := ⟨_, rfl⟩

-- TODO: Move

-- typed binder substitutes like named
example : Exp.subst (.typed "x" .int) (lit (.int 42)) (var "x") = lit (.int 42) := rfl
-- typed binder doesn't substitute other variables
example : Exp.subst (.typed "x" .int) (lit (.int 42)) (var "y") = var "y" := rfl
-- typed binder in letrec shadows correctly
example : (letrec .anon (.typed "x" .int) (var "x")).subst' "x" (lit (.int 99)) =
    letrec .anon (.typed "x" .int) (var "x") := rfl
-- typed binder as function name shadows correctly
example : (letrec (.typed "f" (.arrow .int .int)) (.named "x") (var "f")).subst' "f" (lit (.int 99)) =
    letrec (.typed "f" (.arrow .int .int)) (.named "x") (var "f") := rfl
-- non-shadowed variable is substituted under typed binder
example : (letrec .anon (.typed "x" .int) (var "y")).subst' "y" (lit (.int 7)) =
    letrec .anon (.typed "x" .int) (lit (.int 7)) := rfl

-- ---------------------------------------------------------------------------
-- Edge cases in existing syntax
-- ---------------------------------------------------------------------------


-- ---------------------------------------------------------------------------
-- Delaboration round-trips
-- ---------------------------------------------------------------------------

-- Typed binder in let round-trips
/-- info: pl(let (x : int) := #(BaseLit.int 1); x) : Exp -/
#guard_msgs in #check (app (letrec .anon (.typed "x" .int) (var "x")) (lit (.int 1)) : Exp)

-- Multi-arg fun with mixed typed/untyped: typed binder prevents collapsing
/-- info: pl(fun(x : int), fun y, (x + y)) : Exp -/
#guard_msgs in #check (letrec .anon (.typed "x" .int)
    (letrec .anon (.named "y")
      (binop .plus (var "x") (var "y"))) : Exp)

-- Annotated value inside a pair
/-- info: pl(((#(BaseLit.int 1) : int), #(BaseLit.int 2))) : Exp -/
#guard_msgs in #check (pair (annot (.ty .int) (lit (.int 1))) (lit (.int 2)) : Exp)

-- Annotation on a compound expression
/-- info: pl(((x + y) : int)) : Exp -/
#guard_msgs in #check (annot (.ty .int) (binop .plus (var "x") (var "y")) : Exp)

-- Nested type: ref of arrow
/-- info: pl_ty(ref(int → bool)) : Ty -/
#guard_msgs in #check (Ty.ref (.arrow .int .bool) : Ty)

-- Typed binder with anonymous function name round-trips
/-- info: pl(fun _, x) : Exp -/
#guard_msgs in #check (letrec .anon .anon (var "x") : Exp)

-- ---------------------------------------------------------------------------
-- Pattern syntax
-- ---------------------------------------------------------------------------


-- Delaboration: scrut round-trips
/-- info: pl(scrut x with y) : Exp -/
#guard_msgs in #check (Exp.scrut (var "x") (.var (.named "y")) : Exp)

/-- info: pl(scrut inl(x) with inl(y)) : Exp -/
#guard_msgs in #check (Exp.scrut (inl (var "x")) (.inl (.var (.named "y"))) : Exp)

-- Delaboration: pattern round-trips
/-- info: pl_pat((x, y)) : Pat -/
#guard_msgs in #check (Pat.pair (.var (.named "x")) (.var (.named "y")) : Pat)

/-- info: pl_pat(inl(x)) : Pat -/
#guard_msgs in #check (Pat.inl (.var (.named "x")) : Pat)

/-- info: pl_pat((x : int)) : Pat -/
#guard_msgs in #check (Pat.annot (.ty .int) (.var (.named "x")) : Pat)

-- -- Pair destructuring via case
-- #check (pl(case e | (x, y) => x + y) : Exp)
--
-- -- Nested pattern in case
-- #check (pl(case e | inl((x, y)) => x + y | inr(z) => z) : Exp)

-- Encryption / decryption notation
#elabpl pl(enc_aes128(p, iv, k))
#expect enc_aes128 (var "p") (var "iv") (var "k")

#elabpl pl(dec_aes128(c, iv, k))
#expect dec_aes128 (var "c") (var "iv") (var "k")

-- Delaboration round-trips
/-- info: pl(enc_aes128(p, iv, k)) : Exp -/
#guard_msgs in #check (enc_aes128 (var "p") (var "iv") (var "k") : Exp)

/-- info: pl(dec_aes128(c, iv, k)) : Exp -/
#guard_msgs in #check (dec_aes128 (var "c") (var "iv") (var "k") : Exp)
