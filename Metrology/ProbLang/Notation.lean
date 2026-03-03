import Lean.PrettyPrinter.Delaborator
import Metrology.ProbLang.Syntax

namespace ProbLang

open Lean Lean.PrettyPrinter Elab Parser

declare_syntax_cat pl_exp

/-- embedding ProbLang expressions into terms -/
syntax:max "pl(" pl_exp ")" : term
/-- embedding ProbLang binders into terms -/
syntax:max "pl_binder(" binderIdent ")" : term

/-- escaping back to Lean -/
syntax:max "{" term "}" : pl_exp
/-- embedding literals -/
syntax:max "#" term:max : pl_exp
/-- variables -/
syntax:max ident : pl_exp
/-- parentheses -/
syntax:max "(" pl_exp ")" : pl_exp

-- Operator precedences mirror Init.Notation
syntax:65 pl_exp:66 " + " pl_exp:65 : pl_exp
syntax:65 pl_exp:66 " - " pl_exp:65 : pl_exp
syntax:70 pl_exp:71 " * " pl_exp:70 : pl_exp
syntax:60 pl_exp:61 " && " pl_exp:60 : pl_exp
syntax:55 pl_exp:56 " || " pl_exp:55 : pl_exp
syntax:58 pl_exp:59 " ^^ " pl_exp:58 : pl_exp
syntax:50 pl_exp:50 " = " pl_exp:50 : pl_exp

/-- Booleans -/
syntax:10 "if " pl_exp " then " pl_exp " else " pl_exp : pl_exp
syntax:75 "~" pl_exp:75 : pl_exp
syntax:75 "-" pl_exp:75 : pl_exp

/-- Functions -/
syntax:100 pl_exp:100 ppSpace pl_exp:101 : pl_exp
syntax:10 "let " binderIdent " := " pl_exp:10 "; " pl_exp:1 : pl_exp
syntax:5 pl_exp:6 "; " pl_exp:5 : pl_exp
syntax:10 "fun" binderIdent+ ", " pl_exp:10 : pl_exp
syntax:10 "rec " binderIdent ppSpace binderIdent+ " := " pl_exp:10 : pl_exp

/-- Cases -/
syntax:max "(" pl_exp ", " pl_exp,+ ")" : pl_exp
syntax:100 "fst(" pl_exp ")" : pl_exp
syntax:100 "snd(" pl_exp ")" : pl_exp

syntax:100 "inl(" pl_exp ")" : pl_exp
syntax:100 "inr(" pl_exp ")" : pl_exp
syntax:10 "case " pl_exp " | " binderIdent " => " pl_exp " | " binderIdent " => " pl_exp : pl_exp

/-- State -/
syntax:100 "alloc(" pl_exp ")" : pl_exp
syntax:80 "!" pl_exp:80 : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80 : pl_exp

/-- Random -/
syntax:100 "tape(" pl_exp ")" : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")" : pl_exp

/-- elaborating binders -/
macro_rules
  | `(pl_binder(_))        => `(Binder.anon)
  | `(pl_binder($i:ident)) => `(Binder.named $(Syntax.mkStrLit i.getId.toString))

/-- elaborating expressions -/
macro_rules
  -- Parentheses (transparent)
  | `(pl(($e)))             => `(pl($e))
  -- Escape hatch
  | `(pl({$t}))             => pure t
  -- Literals
  | `(pl(# $e))             => `(Exp.lit $e)
  -- Variables
  | `(pl($i:ident))         => `(Exp.var $(Syntax.mkStrLit i.getId.toString))
  -- Binary operators
  | `(pl($e1 + $e2))        => `(Exp.binop .plus  pl($e1) pl($e2))
  | `(pl($e1 - $e2))        => `(Exp.binop .minus pl($e1) pl($e2))
  | `(pl($e1 * $e2))        => `(Exp.binop .mult  pl($e1) pl($e2))
  | `(pl($e1 && $e2))       => `(Exp.binop .and   pl($e1) pl($e2))
  | `(pl($e1 || $e2))       => `(Exp.binop .or    pl($e1) pl($e2))
  | `(pl($e1 ^^ $e2))       => `(Exp.binop .xor   pl($e1) pl($e2))
  | `(pl($e1 = $e2))        => `(Exp.binop .eq    pl($e1) pl($e2))
  -- Unary operators
  | `(pl(~$e))              => `(Exp.unop .neg   pl($e))
  | `(pl(-$e))              => `(Exp.unop .minus pl($e))
  -- Control flow
  | `(pl(if $ec then $et else $ef)) => `(Exp.cond pl($ec) pl($et) pl($ef))
  -- Application
  | `(pl($e1 $e2))          => `(Exp.app pl($e1) pl($e2))
  -- Desugaring: rec with multiple args, λ
  | `(pl(rec $f $x $xs* := $e)) => do
      if xs.size == 0 then
        `(Exp.letrec pl_binder($f) pl_binder($x) pl($e))
      else
        `(pl(rec $f $x := fun $xs*, $e))
  | `(pl(fun $x $xs* , $e)) => do
      if xs.size == 0 then
        `(pl(rec _ $x := $e))
      else
        `(pl(rec _ $x := fun $xs*, $e))
  -- Pairs
  | `(pl(($e1, $e2)))            => `(Exp.pair pl($e1) pl($e2))
  | `(pl(($e1, $e2, $e3,*)))     => `(pl(($e1, ($e2, $e3,*))))
  | `(pl(fst($e)))               => `(Exp.fst pl($e))
  | `(pl(snd($e)))               => `(Exp.snd pl($e))
  -- Sums
  | `(pl(inl($e)))               => `(Exp.inl pl($e))
  | `(pl(inr($e)))               => `(Exp.inr pl($e))
  | `(pl(case $ec | $il => $el | $ir => $er)) =>
      `(Exp.case pl($ec) pl(rec _ $il := $el) pl(rec _ $ir := $er))
  -- Heap
  | `(pl(alloc($e)))             => `(Exp.alloc pl($e))
  | `(pl(! $e))                  => `(Exp.load pl($e))
  | `(pl($e1 ← $e2))            => `(Exp.store pl($e1) pl($e2))
  -- Let and sequencing
  | `(pl(let $i := $e1; $e2))   => `(Exp.app (Exp.letrec .anon pl_binder($i) pl($e2)) pl($e1))
  | `(pl($e1; $e2))              => `(Exp.app (Exp.letrec .anon .anon pl($e2)) pl($e1))
  -- Probabilistic
  | `(pl(tape($e)))              => `(Exp.tape pl($e))
  | `(pl(rand($e1, $e2)))        => `(Exp.rand pl($e1) pl($e2))


/-- Strip the `pl(...)` wrapper to get a raw `pl_exp`, or fall back to `{t}` escape. -/
partial def unpackPLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_exp)
  | `(pl($e)) => `(pl_exp|$e)
  | `($t)     => `(pl_exp|{$t})

/-- Strip the `pl_binder(...)` wrapper to get a raw `binderIdent`. -/
partial def unpackPLBinder [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `Lean.binderIdent)
  | `(pl_binder($e)) => `(binderIdent|$e)
  | `($_)            => panic! "unknown binder"

/-- Flatten nested anonymous letrec into multi-arg `pl(fun ...)`. -/
partial def unexpFun : Term → UnexpandM Term
  | `(pl(rec _ $x := $e)) => do unexpFun (← `(pl(fun $x, $e)))
  | `(pl(fun $xs*, $e)) => do
    -- If body is also a fun, flatten by appending its binders
    match e with
    | `(pl(fun $ys*, $body)) => unexpFun (← `(pl(fun $xs* $ys*, $body)))
    | _ => return (← `(pl(fun $xs*, $e)))
  | x => return x

@[app_unexpander Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(pl_binder(_))

@[app_unexpander Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(pl_binder($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

@[app_unexpander Exp.var]
def unexpVar : Unexpander
  | `($_ $s:str) => `(pl($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

@[app_unexpander Exp.lit]
def unexpLit : Unexpander
  | `($_ $arg) => `(pl(# $arg))
  | _ => throw ()

@[app_unexpander Exp.binop]
def unexpBinop : Unexpander
  | `($_ BinOp.plus  $e1 $e2) => do `(pl(($(← unpackPLExp e1) + $(← unpackPLExp e2))))
  | `($_ BinOp.minus $e1 $e2) => do `(pl(($(← unpackPLExp e1) - $(← unpackPLExp e2))))
  | `($_ BinOp.mult  $e1 $e2) => do `(pl(($(← unpackPLExp e1) * $(← unpackPLExp e2))))
  | `($_ BinOp.and   $e1 $e2) => do `(pl(($(← unpackPLExp e1) && $(← unpackPLExp e2))))
  | `($_ BinOp.or    $e1 $e2) => do `(pl(($(← unpackPLExp e1) || $(← unpackPLExp e2))))
  | `($_ BinOp.xor   $e1 $e2) => do `(pl(($(← unpackPLExp e1) ^^ $(← unpackPLExp e2))))
  | `($_ BinOp.eq    $e1 $e2) => do `(pl(($(← unpackPLExp e1) = $(← unpackPLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.unop]
def unexpUnop : Unexpander
  | `($_ UnOp.neg   $e) => do `(pl(~$(← unpackPLExp e)))
  | `($_ UnOp.minus $e) => do `(pl(-$(← unpackPLExp e)))
  | _ => throw ()

@[app_unexpander Exp.cond]
def unexpCond : Unexpander
  | `($_ $ec $et $ef) => do
    `(pl(if $(← unpackPLExp ec) then $(← unpackPLExp et) else $(← unpackPLExp ef)))
  | _ => throw ()

@[app_unexpander Exp.letrec]
def unexpLetrec : Unexpander
  | `($_ $f $x $e) => do
    unexpFun (← `(pl(rec $(← unpackPLBinder f) $(← unpackPLBinder x) := $(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    `(pl($(← unpackPLExp e1) $(← unpackPLExp e2)))
  | _ => throw ()

partial def unexpPair' : Term → UnexpandM Term
  | `(pl(($e1, ($e2, $e3,*)))) => do unexpPair' (← `(pl(($e1, $e2, $e3,*))))
  | x => return x

@[app_unexpander Exp.pair]
def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' (← `(pl(($(← unpackPLExp e1), $(← unpackPLExp e2)))))
  | _ => throw ()

@[app_unexpander Exp.fst]
def unexpFst : Unexpander
  | `($_ $e) => do `(pl(fst($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.snd]
def unexpSnd : Unexpander
  | `($_ $e) => do `(pl(snd($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inl]
def unexpInl : Unexpander
  | `($_ $e) => do `(pl(inl($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inr]
def unexpInr : Unexpander
  | `($_ $e) => do `(pl(inr($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.case]
def unexpCase : Unexpander
  | `($_ $ec pl(fun $il, $el) pl(fun $ir, $er)) => do
    `(pl(case $(← unpackPLExp ec) | $il => $el | $ir => $er))
  | _ => throw ()

@[app_unexpander Exp.alloc]
def unexpAlloc : Unexpander
  | `($_ $e) => do `(pl(alloc($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.load]
def unexpLoad : Unexpander
  | `($_ $e) => do `(pl(!$(← unpackPLExp e)))
  | _ => throw ()

@[app_unexpander Exp.store]
def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(pl($(← unpackPLExp e1) ← $(← unpackPLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.tape]
def unexpTape : Unexpander
  | `($_ $e) => do `(pl(tape($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.rand]
def unexpRand : Unexpander
  | `($_ $e1 $e2) => do `(pl(rand($(← unpackPLExp e1), $(← unpackPLExp e2))))
  | _ => throw ()



section Tests

-- Literals and variables
example : pl(#(.int 1)) = Exp.lit (.int 1) := rfl
example : pl(x) = Exp.var "x" := rfl

-- Arithmetic: * binds tighter than +
example : pl(#(.int 1) + #(.int 2)) =
    Exp.binop .plus (Exp.lit (.int 1)) (Exp.lit (.int 2)) := rfl
example : pl(#(.int 1) + #(.int 2) * #(.int 3)) =
    Exp.binop .plus (Exp.lit (.int 1)) (Exp.binop .mult (Exp.lit (.int 2)) (Exp.lit (.int 3))) := rfl

-- Load binds tighter than +
example : pl(!x + #(.int 1)) =
    Exp.binop .plus (Exp.load (Exp.var "x")) (Exp.lit (.int 1)) := rfl

-- Functions
example : pl(fun f, f) = Exp.letrec .anon (.named "f") (Exp.var "f") := rfl
example : pl(fun f x, f x) =
    Exp.letrec .anon (.named "f") (Exp.letrec .anon (.named "x") (Exp.app (Exp.var "f") (Exp.var "x"))) := rfl
example : pl(rec f x := f x) =
    Exp.letrec (.named "f") (.named "x") (Exp.app (Exp.var "f") (Exp.var "x")) := rfl

-- Heap
example : pl(alloc(#(.int 0))) = Exp.alloc (Exp.lit (.int 0)) := rfl
example : pl(!x) = Exp.load (Exp.var "x") := rfl
example : pl(x ← #(.int 1)) = Exp.store (Exp.var "x") (Exp.lit (.int 1)) := rfl

-- Probabilistic
example : pl(tape(#(.int 10))) = Exp.tape (Exp.lit (.int 10)) := rfl
example : pl(rand(#(.int 10), #.unit)) = Exp.rand (Exp.lit (.int 10)) (Exp.lit .unit) := rfl

-- Pairs and sums
example : pl((x, y)) = Exp.pair (Exp.var "x") (Exp.var "y") := rfl
example : pl(fst((x, y))) = Exp.fst (Exp.pair (Exp.var "x") (Exp.var "y")) := rfl
example : pl(inl(x)) = Exp.inl (Exp.var "x") := rfl
example : pl(case inl(x) | l => l | r => r) =
    Exp.case (Exp.inl (Exp.var "x"))
      (Exp.letrec .anon (.named "l") (Exp.var "l"))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl
example :
  pl(case inl(x)
     | l => l
     | r => r) =
  Exp.case (Exp.inl (Exp.var "x"))
    (Exp.letrec .anon (.named "l") (Exp.var "l"))
    (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl



-- Operator associativity and precedence
-- + is right-associative (RHS has same precedence 65, so right wins)
example : pl(#(.int 1) + #(.int 2) + #(.int 3)) =
    Exp.binop .plus (Exp.lit (.int 1)) (Exp.binop .plus (Exp.lit (.int 2)) (Exp.lit (.int 3))) := rfl
-- - is right-associative likewise
example : pl(#(.int 1) - #(.int 2) - #(.int 3)) =
    Exp.binop .minus (Exp.lit (.int 1)) (Exp.binop .minus (Exp.lit (.int 2)) (Exp.lit (.int 3))) := rfl
-- * binds tighter than -
example : pl(#(.int 1) - #(.int 2) * #(.int 3)) =
    Exp.binop .minus (Exp.lit (.int 1)) (Exp.binop .mult (Exp.lit (.int 2)) (Exp.lit (.int 3))) := rfl
-- parentheses override precedence
example : pl((#(.int 1) + #(.int 2)) * #(.int 3)) =
    Exp.binop .mult (Exp.binop .plus (Exp.lit (.int 1)) (Exp.lit (.int 2))) (Exp.lit (.int 3)) := rfl
-- unary minus binds tighter than binary +
example : pl(-x + y) =
    Exp.binop .plus (Exp.unop .minus (Exp.var "x")) (Exp.var "y") := rfl
-- ~ binds tighter than &&
example : pl(~x && y) =
    Exp.binop .and (Exp.unop .neg (Exp.var "x")) (Exp.var "y") := rfl
-- && binds tighter than ||
example : pl(x && y || z) =
    Exp.binop .or (Exp.binop .and (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl
-- = has lower precedence than +
example : pl(x + y = z) =
    Exp.binop .eq (Exp.binop .plus (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl

-- Escape hatch {}: splice a Lean term directly
example (e : Exp) : pl({e}) = e := rfl
example (e1 e2 : Exp) : pl({e1} + {e2}) = Exp.binop .plus e1 e2 := rfl

-- Literals
example : pl(#(.bool true)) = Exp.lit (.bool true) := rfl
example : pl(#.unit) = Exp.lit .unit := rfl

-- Unary operators
example : pl(~x) = Exp.unop .neg (Exp.var "x") := rfl
example : pl(-x) = Exp.unop .minus (Exp.var "x") := rfl

-- Conditional
example : pl(if x then y else z) = Exp.cond (Exp.var "x") (Exp.var "y") (Exp.var "z") := rfl
-- if-then-else is low precedence: body can contain operators
example : pl(if x then y + z else w) =
    Exp.cond (Exp.var "x") (Exp.binop .plus (Exp.var "y") (Exp.var "z")) (Exp.var "w") := rfl

-- Sequencing
example : pl(e1; e2) = Exp.app (Exp.letrec .anon .anon (Exp.var "e2")) (Exp.var "e1") := rfl
-- Let binding (tested via #check since `:=` inside pl(let ...) confuses example/def parsers)
/-- info: pl(fun x, x e) : Exp -/
#guard_msgs in #check (pl(let x := e; x) : Exp)
/-- info: pl(fun x, (x + x) #(BaseLit.int 1)) : Exp -/
#guard_msgs in #check (pl(let x := #(.int 1); x + x) : Exp)

-- Application is left-associative
example : pl(f x y) = Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y") := rfl
-- Application binds tighter than +
example : pl(f x + g y) =
    Exp.binop .plus (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.app (Exp.var "g") (Exp.var "y")) := rfl

-- Sequencing
example : pl(e1; e2) = Exp.app (Exp.letrec .anon .anon (Exp.var "e2")) (Exp.var "e1") := rfl

-- rec with named self-reference
example : pl(rec f x := f x) =
    Exp.letrec (.named "f") (.named "x") (Exp.app (Exp.var "f") (Exp.var "x")) := rfl
-- fun with anonymous self-reference
example : pl(fun x, x) = Exp.letrec .anon (.named "x") (Exp.var "x") := rfl
-- multi-arg fun desugars to nested letrec
example : pl(fun x y z, x) =
    Exp.letrec .anon (.named "x")
      (Exp.letrec .anon (.named "y")
        (Exp.letrec .anon (.named "z") (Exp.var "x"))) := rfl

-- Pairs: snd and nested triples
example : pl(snd((x, y))) = Exp.snd (Exp.pair (Exp.var "x") (Exp.var "y")) := rfl
example : pl((x, y, z)) =
    Exp.pair (Exp.var "x") (Exp.pair (Exp.var "y") (Exp.var "z")) := rfl

-- Sums
example : pl(inr(x)) = Exp.inr (Exp.var "x") := rfl
-- case with non-trivial branch bodies
example : pl(case inl(x) | l => l + #(.int 1) | r => r) =
    Exp.case (Exp.inl (Exp.var "x"))
      (Exp.letrec .anon (.named "l") (Exp.binop .plus (Exp.var "l") (Exp.lit (.int 1))))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- Store binds tighter than sequencing
example : pl(x ← #(.int 1); e2) =
    Exp.app (Exp.letrec .anon .anon (Exp.var "e2"))
            (Exp.store (Exp.var "x") (Exp.lit (.int 1))) := rfl

-- Delaboration (unexpander) tests: check that Exp constructors print back as pl(...) syntax
/-- info: pl(#(BaseLit.int 1)) : Exp -/
#guard_msgs in #check (Exp.lit (.int 1) : Exp)

/-- info: pl(x) : Exp -/
#guard_msgs in #check (Exp.var "x" : Exp)

/-- info: pl((#(BaseLit.int 1) + (#(BaseLit.int 2) * #(BaseLit.int 3)))) : Exp -/
#guard_msgs in #check (Exp.binop .plus (Exp.lit (.int 1)) (Exp.binop .mult (Exp.lit (.int 2)) (Exp.lit (.int 3))) : Exp)

/-- info: pl(!x) : Exp -/
#guard_msgs in #check (Exp.load (Exp.var "x") : Exp)

/-- info: pl(fun f, f) : Exp -/
#guard_msgs in #check (Exp.letrec .anon (.named "f") (Exp.var "f") : Exp)

/-- info: pl(fun f, fun x, f x) : Exp -/
#guard_msgs in #check (Exp.letrec .anon (.named "f") (Exp.letrec .anon (.named "x") (Exp.app (Exp.var "f") (Exp.var "x"))) : Exp)

/-- info: pl(alloc(#(BaseLit.int 0))) : Exp -/
#guard_msgs in #check (Exp.alloc (Exp.lit (.int 0)) : Exp)

/-- info: pl(inl(x)) : Exp -/
#guard_msgs in #check (Exp.inl (Exp.var "x") : Exp)

end Tests

end ProbLang
