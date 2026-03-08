import Lean.PrettyPrinter.Delaborator
import Metrology.ProbLang.Syntax

namespace ProbLang

-- TODO: Change single-arm case syntax to be a let
-- TODO: Add constructors to case arms, to allow re-ordering
-- TODO: Add a syntax for match expressions to unify `if let` and enable generic nested pattern matches

open Lean Lean.PrettyPrinter Elab Parser

declare_syntax_cat pl_exp
declare_syntax_cat pl_ty
declare_syntax_cat pl_arg

/-- embedding ProbLang expressions into terms -/
syntax:max "pl(" pl_exp ")" : term
/-- embedding ProbLang binders into terms -/
syntax:max "pl_binder(" binderIdent ")" : term
/-- embedding ProbLang typed binders into terms -/
syntax:max "pl_binder(" "(" ident " : " pl_ty ")" ")" : term
/-- embedding ProbLang types into terms -/
syntax:max "pl_ty(" pl_ty ")" : term

/-- pl_arg: plain binder or typed binder -/
syntax binderIdent : pl_arg
syntax "(" ident " : " pl_ty ")" : pl_arg

/-- embedding ProbLang binder arguments into terms -/
syntax:max "pl_binder_arg(" pl_arg ")" : term

/-- Type syntax -/
syntax:max "int" : pl_ty
syntax:max "bool" : pl_ty
syntax:max "unit" : pl_ty
syntax:max "(" pl_ty ")" : pl_ty
syntax:35 pl_ty:36 " × " pl_ty:35 : pl_ty
syntax:30 pl_ty:31 " + " pl_ty:30 : pl_ty
syntax:25 pl_ty:26 " → " pl_ty:25 : pl_ty
syntax:max "ref(" pl_ty ")" : pl_ty
syntax:max "tape(" pl_ty ")" : pl_ty

/-- escaping back to Lean -/
syntax:max "{" term "}" : pl_exp
/-- embedding literals -/
syntax:max "#" term:max : pl_exp
/-- variables -/
syntax:max ident : pl_exp
/-- parentheses -/
syntax:max "(" pl_exp ")" : pl_exp
/-- type annotation -/
syntax:max "(" pl_exp " : " pl_ty ")" : pl_exp

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
syntax:10 "let " pl_arg " := " pl_exp:10 "; " pl_exp:1 : pl_exp
syntax:5 pl_exp:6 "; " pl_exp:5 : pl_exp
syntax:10 "fun" pl_arg+ ", " pl_exp:10 : pl_exp
syntax:10 "rec " pl_arg ppSpace pl_arg+ " := " pl_exp:10 : pl_exp

/-- Cases -/
syntax:max "(" pl_exp ", " pl_exp,+ ")" : pl_exp
syntax:100 "fst(" pl_exp ")" : pl_exp
syntax:100 "snd(" pl_exp ")" : pl_exp

syntax:100 "inl(" pl_exp ")" : pl_exp
syntax:100 "inr(" pl_exp ")" : pl_exp
syntax:10 "case " pl_exp " | " pl_arg " => " pl_exp " | " pl_arg " => " pl_exp : pl_exp

/-- State -/
syntax:100 "alloc(" pl_exp ")" : pl_exp
syntax:80 "!" pl_exp:80 : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80 : pl_exp

/-- Random -/
syntax:100 "tape(" pl_exp ")" : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")" : pl_exp

/-- Failure -/
syntax:max "fail" : pl_exp

/-- Destructuring let for pairs -/
syntax:10 "let" "(" pl_arg ", " pl_arg ")" ":=" pl_exp:10 "; " pl_exp:1 : pl_exp

/-- Single-arm case for sums -/
syntax:10 "case " pl_exp " | " "inl(" pl_arg ")" " => " pl_exp : pl_exp
syntax:10 "case " pl_exp " | " "inr(" pl_arg ")" " => " pl_exp : pl_exp

/-- Assertion -/
syntax:100 "assert(" pl_exp ")" : pl_exp

-- Keywords that may not be used as variable or binder names in ProbLang.
-- The Lean-level keywords (if, then, else, let, fun, rec, case) are already
-- rejected by the Lean lexer before our rules fire, but are listed here for
-- completeness.
private def reservedKeywords : List String :=
  ["fst", "snd", "inl", "inr", "alloc", "tape", "rand", "fail",
   "if", "then", "else", "let", "fun", "rec", "case"]

private def checkNotReserved (i : Lean.Ident) : Lean.MacroM Unit := do
  let s := i.getId.toString
  if reservedKeywords.contains s then
    Macro.throwError s!"'{s}' is a reserved keyword in ProbLang and cannot be used as an identifier"

/-- elaborating types -/
macro_rules
  | `(pl_ty(int))          => `(Ty.int)
  | `(pl_ty(bool))         => `(Ty.bool)
  | `(pl_ty(unit))         => `(Ty.unit)
  | `(pl_ty(($τ)))         => `(pl_ty($τ))
  | `(pl_ty($τ1 × $τ2))   => `(Ty.prod pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 + $τ2))   => `(Ty.sum pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 → $τ2))   => `(Ty.arrow pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty(ref($τ)))      => `(Ty.ref pl_ty($τ))
  | `(pl_ty(tape($τ)))     => `(Ty.tape pl_ty($τ))

/-- elaborating binders -/
macro_rules
  | `(pl_binder(_))        => `(Binder.anon)
  | `(pl_binder($i:ident)) => do
    checkNotReserved i
    `(Binder.named $(Syntax.mkStrLit i.getId.toString))
  | `(pl_binder(($i:ident : $τ))) => do
    checkNotReserved i
    `(Binder.typed $(Syntax.mkStrLit i.getId.toString) pl_ty($τ))

/-- elaborating binder arguments (pl_arg → pl_binder) -/
macro_rules
  | `(pl_binder_arg($i:binderIdent)) => `(pl_binder($i))
  | `(pl_binder_arg(($i:ident : $τ))) => `(pl_binder(($i : $τ)))

/-- elaborating expressions -/
macro_rules
  -- Type annotation (must precede parentheses)
  | `(pl(($e : $τ)))        => `(Exp.annot (.ty pl_ty($τ)) pl($e))
  -- Parentheses (transparent)
  | `(pl(($e)))             => `(pl($e))
  -- Escape hatch
  | `(pl({$t}))             => pure t
  -- Literal shorthands (must precede the general `# $e` rule)
  | `(pl(# $n:num))         => `(Exp.lit (.int (Int.ofNat $n)))
  | `(pl(#true))            => `(Exp.lit (.bool true))
  | `(pl(#false))           => `(Exp.lit (.bool false))
  -- Literals
  | `(pl(# $e))             => `(Exp.lit $e)
  -- Variables
  | `(pl($i:ident))         => do
    checkNotReserved i
    `(Exp.var $(Syntax.mkStrLit i.getId.toString))
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
  | `(pl(rec $f:pl_arg $x:pl_arg $xs:pl_arg* := $e)) => do
      if xs.size == 0 then
        `(Exp.letrec pl_binder_arg($f) pl_binder_arg($x) pl($e))
      else
        `(pl(rec $f $x := fun $xs*, $e))
  | `(pl(fun $x:pl_arg $xs:pl_arg* , $e)) => do
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
  | `(pl(case $ec | $il:pl_arg => $el | $ir:pl_arg => $er)) =>
      `(Exp.case pl($ec) pl(rec _ $il := $el) pl(rec _ $ir := $er))
  -- Heap
  | `(pl(alloc($e)))             => `(Exp.alloc pl($e))
  | `(pl(! $e))                  => `(Exp.load pl($e))
  | `(pl($e1 ← $e2))            => `(Exp.store pl($e1) pl($e2))
  -- Let and sequencing
  | `(pl(let $i:pl_arg := $e1; $e2))    => `(Exp.app (Exp.letrec .anon pl_binder_arg($i) pl($e2)) pl($e1))
  | `(pl($e1; $e2))              => `(Exp.app (Exp.letrec .anon .anon pl($e2)) pl($e1))
  -- Probabilistic
  | `(pl(tape($e)))              => `(Exp.tape pl($e))
  | `(pl(rand($e1, $e2)))        => `(Exp.rand pl($e1) pl($e2))
  -- Failure
  | `(pl(fail))                  => `(Exp.fail)
  -- Destructuring let for pairs: let (x, y) := e; body
  --   ↦  let p✝ := e; let x := fst(p✝); let y := snd(p✝); body
  -- Uses addMacroScope to generate a fresh hygienic name for the pair binding.
  | `(pl(let ( $x:pl_arg , $y:pl_arg ) := $e ; $body)) => do
      let pName := (← Lean.MonadQuotation.addMacroScope `p).toString
      `(Exp.app
          (Exp.letrec .anon (Binder.named $(quote pName))
            (Exp.app
              (Exp.letrec .anon pl_binder_arg($x)
                (Exp.app
                  (Exp.letrec .anon pl_binder_arg($y) pl($body))
                  (Exp.snd (Exp.var $(quote pName)))))
              (Exp.fst (Exp.var $(quote pName)))))
          pl($e))
  -- Single-arm case: silently fails on the other branch
  | `(pl(case $ec | inl($x:pl_arg) => $el)) =>
      `(pl(case $ec | $x => $el | _ => fail))
  | `(pl(case $ec | inr($y:pl_arg) => $er)) =>
      `(pl(case $ec | _ => fail | $y => $er))
  -- Assert: assert(e) = if e then #.unit else fail
  | `(pl(assert($e))) => `(pl(if $e then #.unit else fail))


/-- Strip the `pl(...)` wrapper to get a raw `pl_exp`, or fall back to `{t}` escape. -/
partial def unpackPLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_exp)
  | `(pl($e)) => `(pl_exp|$e)
  | `($t)     => `(pl_exp|{$t})

/-- Strip the `pl_ty(...)` wrapper to get a raw `pl_ty`. -/
partial def unpackPLTy [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_ty)
  | `(pl_ty($τ)) => pure τ
  | `($_)        => panic! "unknown type"

/-- Strip the `pl_binder(...)` wrapper to get a raw `pl_arg`. -/
partial def unpackPLBinder [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_arg)
  | `(pl_binder($i:ident)) => `(pl_arg|$i:ident)
  | `(pl_binder(_)) => `(pl_arg|_)
  | `(pl_binder(($i:ident : $τ))) => `(pl_arg|($i : $τ))
  | `($_)            => panic! "unknown binder"

/-- Flatten multi-arg `fun`/`rec` into a single binder list.
    For anonymous recs, folds into `pl(fun xs*, body)`.
    For named recs, folds inner `fun` binders into `pl(rec f xs*, body)`. -/
partial def unexpFun : Term → UnexpandM Term
  | `(pl(rec _ $x := $e)) => do unexpFun (← `(pl(fun $x, $e)))
  | `(pl(fun $xs*, $e)) => do
    match e with
    | `(pl(fun $ys*, $body)) => unexpFun (← `(pl(fun $xs* $ys*, $body)))
    | _ => return (← `(pl(fun $xs*, $e)))
  -- Named rec: if body is a fun, absorb its binders into the rec argument list
  | `(pl(rec $f $xs* := $e)) => do
    match (e : TSyntax `pl_exp) with
    | `(pl_exp| fun $ys*, $body) => unexpFun (← `(pl(rec $f $xs* $ys* := $body)))
    | _ => return (← `(pl(rec $f $xs* := $e)))
  | x => return x

@[app_unexpander Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(pl_binder(_))

@[app_unexpander Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(pl_binder($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

@[app_unexpander Binder.typed]
def unexpTyped : Unexpander
  | `($_ $s:str $τ) => do
    `(pl_binder(($(Lean.mkIdent $ Name.mkSimple s.getString):ident : $(← unpackPLTy τ))))
  | _ => throw ()

@[app_unexpander Ty.int]
def unexpTyInt : Unexpander | `($_) => `(pl_ty(int))
@[app_unexpander Ty.bool]
def unexpTyBool : Unexpander | `($_) => `(pl_ty(bool))
@[app_unexpander Ty.unit]
def unexpTyUnit : Unexpander | `($_) => `(pl_ty(unit))
@[app_unexpander Ty.prod]
def unexpTyProd : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) × $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.sum]
def unexpTySum : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) + $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.arrow]
def unexpTyArrow : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) → $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.ref]
def unexpTyRef : Unexpander
  | `($_ $τ) => do `(pl_ty(ref($(← unpackPLTy τ))))
  | _ => throw ()
@[app_unexpander Ty.tape]
def unexpTyTape : Unexpander
  | `($_ $τ) => do `(pl_ty(tape($(← unpackPLTy τ))))
  | _ => throw ()

@[app_unexpander Annot.ty]
def unexpAnnotTy : Unexpander
  | `($_ $τ) => pure τ  -- pass through the pl_ty(...) wrapper
  | _ => throw ()

@[app_unexpander Exp.annot]
def unexpAnnot : Unexpander
  | `($_ $a $e) => do
    match a with
    | `(pl_ty($τ)) => `(pl(($(← unpackPLExp e) : $τ)))
    | _ => throw ()
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

/-- Check if a `pl_arg` represents a named (non-anonymous) binder. -/
private def isNamedArg (bi : TSyntax `pl_arg) : Bool :=
  -- A typed binder `(x : τ)` always has multiple args (parens, ident, colon, ty).
  -- A plain binderIdent wraps ident or hole; check first child's first child.
  if bi.raw.getNumArgs > 1 then true        -- typed binder
  else bi.raw[0]![0]!.isIdent               -- plain binderIdent: ident vs _

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    -- Recognize `let x := val; body` and `val; body` before falling through
    -- to raw application.  Both are encoded as (letrec .anon binder body) val,
    -- which `unexpLetrec` has already turned into pl(fun xs*, body).
    match e1 with
    | `(pl(fun $xs*, $body)) =>
        if xs.size == 1 then
          let bi := xs[0]!
          if isNamedArg bi then
            -- Named binder → let x := val; body
            return (← `(pl(let $bi := $(← unpackPLExp e2); $body)))
          else
            -- Anonymous binder (_) → val; body
            return (← `(pl($(← unpackPLExp e2); $body)))
        `(pl($(← unpackPLExp e1) $(← unpackPLExp e2)))
    | _ =>
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

@[app_unexpander ProbLang.Exp.fail]
def unexpFail : Unexpander
  | `($_) => do `(pl(fail))

section Tests

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
/-- error: 'tape' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(tape) : Exp)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rand) : Exp)
-- Reserved keywords are rejected in binder position
/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun fst, x) : Exp)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun inl, x) : Exp)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rec f rand := x) : Exp)

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

-- Literal shorthands
example : pl(#1) = Exp.lit (.int 1) := rfl
example : pl(#0) = Exp.lit (.int 0) := rfl
example : pl(#42) = Exp.lit (.int 42) := rfl
example : pl(#true) = Exp.lit (.bool true) := rfl
example : pl(#false) = Exp.lit (.bool false) := rfl
-- Shorthands compose with operators
example : pl(#1 + #2) = Exp.binop .plus (Exp.lit (.int 1)) (Exp.lit (.int 2)) := rfl
example : pl(#true && #false) = Exp.binop .and (Exp.lit (.bool true)) (Exp.lit (.bool false)) := rfl

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
/-- info: pl(let x := e; x) : Exp -/
#guard_msgs in #check (pl(let x := e; x) : Exp)
/-- info: pl(let x := #(BaseLit.int 1); (x + x)) : Exp -/
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

-- rec with multiple args desugars to rec with single arg and inner fun
example : pl(rec f x y := f x y) =
    Exp.letrec (.named "f") (.named "x")
      (Exp.letrec .anon (.named "y")
        (Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y"))) := rfl
-- three-arg rec
example : pl(rec f x y z := f x y z) =
    Exp.letrec (.named "f") (.named "x")
      (Exp.letrec .anon (.named "y")
        (Exp.letrec .anon (.named "z")
          (Exp.app (Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y")) (Exp.var "z")))) := rfl

-- fun uses .anon self-binder; rec uses .named
example : pl(fun x, x) = Exp.letrec .anon (.named "x") (Exp.var "x") := rfl
example : pl(rec f x := x) = Exp.letrec (.named "f") (.named "x") (Exp.var "x") := rfl

-- anonymous argument binder _
example : pl(fun _, x) = Exp.letrec .anon .anon (Exp.var "x") := rfl
example : pl(rec f _ := f) = Exp.letrec (.named "f") .anon (Exp.var "f") := rfl

-- snd with nested triple
example : pl(snd((x, y, z))) =
    Exp.snd (Exp.pair (Exp.var "x") (Exp.pair (Exp.var "y") (Exp.var "z"))) := rfl

-- Sequencing with let: `let x := e1; e2; e3` parses as `let x := e1; (e2; e3)`
-- because let (prec 10) has higher precedence than ; (prec 5).
-- So it elaborates to ((fun x, ((fun _, e3) e2)) e1).
example : pl(let x := e1; e2; e3) =
    Exp.app (Exp.letrec .anon (.named "x")
              (Exp.app (Exp.letrec .anon .anon (Exp.var "e3")) (Exp.var "e2")))
            (Exp.var "e1") := rfl

-- xor precedence: ^^ binds tighter than ||, looser than &&
example : pl(x && y ^^ z) =
    Exp.binop .xor (Exp.binop .and (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl
example : pl(x ^^ y || z) =
    Exp.binop .or (Exp.binop .xor (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl

-- ! (load) binds tighter than *
example : pl(!x * y) =
    Exp.binop .mult (Exp.load (Exp.var "x")) (Exp.var "y") := rfl

-- application binds tighter than *
example : pl(f x * g y) =
    Exp.binop .mult (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.app (Exp.var "g") (Exp.var "y")) := rfl

-- ← (store) binds tighter than ;;
example : pl(x ← y; z) =
    Exp.app (Exp.letrec .anon .anon (Exp.var "z"))
            (Exp.store (Exp.var "x") (Exp.var "y")) := rfl

-- nested let scoping: x is in scope in the body of the second let
example : pl(let x := e1; let y := e2; x + y) =
    Exp.app
      (Exp.letrec .anon (.named "x")
        (Exp.app
          (Exp.letrec .anon (.named "y")
            (Exp.binop .plus (Exp.var "x") (Exp.var "y")))
          (Exp.var "e2")))
      (Exp.var "e1") := rfl

-- case with inr scrutinee
example : pl(case inr(x) | l => l | r => r) =
    Exp.case (Exp.inr (Exp.var "x"))
      (Exp.letrec .anon (.named "l") (Exp.var "l"))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- escape hatch inside compound expressions
example (e : Exp) : pl(let x := {e}; x) =
    Exp.app (Exp.letrec .anon (.named "x") (Exp.var "x")) e := rfl
example (e : Exp) : pl(if {e} then x else y) =
    Exp.cond e (Exp.var "x") (Exp.var "y") := rfl
example (e : Exp) : pl(fun x, {e}) =
    Exp.letrec .anon (.named "x") e := rfl
example (e1 e2 : Exp) : pl(case {e1} | l => {e2} | r => r) =
    Exp.case e1
      (Exp.letrec .anon (.named "l") e2)
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- Variable shadowing: let x rebinds x; inner x refers to new binding
example : pl(let x := e; let x := x; x) =
    Exp.app
      (Exp.letrec .anon (.named "x")
        (Exp.app
          (Exp.letrec .anon (.named "x") (Exp.var "x"))
          (Exp.var "x")))
      (Exp.var "e") := rfl

-- fun shadows outer variable of same name
example : pl(fun x, fun x, x) =
    Exp.letrec .anon (.named "x")
      (Exp.letrec .anon (.named "x") (Exp.var "x")) := rfl

-- rec self-name shadows outer variable of same name
example : pl(rec f x := rec f x := f x) =
    Exp.letrec (.named "f") (.named "x")
      (Exp.letrec (.named "f") (.named "x")
        (Exp.app (Exp.var "f") (Exp.var "x"))) := rfl

-- rec self-name and arg name are the same identifier
example : pl(rec x x := x x) =
    Exp.letrec (.named "x") (.named "x")
      (Exp.app (Exp.var "x") (Exp.var "x")) := rfl

-- if branches contain let/fun (low-prec forms inside low-prec if)
example : pl(if x then let y := e; y else z) =
    Exp.cond (Exp.var "x")
      (Exp.app (Exp.letrec .anon (.named "y") (Exp.var "y")) (Exp.var "e"))
      (Exp.var "z") := rfl

-- case branch body contains sequencing
example : pl(case inl(x) | l => e1; l | r => r) =
    Exp.case (Exp.inl (Exp.var "x"))
      (Exp.letrec .anon (.named "l")
        (Exp.app (Exp.letrec .anon .anon (Exp.var "l")) (Exp.var "e1")))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- application of a literal (function position need not be a variable)
example : pl(#(.int 0) x) = Exp.app (Exp.lit (.int 0)) (Exp.var "x") := rfl

-- applying a pair projection
example : pl(fst(p) x) = Exp.app (Exp.fst (Exp.var "p")) (Exp.var "x") := rfl

-- unary minus on a compound expression
example : pl(-(x + y)) =
    Exp.unop .minus (Exp.binop .plus (Exp.var "x") (Exp.var "y")) := rfl

-- double negation
example : pl(~~x) = Exp.unop .neg (Exp.unop .neg (Exp.var "x")) := rfl

-- store into a computed address (address expression is non-trivial)
example : pl(fst(p) ← x) =
    Exp.store (Exp.fst (Exp.var "p")) (Exp.var "x") := rfl

-- load a loaded address (!(!x))
example : pl(!(!x)) = Exp.load (Exp.load (Exp.var "x")) := rfl

-- alloc of an allocated value
example : pl(alloc(alloc(x))) = Exp.alloc (Exp.alloc (Exp.var "x")) := rfl

-- pair of sums
example : pl((inl(x), inr(y))) =
    Exp.pair (Exp.inl (Exp.var "x")) (Exp.inr (Exp.var "y")) := rfl

-- fst/snd of a pair of pairs (projection from nested structure)
example : pl(fst(snd((x, (y, z))))) =
    Exp.fst (Exp.snd (Exp.pair (Exp.var "x") (Exp.pair (Exp.var "y") (Exp.var "z")))) := rfl

-- = is non-associative: x = y = z should parse as x = (y = z)
-- (right-associative at same precedence 50)
example : pl(x = y = z) =
    Exp.binop .eq (Exp.var "x") (Exp.binop .eq (Exp.var "y") (Exp.var "z")) := rfl

-- if condition contains a boolean operator
example : pl(if x && y then z else w) =
    Exp.cond (Exp.binop .and (Exp.var "x") (Exp.var "y")) (Exp.var "z") (Exp.var "w") := rfl

-- sequencing three expressions: e1; e2; e3 is right-associative
example : pl(e1; e2; e3) =
    Exp.app (Exp.letrec .anon .anon
              (Exp.app (Exp.letrec .anon .anon (Exp.var "e3")) (Exp.var "e2")))
            (Exp.var "e1") := rfl

-- Unary minus vs binary minus: -x - y is ((-x) - y), not -(x - y)
example : pl(-x - y) =
    Exp.binop .minus (Exp.unop .minus (Exp.var "x")) (Exp.var "y") := rfl

-- Unary minus vs binary minus: x - -y
example : pl(x - -y) =
    Exp.binop .minus (Exp.var "x") (Exp.unop .minus (Exp.var "y")) := rfl

-- ~ applied to an equality
example : pl(~(x = y)) =
    Exp.unop .neg (Exp.binop .eq (Exp.var "x") (Exp.var "y")) := rfl

-- = lower precedence than &&: x && y = z is (x && y) = z
example : pl(x && y = z) =
    Exp.binop .eq (Exp.binop .and (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl

-- = lower precedence than ||
example : pl(x || y = z) =
    Exp.binop .eq (Exp.binop .or (Exp.var "x") (Exp.var "y")) (Exp.var "z") := rfl

-- application of a fun expression (immediately invoked lambda)
example : pl((fun x, x) y) =
    Exp.app (Exp.letrec .anon (.named "x") (Exp.var "x")) (Exp.var "y") := rfl

-- application of a rec expression
example : pl((rec f x := f x) y) =
    Exp.app (Exp.letrec (.named "f") (.named "x") (Exp.app (Exp.var "f") (Exp.var "x"))) (Exp.var "y") := rfl

-- fun body is itself a fun (currying spelled out)
example : pl(fun x, fun y, x) =
    Exp.letrec .anon (.named "x") (Exp.letrec .anon (.named "y") (Exp.var "x")) := rfl

-- let binding of a fun
example : pl(let f := fun x, x; f) =
    Exp.app (Exp.letrec .anon (.named "f") (Exp.var "f"))
            (Exp.letrec .anon (.named "x") (Exp.var "x")) := rfl

-- let binding of a pair
example : pl(let p := (x, y); fst(p)) =
    Exp.app (Exp.letrec .anon (.named "p") (Exp.fst (Exp.var "p")))
            (Exp.pair (Exp.var "x") (Exp.var "y")) := rfl

-- case scrutinee is itself a case
example : pl(case (case inl(x) | l => inl(l) | r => inr(r)) | l => l | r => r) =
    Exp.case
      (Exp.case (Exp.inl (Exp.var "x"))
        (Exp.letrec .anon (.named "l") (Exp.inl (Exp.var "l")))
        (Exp.letrec .anon (.named "r") (Exp.inr (Exp.var "r"))))
      (Exp.letrec .anon (.named "l") (Exp.var "l"))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- case scrutinee is an if
example : pl(case (if b then inl(x) else inr(y)) | l => l | r => r) =
    Exp.case
      (Exp.cond (Exp.var "b") (Exp.inl (Exp.var "x")) (Exp.inr (Exp.var "y")))
      (Exp.letrec .anon (.named "l") (Exp.var "l"))
      (Exp.letrec .anon (.named "r") (Exp.var "r")) := rfl

-- if condition is itself an if
example : pl(if (if b then x else y) then z else w) =
    Exp.cond
      (Exp.cond (Exp.var "b") (Exp.var "x") (Exp.var "y"))
      (Exp.var "z") (Exp.var "w") := rfl

-- if branches are themselves ifs (dangling else resolved by grammar)
example : pl(if x then (if y then a else b) else c) =
    Exp.cond (Exp.var "x")
      (Exp.cond (Exp.var "y") (Exp.var "a") (Exp.var "b"))
      (Exp.var "c") := rfl

-- store value is a freshly allocated reference
example : pl(x ← alloc(y)) =
    Exp.store (Exp.var "x") (Exp.alloc (Exp.var "y")) := rfl

-- alloc of a fun value
example : pl(alloc(fun x, x)) =
    Exp.alloc (Exp.letrec .anon (.named "x") (Exp.var "x")) := rfl

-- rand applied to tape result
example : pl(rand(tape(n), #.unit)) =
    Exp.rand (Exp.tape (Exp.var "n")) (Exp.lit .unit) := rfl

-- Failure
example : pl(fail) = Exp.fail := rfl

-- Destructuring let for pairs.
-- The intermediate pair binding uses a hygienic name (addMacroScope), so we
-- can't predict the exact string.  We verify structure by checking that:
--  (a) the body expression reaches the right leaves, and
--  (b) a user variable "p" in the body is NOT captured by the pair binding.
-- The delab shows the hygienic name with _hyg suffix.
example : ∃ n,
    pl(let (x, y) := e; x + y) =
      Exp.app
        (Exp.letrec .anon (.named n)
          (Exp.app
            (Exp.letrec .anon (.named "x")
              (Exp.app
                (Exp.letrec .anon (.named "y")
                  (Exp.binop .plus (Exp.var "x") (Exp.var "y")))
                (Exp.snd (Exp.var n))))
            (Exp.fst (Exp.var n))))
        (Exp.var "e") := ⟨_, rfl⟩
-- Hygiene: "p" in the body refers to the outer variable, not the pair binding
example : ∃ n, n ≠ "p" ∧
    pl(let (x, y) := e; p) =
      Exp.app
        (Exp.letrec .anon (.named n)
          (Exp.app
            (Exp.letrec .anon (.named "x")
              (Exp.app
                (Exp.letrec .anon (.named "y") (Exp.var "p"))
                (Exp.snd (Exp.var n))))
            (Exp.fst (Exp.var n))))
        (Exp.var "e") := ⟨_, by decide, rfl⟩

-- Single-arm case for sums (inl and inr)
example : pl(case inl(x) | inl(v) => v) =
    Exp.case (Exp.inl (Exp.var "x"))
      (Exp.letrec .anon (.named "v") (Exp.var "v"))
      (Exp.letrec .anon .anon Exp.fail) := rfl
example : pl(case inr(x) | inr(v) => v) =
    Exp.case (Exp.inr (Exp.var "x"))
      (Exp.letrec .anon .anon Exp.fail)
      (Exp.letrec .anon (.named "v") (Exp.var "v")) := rfl

-- Assert
example : pl(assert(b)) =
    Exp.cond (Exp.var "b") (Exp.lit .unit) Exp.fail := rfl

-- tape and rand in a let
example : pl(let t := tape(n); rand(t, #.unit)) =
    Exp.app
      (Exp.letrec .anon (.named "t")
        (Exp.rand (Exp.var "t") (Exp.lit .unit)))
      (Exp.tape (Exp.var "n")) := rfl

-- applying the result of a load
example : pl((!f) x) = Exp.app (Exp.load (Exp.var "f")) (Exp.var "x") := rfl

-- storing the result of an application
example : pl(p ← f x) =
    Exp.store (Exp.var "p") (Exp.app (Exp.var "f") (Exp.var "x")) := rfl

-- fst of an application
example : pl(fst(f x)) = Exp.fst (Exp.app (Exp.var "f") (Exp.var "x")) := rfl

-- inl of an if
example : pl(inl(if b then x else y)) =
    Exp.inl (Exp.cond (Exp.var "b") (Exp.var "x") (Exp.var "y")) := rfl

-- deeply nested pairs (4-tuple)
example : pl((a, b, c, d)) =
    Exp.pair (Exp.var "a")
      (Exp.pair (Exp.var "b")
        (Exp.pair (Exp.var "c") (Exp.var "d"))) := rfl

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

/-- info: pl(inr(x)) : Exp -/
#guard_msgs in #check (Exp.inr (Exp.var "x") : Exp)

/-- info: pl(~x) : Exp -/
#guard_msgs in #check (Exp.unop .neg (Exp.var "x") : Exp)

/-- info: pl(-x) : Exp -/
#guard_msgs in #check (Exp.unop .minus (Exp.var "x") : Exp)

/-- info: pl(if x then y else z) : Exp -/
#guard_msgs in #check (Exp.cond (Exp.var "x") (Exp.var "y") (Exp.var "z") : Exp)

/-- info: pl((x, y)) : Exp -/
#guard_msgs in #check (Exp.pair (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x, y, z)) : Exp -/
#guard_msgs in #check (Exp.pair (Exp.var "x") (Exp.pair (Exp.var "y") (Exp.var "z")) : Exp)

/-- info: pl(fst(x)) : Exp -/
#guard_msgs in #check (Exp.fst (Exp.var "x") : Exp)

/-- info: pl(snd(x)) : Exp -/
#guard_msgs in #check (Exp.snd (Exp.var "x") : Exp)

/-- info: pl(case inl(x) | l => l | r => r) : Exp -/
#guard_msgs in #check (Exp.case (Exp.inl (Exp.var "x"))
    (Exp.letrec .anon (.named "l") (Exp.var "l"))
    (Exp.letrec .anon (.named "r") (Exp.var "r")) : Exp)

/-- info: pl(x ← y) : Exp -/
#guard_msgs in #check (Exp.store (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl(tape(#(BaseLit.int 10))) : Exp -/
#guard_msgs in #check (Exp.tape (Exp.lit (.int 10)) : Exp)

/-- info: pl(rand(#(BaseLit.int 10), #BaseLit.unit)) : Exp -/
#guard_msgs in #check (Exp.rand (Exp.lit (.int 10)) (Exp.lit .unit) : Exp)

/-- info: pl(fail) : Exp -/
#guard_msgs in #check (Exp.fail : Exp)

/-- info: pl(rec f x := f x) : Exp -/
#guard_msgs in #check (Exp.letrec (.named "f") (.named "x") (Exp.app (Exp.var "f") (Exp.var "x")) : Exp)

/-- info: pl(fun _, x) : Exp -/
#guard_msgs in #check (Exp.letrec .anon .anon (Exp.var "x") : Exp)

/-- info: pl(rec f _ := f) : Exp -/
#guard_msgs in #check (Exp.letrec (.named "f") .anon (Exp.var "f") : Exp)

/-- info: pl((x - y)) : Exp -/
#guard_msgs in #check (Exp.binop .minus (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x * y)) : Exp -/
#guard_msgs in #check (Exp.binop .mult (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x && y)) : Exp -/
#guard_msgs in #check (Exp.binop .and (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x || y)) : Exp -/
#guard_msgs in #check (Exp.binop .or (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x ^^ y)) : Exp -/
#guard_msgs in #check (Exp.binop .xor (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl((x = y)) : Exp -/
#guard_msgs in #check (Exp.binop .eq (Exp.var "x") (Exp.var "y") : Exp)

/-- info: pl(fun f, f x y) : Exp -/
#guard_msgs in #check (Exp.letrec .anon (.named "f")
    (Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y")) : Exp)

/-- info: pl(e1; e2) : Exp -/
#guard_msgs in #check (Exp.app (Exp.letrec .anon .anon (Exp.var "e2")) (Exp.var "e1") : Exp)

-- Delaboration: let and sequencing
/-- info: pl(let x := e1; e2) : Exp -/
#guard_msgs in #check (Exp.app (Exp.letrec .anon (.named "x") (Exp.var "e2")) (Exp.var "e1") : Exp)

/-- info: pl(e1; e2) : Exp -/
#guard_msgs in #check (Exp.app (Exp.letrec .anon .anon (Exp.var "e2")) (Exp.var "e1") : Exp)

-- Delaboration: multi-arg rec
/-- info: pl(rec f x y := f x y) : Exp -/
#guard_msgs in #check (Exp.letrec (.named "f") (.named "x")
    (Exp.letrec .anon (.named "y")
      (Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y"))) : Exp)

-- Type syntax
example : pl_ty(int) = Ty.int := rfl
example : pl_ty(bool) = Ty.bool := rfl
example : pl_ty(unit) = Ty.unit := rfl
example : pl_ty(int × bool) = Ty.prod .int .bool := rfl
example : pl_ty(int + bool) = Ty.sum .int .bool := rfl
example : pl_ty(int → bool) = Ty.arrow .int .bool := rfl
example : pl_ty(ref(int)) = Ty.ref .int := rfl
-- × is right-associative
example : pl_ty(int × bool × unit) = Ty.prod .int (.prod .bool .unit) := rfl
-- → is right-associative
example : pl_ty(int → bool → unit) = Ty.arrow .int (.arrow .bool .unit) := rfl
-- + is right-associative
example : pl_ty(int + bool + unit) = Ty.sum .int (.sum .bool .unit) := rfl
-- × binds tighter than +
example : pl_ty(int × bool + unit) = Ty.sum (.prod .int .bool) .unit := rfl
-- × binds tighter than →
example : pl_ty(int × bool → unit) = Ty.arrow (.prod .int .bool) .unit := rfl
-- parentheses override precedence
example : pl_ty(int × (bool + unit)) = Ty.prod .int (.sum .bool .unit) := rfl
-- ref and tape
example : pl_ty(ref(int × bool)) = Ty.ref (.prod .int .bool) := rfl
example : pl_ty(tape(int)) = Ty.tape .int := rfl

-- Expression type annotations
example : pl((x : int)) = Exp.annot (.ty .int) (Exp.var "x") := rfl
example : pl((#1 : int)) = Exp.annot (.ty .int) (Exp.lit (.int 1)) := rfl
example : pl((x + y : int)) = Exp.annot (.ty .int) (Exp.binop .plus (Exp.var "x") (Exp.var "y")) := rfl

-- Typed binders in fun
example : pl(fun (x : int), x) = Exp.letrec .anon (.typed "x" .int) (Exp.var "x") := rfl
-- Typed binders in rec
example : pl(rec f (x : int) := f x) =
    Exp.letrec (.named "f") (.typed "x" .int) (Exp.app (Exp.var "f") (Exp.var "x")) := rfl
-- Typed binders in let
example : pl(let (x : int) := #1; x) =
    Exp.app (Exp.letrec .anon (.typed "x" .int) (Exp.var "x")) (Exp.lit (.int 1)) := rfl
-- Mixed typed and untyped binders
example : pl(fun (x : int) y, x + y) =
    Exp.letrec .anon (.typed "x" .int)
      (Exp.letrec .anon (.named "y")
        (Exp.binop .plus (Exp.var "x") (Exp.var "y"))) := rfl

-- Delaboration: type annotations
/-- info: pl((x : int)) : Exp -/
#guard_msgs in #check (Exp.annot (.ty .int) (Exp.var "x") : Exp)

-- Delaboration: typed binders
/-- info: pl(fun(x : int), x) : Exp -/
#guard_msgs in #check (Exp.letrec .anon (.typed "x" .int) (Exp.var "x") : Exp)

/-- info: pl(rec f (x : int) := f x) : Exp -/
#guard_msgs in #check (Exp.letrec (.named "f") (.typed "x" .int) (Exp.app (Exp.var "f") (Exp.var "x")) : Exp)

-- Delaboration: types
/-- info: pl_ty(int × bool → unit) : Ty -/
#guard_msgs in #check (Ty.arrow (.prod .int .bool) .unit : Ty)

/-- info: pl_ty(ref(int)) : Ty -/
#guard_msgs in #check (Ty.ref .int : Ty)

-- + binds tighter than →
example : pl_ty(int + bool → unit) = Ty.arrow (.sum .int .bool) .unit := rfl
-- ref inside compound types
example : pl_ty(ref(int) × ref(bool)) = Ty.prod (.ref .int) (.ref .bool) := rfl
-- nested ref
example : pl_ty(ref(ref(int))) = Ty.ref (.ref .int) := rfl

-- Annotation with compound type
example : pl((x : int → bool)) = Exp.annot (.ty (.arrow .int .bool)) (Exp.var "x") := rfl
-- Annotation with product type
example : pl((x : int × bool)) = Exp.annot (.ty (.prod .int .bool)) (Exp.var "x") := rfl
-- Nested annotation
example : pl(((x : int) : int)) =
    Exp.annot (.ty .int) (Exp.annot (.ty .int) (Exp.var "x")) := rfl

-- Typed binder in case arms
example : pl(case inl(#1) | (x : int) => x | (y : bool) => y) =
    Exp.case (Exp.inl (Exp.lit (.int 1)))
      (Exp.letrec .anon (.typed "x" .int) (Exp.var "x"))
      (Exp.letrec .anon (.typed "y" .bool) (Exp.var "y")) := rfl

-- Multi-arg rec with all typed binders
example : pl(rec f (x : int) (y : bool) := f x y) =
    Exp.letrec (.named "f") (.typed "x" .int)
      (Exp.letrec .anon (.typed "y" .bool)
        (Exp.app (Exp.app (Exp.var "f") (Exp.var "x")) (Exp.var "y"))) := rfl

-- Typed binder in single-arm case
example : pl(case inl(#1) | inl((v : int)) => v) =
    Exp.case (Exp.inl (Exp.lit (.int 1)))
      (Exp.letrec .anon (.typed "v" .int) (Exp.var "v"))
      (Exp.letrec .anon .anon Exp.fail) := rfl

-- Annotation inside a let body
example : pl(let (x : int) := #1; (x : int)) =
    Exp.app (Exp.letrec .anon (.typed "x" .int)
              (Exp.annot (.ty .int) (Exp.var "x")))
            (Exp.lit (.int 1)) := rfl

-- Delaboration: compound type annotation
/-- info: pl((x : int → bool)) : Exp -/
#guard_msgs in #check (Exp.annot (.ty (.arrow .int .bool)) (Exp.var "x") : Exp)

-- Delaboration: product type
/-- info: pl_ty(int × bool) : Ty -/
#guard_msgs in #check (Ty.prod .int .bool : Ty)

-- Delaboration: sum type
/-- info: pl_ty(int + bool) : Ty -/
#guard_msgs in #check (Ty.sum .int .bool : Ty)

-- ---------------------------------------------------------------------------
-- Annotation interactions with IsVal
-- ---------------------------------------------------------------------------

-- Annotated literal is a value
example : (pl((#1 : int))).isValue := ⟨.annot .lit⟩
-- Annotated pair is a value
example : (pl(((#1, #2) : int × int))).isValue := ⟨.annot (.pair .lit .lit)⟩
-- Annotated non-value is not a value
example : ¬(pl((x + y : int))).isValue := by simp [Exp.isValue_iff_isValueR]

-- Annotated value in operational positions
example : pl(fst(((#1, #2) : int × int))) =
    Exp.fst (Exp.annot (.ty (.prod .int .int)) (Exp.pair (Exp.lit (.int 1)) (Exp.lit (.int 2)))) := rfl
example : pl((fun x, x : int → int) #1) =
    Exp.app (Exp.annot (.ty (.arrow .int .int)) (Exp.letrec .anon (.named "x") (Exp.var "x")))
            (Exp.lit (.int 1)) := rfl

-- ---------------------------------------------------------------------------
-- Typed binders in destructuring let
-- ---------------------------------------------------------------------------

example : ∃ n,
    pl(let ((x : int), (y : bool)) := e; x + y) =
      Exp.app
        (Exp.letrec .anon (.named n)
          (Exp.app
            (Exp.letrec .anon (.typed "x" .int)
              (Exp.app
                (Exp.letrec .anon (.typed "y" .bool)
                  (Exp.binop .plus (Exp.var "x") (Exp.var "y")))
                (Exp.snd (Exp.var n))))
            (Exp.fst (Exp.var n))))
        (Exp.var "e") := ⟨_, rfl⟩

-- ---------------------------------------------------------------------------
-- Substitution with typed binders
-- ---------------------------------------------------------------------------

-- typed binder substitutes like named
example : Exp.subst (.typed "x" .int) (Exp.lit (.int 42)) (Exp.var "x") = Exp.lit (.int 42) := rfl
-- typed binder doesn't substitute other variables
example : Exp.subst (.typed "x" .int) (Exp.lit (.int 42)) (Exp.var "y") = Exp.var "y" := rfl
-- typed binder in letrec shadows correctly
example : (Exp.letrec .anon (.typed "x" .int) (Exp.var "x")).subst' "x" (Exp.lit (.int 99)) =
    Exp.letrec .anon (.typed "x" .int) (Exp.var "x") := rfl
-- typed binder as function name shadows correctly
example : (Exp.letrec (.typed "f" (.arrow .int .int)) (.named "x") (Exp.var "f")).subst' "f" (Exp.lit (.int 99)) =
    Exp.letrec (.typed "f" (.arrow .int .int)) (.named "x") (Exp.var "f") := rfl
-- non-shadowed variable is substituted under typed binder
example : (Exp.letrec .anon (.typed "x" .int) (Exp.var "y")).subst' "y" (Exp.lit (.int 7)) =
    Exp.letrec .anon (.typed "x" .int) (Exp.lit (.int 7)) := rfl

-- ---------------------------------------------------------------------------
-- Edge cases in existing syntax
-- ---------------------------------------------------------------------------

-- fun with _ applied to a value
example : pl((fun _, fail) #1) =
    Exp.app (Exp.letrec .anon .anon Exp.fail) (Exp.lit (.int 1)) := rfl
-- sequencing with fail
example : pl(fail; x) =
    Exp.app (Exp.letrec .anon .anon (Exp.var "x")) Exp.fail := rfl
-- case where both arms use _
example : pl(case inl(#1) | _ => #2 | _ => #3) =
    Exp.case (Exp.inl (Exp.lit (.int 1)))
      (Exp.letrec .anon .anon (Exp.lit (.int 2)))
      (Exp.letrec .anon .anon (Exp.lit (.int 3))) := rfl
-- deeply nested lets
example : pl(let x := (let y := #1; y); x) =
    Exp.app
      (Exp.letrec .anon (.named "x") (Exp.var "x"))
      (Exp.app (Exp.letrec .anon (.named "y") (Exp.var "y")) (Exp.lit (.int 1))) := rfl

-- store/load with annotations
example : pl(alloc((#0 : int))) =
    Exp.alloc (Exp.annot (.ty .int) (Exp.lit (.int 0))) := rfl
example : pl(!(r : ref(int))) =
    Exp.load (Exp.annot (.ty (.ref .int)) (Exp.var "r")) := rfl

-- ---------------------------------------------------------------------------
-- Delaboration round-trips
-- ---------------------------------------------------------------------------

-- Typed binder in let round-trips
/-- info: pl(let (x : int) := #(BaseLit.int 1); x) : Exp -/
#guard_msgs in #check (Exp.app (Exp.letrec .anon (.typed "x" .int) (Exp.var "x")) (Exp.lit (.int 1)) : Exp)

-- Multi-arg fun with mixed typed/untyped: typed binder prevents collapsing
/-- info: pl(fun(x : int), fun y, (x + y)) : Exp -/
#guard_msgs in #check (Exp.letrec .anon (.typed "x" .int)
    (Exp.letrec .anon (.named "y")
      (Exp.binop .plus (Exp.var "x") (Exp.var "y"))) : Exp)

-- Annotated value inside a pair
/-- info: pl(((#(BaseLit.int 1) : int), #(BaseLit.int 2))) : Exp -/
#guard_msgs in #check (Exp.pair (Exp.annot (.ty .int) (Exp.lit (.int 1))) (Exp.lit (.int 2)) : Exp)

-- Annotation on a compound expression
/-- info: pl(((x + y) : int)) : Exp -/
#guard_msgs in #check (Exp.annot (.ty .int) (Exp.binop .plus (Exp.var "x") (Exp.var "y")) : Exp)

-- Nested type: ref of arrow
/-- info: pl_ty(ref(int → bool)) : Ty -/
#guard_msgs in #check (Ty.ref (.arrow .int .bool) : Ty)

-- Typed binder with anonymous function name round-trips
/-- info: pl(fun _, x) : Exp -/
#guard_msgs in #check (Exp.letrec .anon .anon (Exp.var "x") : Exp)

end Tests

end ProbLang
