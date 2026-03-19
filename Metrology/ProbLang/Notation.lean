import Lean.PrettyPrinter.Delaborator
import Metrology.ProbLang.Syntax

namespace ProbLang

-- TODO: Add pl_pat syntax category and match expression notation
-- TODO: Build metaprogram to desugar multi-arm pattern matching into match+case

open Lean Lean.PrettyPrinter Elab Parser

declare_syntax_cat pl_exp
declare_syntax_cat pl_ty
declare_syntax_cat pl_arg
declare_syntax_cat pl_pat

/-- embedding ProbLang expressions into terms -/
syntax:max "pl(" pl_exp ")" : term
/-- embedding ProbLang binders into terms -/
syntax:max "pl_binder(" binderIdent ")" : term
/-- embedding ProbLang typed binders into terms -/
syntax:max "pl_binder(" "(" ident " : " pl_ty ")" ")" : term
/-- embedding ProbLang types into terms -/
syntax:max "pl_ty(" pl_ty ")" : term
/-- embedding ProbLang patterns into terms -/
syntax:max "pl_pat(" pl_pat ")" : term

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
syntax:max "tape" : pl_ty

/-- Pattern syntax -/
syntax:max "_" : pl_pat
syntax:max ident : pl_pat
syntax:max "#" term:max : pl_pat
syntax:max "(" pl_pat ")" : pl_pat
syntax:max "(" pl_pat ", " pl_pat ")" : pl_pat
syntax:max "inl(" pl_pat ")" : pl_pat
syntax:max "inr(" pl_pat ")" : pl_pat
syntax:max "(" pl_pat " : " pl_ty ")" : pl_pat

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
syntax:65 pl_exp:65 " + " pl_exp:66 : pl_exp
syntax:65 pl_exp:65 " - " pl_exp:66 : pl_exp
syntax:70 pl_exp:70 " * " pl_exp:71 : pl_exp
syntax:60 pl_exp:60 " && " pl_exp:61 : pl_exp
syntax:55 pl_exp:55 " || " pl_exp:56 : pl_exp
syntax:58 pl_exp:58 " ^^ " pl_exp:59 : pl_exp
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
/-- Pattern-matching case with one or more arms. Last arm fails if no match. -/
syntax:10 "case " pl_exp " | " pl_pat " => " pl_exp:10 (" | " pl_pat " => " pl_exp:10)* : pl_exp

/-- State -/
syntax:100 "alloc(" pl_exp ")" : pl_exp
syntax:80 "!" pl_exp:80 : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80 : pl_exp

/-- Random -/
syntax:100 "tape(" pl_exp ")" : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")" : pl_exp

/-- Scrutinize (pattern match) -/
syntax:10 "scrut " pl_exp " with " pl_pat : pl_exp

/-- Encryption -/
syntax:100 "enc_aes128(" pl_exp ", " pl_exp ", " pl_exp ")" : pl_exp
syntax:100 "dec_aes128(" pl_exp ", " pl_exp ", " pl_exp ")" : pl_exp

/-- Failure -/
syntax:max "fail" : pl_exp

/-- Destructuring let!: let! pat := expr; body  (fails if pattern doesn't match) -/
syntax:10 "let! " pl_pat " := " pl_exp:10 "; " pl_exp:1 : pl_exp

/-- Assertion -/
syntax:100 "assert(" pl_exp ")" : pl_exp

-- Keywords that may not be used as variable or binder names in ProbLang.
-- The Lean-level keywords (if, then, else, let, fun, rec, case) are already
-- rejected by the Lean lexer before our rules fire, but are listed here for
-- completeness.
private def reservedKeywords : List String :=
  ["fst", "snd", "inl", "inr", "alloc", "tape", "rand", "fail", "scrut", "enc_aes128", "dec_aes128",
   "if", "then", "else", "let", "fun", "rec", "case",
   "__scrut", "__bind"]

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
  | `(pl_ty($τ1 × $τ2))    => `(Ty.prod pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 + $τ2))    => `(Ty.sum pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty($τ1 → $τ2))   => `(Ty.arrow pl_ty($τ1) pl_ty($τ2))
  | `(pl_ty(ref($τ)))      => `(Ty.ref pl_ty($τ))
  | `(pl_ty(tape))         => `(Ty.tape)

/-- elaborating patterns -/
macro_rules
  | `(pl_pat(_))                  => `(Pat.var .anon)
  | `(pl_pat($i:ident))           => do
    checkNotReserved i
    `(Pat.var (.named $(Syntax.mkStrLit i.getId.toString)))
  | `(pl_pat(# $e))               => `(Pat.lit $e)
  | `(pl_pat(($p)))               => `(pl_pat($p))
  | `(pl_pat(($p1, $p2)))         => `(Pat.pair pl_pat($p1) pl_pat($p2))
  | `(pl_pat(inl($p)))            => `(Pat.inl pl_pat($p))
  | `(pl_pat(inr($p)))            => `(Pat.inr pl_pat($p))
  | `(pl_pat(($p : $τ)))          => `(Pat.annot (.ty pl_ty($τ)) pl_pat($p))

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

/-- Given a pattern and a term representing the bindings expression,
    wrap `body` in a chain of `let` bindings that project each variable
    from the bindings structure.

    The bindings structure mirrors the pattern:
    - `var x`     → bindings = the matched value;  emit `let x := bindings; body`
    - `_`         → bindings = the matched value;  emit `body` (no binding)
    - `lit _`     → bindings = unit;  emit `body` (no binding)
    - `pair p q`  → bindings = (b1, b2);  recurse on p with fst, q with snd
    - `inl p`     → bindings = sub;  recurse on p
    - `inr p`     → bindings = sub;  recurse on p
    - `annot _ p` → bindings = sub;  recurse on p
    - `(p)`       → transparent parens;  recurse on p -/
partial def patBindings [Monad m] [MonadRef m] [MonadQuotation m]
    (pat : TSyntax `pl_pat) (bindings : TSyntax `pl_exp) (body : TSyntax `pl_exp) :
    m (TSyntax `pl_exp) := do
  match pat with
  | `(pl_pat|$i:ident) =>
    `(pl_exp| let $i:ident := $bindings; $body)
  | `(pl_pat|_) =>
    pure body
  | `(pl_pat|# $_) =>
    pure body
  | `(pl_pat|($p)) =>
    patBindings p bindings body
  | `(pl_pat|($p1, $p2)) => do
    let inner ← patBindings p2 (← `(pl_exp| snd($bindings))) body
    patBindings p1 (← `(pl_exp| fst($bindings))) inner
  | `(pl_pat|inl($p)) =>
    patBindings p bindings body
  | `(pl_pat|inr($p)) =>
    patBindings p bindings body
  | `(pl_pat|($p : $_)) =>
    patBindings p bindings body
  | _ => pure body

/-- Build a single case arm: `Exp.case (scrut scrutVar pat) (fun b => <project> body) (fun _ => fallback)` -/
partial def buildCaseArm [Monad m] [MonadRef m] [MonadQuotation m]
    (scrutVar : TSyntax `pl_exp) (pat : TSyntax `pl_pat) (body : TSyntax `pl_exp)
    (fallback : Term) : m Term := do
  let bVar ← `(pl_exp| {Exp.var "__bind"})
  let projected ← patBindings pat bVar body
  `(Exp.case
      (Exp.scrut pl($scrutVar) pl_pat($pat))
      (Exp.letrec .anon (Binder.named "__bind") pl($projected))
      (Exp.letrec .anon .anon $fallback))

/-- Build a chain of case arms, with fail at the end. -/
partial def buildCaseChain [Monad m] [MonadRef m] [MonadQuotation m]
    (scrutVar : TSyntax `pl_exp)
    (pats : Array (TSyntax `pl_pat)) (bodies : Array (TSyntax `pl_exp)) : m Term := do
  -- Base: fail (will be wrapped in a lambda by buildCaseArm)
  let mut result ← `(Exp.fail)
  -- Build from last arm to first
  for i in List.range pats.size |>.reverse do
    result ← buildCaseArm scrutVar pats[i]! bodies[i]! result
  return result

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
  -- [commented out: old case elaboration, to be replaced by match+case]
  -- | `(pl(case $ec | $il:pl_arg => $el | $ir:pl_arg => $er)) =>
  --     `(Exp.case pl($ec) pl(rec _ $il := $el) pl(rec _ $ir := $er))
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
  -- Encryption
  | `(pl(enc_aes128($e1, $e2, $e3))) => `(Exp.enc_aes128 pl($e1) pl($e2) pl($e3))
  | `(pl(dec_aes128($e1, $e2, $e3))) => `(Exp.dec_aes128 pl($e1) pl($e2) pl($e3))
  -- Failure
  | `(pl(fail))                  => `(Exp.fail)
  -- Scrutinize (pattern match)
  | `(pl(scrut $e with $p))      => `(Exp.scrut pl($e) pl_pat($p))
  -- Destructuring let!:
  --   let! pat := e; body
  --     ↦  case (scrut e pat)
  --          | bindings => <project bindings> body
  --          | _ => fail
  | `(pl(let! $p := $e; $body)) => do
      let bVar ← `(pl_exp| {Exp.var "__bind"})
      let projected ← patBindings p bVar body
      `(Exp.case
          (Exp.scrut pl($e) pl_pat($p))
          (Exp.letrec .anon (Binder.named "__bind") pl($projected))
          (Exp.letrec .anon .anon Exp.fail))
  -- Pattern-matching case:
  --   case e | p1 => b1 | p2 => b2 | ...
  --     ↦  let tmp := e; <nested scrut+case chain, fail at end>
  | `(pl(case $e | $p => $b $[| $ps => $bs]*)) => do
      let tmpVar ← `(pl_exp| {Exp.var "__scrut"})
      let allPats := #[p] ++ ps
      let allBodies := #[b] ++ bs
      let chain ← buildCaseChain tmpVar allPats allBodies
      `(Exp.app
          (Exp.letrec .anon (Binder.named "__scrut") $chain)
          pl($e))
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

/-- Strip the `pl_pat(...)` wrapper to get a raw `pl_pat`. -/
partial def unpackPLPat [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_pat)
  | `(pl_pat($p)) => pure p
  | `($_)         => panic! "unknown pattern"

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
  | `($_) => do `(pl_ty(tape))

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

-- [commented out: old case unexpander, to be replaced by match+case]
-- @[app_unexpander Exp.case]
-- def unexpCase : Unexpander
--   | `($_ $ec pl(fun $il, $el) pl(fun $ir, $er)) => do
--     `(pl(case $(← unpackPLExp ec) | $il => $el | $ir => $er))
--   | _ => throw ()

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

@[app_unexpander Pat.var]
def unexpPatVar : Unexpander
  | `($_ $b) => do
    let bi ← unpackPLBinder b
    match bi with
    | `(pl_arg|$i:ident) => `(pl_pat($i:ident))
    | `(pl_arg|_) => `(pl_pat(_))
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Pat.lit]
def unexpPatLit : Unexpander
  | `($_ $b) => `(pl_pat(# $b))
  | _ => throw ()

@[app_unexpander Pat.pair]
def unexpPatPair : Unexpander
  | `($_ $p1 $p2) => do `(pl_pat(($(← unpackPLPat p1), $(← unpackPLPat p2))))
  | _ => throw ()

@[app_unexpander Pat.inl]
def unexpPatInl : Unexpander
  | `($_ $p) => do `(pl_pat(inl($(← unpackPLPat p))))
  | _ => throw ()

@[app_unexpander Pat.inr]
def unexpPatInr : Unexpander
  | `($_ $p) => do `(pl_pat(inr($(← unpackPLPat p))))
  | _ => throw ()

@[app_unexpander Pat.annot]
def unexpPatAnnot : Unexpander
  | `($_ $a $p) => do
    match a with
    | `(pl_ty($τ)) => `(pl_pat(($(← unpackPLPat p) : $τ)))
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Exp.enc_aes128]
def unexpEncAes128 : Unexpander
  | `($_ $e1 $e2 $e3) => do `(pl(enc_aes128($(← unpackPLExp e1), $(← unpackPLExp e2), $(← unpackPLExp e3))))
  | _ => throw ()

@[app_unexpander Exp.dec_aes128]
def unexpDecAes128 : Unexpander
  | `($_ $e1 $e2 $e3) => do `(pl(dec_aes128($(← unpackPLExp e1), $(← unpackPLExp e2), $(← unpackPLExp e3))))
  | _ => throw ()

@[app_unexpander Exp.scrut]
def unexpScrut : Unexpander
  | `($_ $e $p) => do `(pl(scrut $(← unpackPLExp e) with $(← unpackPLPat p)))
  | _ => throw ()

end ProbLang
