module

public meta import Lean.PrettyPrinter.Delaborator
public meta import Lean.Elab.Term
public import Metrology.ProbLang.Syntax.Syntax
public meta import Metrology.ProbLang.Syntax.Syntax

@[expose] public section

/-! # Surface syntax for ProbLang  -/

namespace ProbLang

open Lean Lean.Elab Lean.Elab.Term Lean.PrettyPrinter Lean.Meta Lean.Parser

/-- Controls rendering of ProbLang type annotations. `0` hide all, `1` show
    annotations on let/fun/rec binders only, `2` show every annotation. -/
meta register_option pp.problang.annot : Nat := {
  defValue := 0
  descr := "ProbLang: display type annotations (0=none | 1=binders | 2=all)"
}

declare_syntax_cat pl_exp
declare_syntax_cat pl_ty
declare_syntax_cat pl_arg
declare_syntax_cat pl_pat

syntax:max "pl(" pl_exp ")" : term
syntax:max "pl_ty(" pl_ty ")" : term
syntax:max "pl_pat(" pl_pat ")" : term

/-! ## `plBinderHint!`: attach display metadata to a binder expression.
`plBinderHint! name τ? e` elaborates `e` and wraps it in an `Expr.mdata`
carrying the binder's display name.

The `τ?` slot is parsed but currently unused — reserved for future type-annotation
rendering. -/

/-- Opaque syntax for the binder-hint wrapper; only the elaborator consumes it. -/
syntax (name := plBinderHint) "plBinderHint!" str term:max term:max : term

/-- Metadata key used by `plBinderHint!`. -/
meta def plBinderNameKey : Name := `ProbLang.plBinderName

@[term_elab plBinderHint]
meta def elabPlBinderHint : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let `(plBinderHint! $nameStr:str $_τ $eTerm) := stx
    | throwError "plBinderHint!: unexpected syntax"
  let e ← Lean.Elab.Term.elabTerm eTerm expectedType?
  let kv := ({} : KVMap).insert plBinderNameKey (DataValue.ofString nameStr.getString)
  return Expr.mdata kv e

/-- Binder argument: plain or typed. -/
syntax binderIdent : pl_arg
syntax "(" ident " : " pl_ty ")" : pl_arg

-- Types
syntax:max "int"                                                : pl_ty
syntax:max "bool"                                               : pl_ty
syntax:max "unit"                                               : pl_ty
syntax:max "(" pl_ty ")"                                        : pl_ty
syntax:35 pl_ty:36 " × " pl_ty:35                               : pl_ty
syntax:30 pl_ty:31 " + " pl_ty:30                               : pl_ty
syntax:25 pl_ty:26 " → " pl_ty:25                              : pl_ty
syntax:max "ref(" pl_ty ")"                                     : pl_ty
syntax:max "tape"                                               : pl_ty

-- Patterns
syntax:max "_"                                                  : pl_pat
syntax:max ident                                                : pl_pat
syntax:max "#" term:max                                         : pl_pat
syntax:max "(" pl_pat ")"                                       : pl_pat
syntax:max "(" pl_pat ", " pl_pat ")"                           : pl_pat
syntax:max "inl(" pl_pat ")"                                    : pl_pat
syntax:max "inr(" pl_pat ")"                                    : pl_pat
syntax:max "(" pl_pat " : " pl_ty ")"                           : pl_pat

-- Expressions
syntax:max "{" term "}"                                         : pl_exp
syntax:max "#" term:max                                         : pl_exp
syntax:max ident                                                : pl_exp
syntax:max "(" pl_exp ")"                                       : pl_exp
syntax:max "(" pl_exp " : " pl_ty ")"                           : pl_exp
syntax:65 pl_exp:65 " + " pl_exp:66                             : pl_exp
syntax:65 pl_exp:65 " - " pl_exp:66                             : pl_exp
syntax:70 pl_exp:70 " * " pl_exp:71                             : pl_exp
syntax:70 pl_exp:70 " / " pl_exp:71                             : pl_exp
syntax:70 pl_exp:70 " % " pl_exp:71                             : pl_exp
syntax:50 pl_exp:50 " < " pl_exp:50                             : pl_exp
syntax:50 pl_exp:50 " <= " pl_exp:50                            : pl_exp
syntax:60 pl_exp:60 " && " pl_exp:61                            : pl_exp
syntax:55 pl_exp:55 " || " pl_exp:56                            : pl_exp
syntax:58 pl_exp:58 " ^^ " pl_exp:59                            : pl_exp
syntax:50 pl_exp:50 " = " pl_exp:50                             : pl_exp
syntax:10 "if " pl_exp " then " pl_exp " else " pl_exp          : pl_exp
syntax:75 "~" pl_exp:75                                         : pl_exp
syntax:75 "-" pl_exp:75                                         : pl_exp
syntax:100 pl_exp:100 ppSpace pl_exp:101                        : pl_exp
syntax:10 "let " pl_arg " := " pl_exp:10 "; " pl_exp:1          : pl_exp
syntax:5 pl_exp:6 "; " pl_exp:5                                 : pl_exp
syntax:10 "fun" pl_arg+ ", " pl_exp:10                          : pl_exp
syntax:10 "rec " pl_arg ppSpace pl_arg+ " := " pl_exp:10        : pl_exp
syntax:max "(" pl_exp ", " pl_exp,+ ")"                         : pl_exp
syntax:100 "fst(" pl_exp ")"                                    : pl_exp
syntax:100 "snd(" pl_exp ")"                                    : pl_exp
syntax:100 "inl(" pl_exp ")"                                    : pl_exp
syntax:100 "inr(" pl_exp ")"                                    : pl_exp
syntax:10 "case " pl_exp " | " pl_pat " => " pl_exp:10
          (" | " pl_pat " => " pl_exp:10)*                      : pl_exp
syntax:100 "alloc(" pl_exp ")"                                  : pl_exp
syntax:80 "!" pl_exp:80                                         : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80                            : pl_exp
syntax:100 "tape(" pl_exp ")"                                   : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")"                       : pl_exp
syntax:10 "scrut " pl_exp " with " pl_pat                       : pl_exp
syntax:max "fail"                                               : pl_exp
syntax:10 "let! " pl_pat " := " pl_exp:10 "; " pl_exp:1         : pl_exp
syntax:100 "assert(" pl_exp ")"                                 : pl_exp

meta def reservedKeywords : List String :=
  ["fst", "snd", "inl", "inr", "alloc", "tape", "rand", "fail", "scrut",
   "if", "then", "else", "let", "fun", "rec", "case"]

meta def checkNotReserved (i : Lean.Ident) : TermElabM Unit := do
  let s := i.getId.toString
  if reservedKeywords.contains s then
    throwErrorAt i "'{s}' is a reserved keyword in ProbLang and cannot be used as an identifier"

/-! ## Type elaboration -/

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

/-! ## Pattern elaboration -/

macro_rules
  | `(pl_pat(_))                  => `(Pat.wildcard)
  | `(pl_pat($_:ident))           => `(Pat.wildcard)
  | `(pl_pat(# $e))               => `(Pat.lit $e)
  | `(pl_pat(($p)))               => `(pl_pat($p))
  | `(pl_pat(($p1, $p2)))         => `(Pat.pair pl_pat($p1) pl_pat($p2))
  | `(pl_pat(inl($p)))            => `(Pat.inl pl_pat($p))
  | `(pl_pat(inr($p)))            => `(Pat.inr pl_pat($p))

/-! ## Expression elaboration -/

/-- Map from Lean identifier names to the intenral atom assigned at binding time. -/
abbrev NameEnv := Lean.NameMap Var

/-- Allocator state held in an `IO.Ref` for the duration of one `pl(…)` call:
    just a fresh-atom counter for binder gensyms. -/
structure AtomState where
  next : Nat := 0

/-- Generate a fresh atom -/
meta def genAtom (st : IO.Ref AtomState) : TermElabM Var := do
  let s ← st.get
  st.set { next := s.next + 1 }
  return .internal s.next

/-- A named binder: its Lean identifier, its fvar atom, and optional type annot. -/
structure NamedBinder where
  ident : Lean.Ident
  atom  : Var
  ty    : Option (TSyntax `pl_ty)

/-- Allocate a fresh atom for a named binder, check it isn't reserved, and
    return the `NamedBinder` together with an env extended with its binding. -/
meta def bindNamed (st : IO.Ref AtomState) (env : NameEnv) (i : Lean.Ident) (ty : Option (TSyntax `pl_ty)) :
    TermElabM (NamedBinder × NameEnv) := do
  checkNotReserved i
  let atom ← genAtom st
  return ({ ident := i, atom, ty }, env.insert i.getId atom)

meta def quoteVar : Var → TermElabM Term
  | .named s    => `(Var.named $(Syntax.mkStrLit s))
  | .internal n => `(Var.internal $(Syntax.mkNatLit n))

/-! ### Smart term constructors
These constructors bind any additional metadata to the term via `plBinderHint!`-/

/-- Render an `Option Ty` syntax term from an optional `pl_ty`. -/
meta def tyOptTerm (τ : Option (TSyntax `pl_ty)) : TermElabM Term := do
  match τ with
  | some τ' => `((some pl_ty($τ')))
  | none    => `((none : Option Ty))

/-- Emit `plBinderHint! name τ (head body)` where `head` is `Exp.lam` or `Exp.fix`. -/
meta def wrapHint (head : Term) (name : Option String) (τ : Option (TSyntax `pl_ty))
    (body : Term) : TermElabM Term := do
  let nm := name.getD "_"
  `(plBinderHint! $(Syntax.mkStrLit nm) $(← tyOptTerm τ) ($head $body))

/-- Anonymous `Exp.lam` wrapping `body` (no `close`, no name). -/
meta def mkAnonLam (body : Term) : TermElabM Term := do
  wrapHint (← `(Exp.lam)) none none body

/-- Anonymous `λ. close body atom` — used for the case/let! scrutinee binder
    where the name is synthetic (no user ident to display). -/
meta def closeAnonLam (body : Term) (atom : Var) : TermElabM Term := do
  let closed ← ``(Exp.close $body $(← quoteVar atom))
  wrapHint (← `(Exp.lam)) none none closed

/-- Named-binder helper: close `body` over `b.atom`, wrap in `head` (`Exp.lam`
    or `Exp.fix`) with display name/type taken from `b`. -/
meta def closeNamedHead (head : Term) (b : NamedBinder) (body : Term) : TermElabM Term := do
  let closed ← ``(Exp.close $body $(← quoteVar b.atom))
  wrapHint head (some b.ident.getId.toString) b.ty closed

meta def mkNamedLam (b : NamedBinder) (body : Term) : TermElabM Term := do
  closeNamedHead (← `(Exp.lam)) b body

meta def mkNamedFix (b : NamedBinder) (body : Term) : TermElabM Term := do
  closeNamedHead (← `(Exp.fix)) b body

mutual

/-- Elaborate a `pl_exp` into an `Expr : Exp` under the given name env and
    atom-allocator `st`. -/
meta partial def elabPL (env : NameEnv) (st : IO.Ref AtomState) :
    TSyntax `pl_exp → TermElabM Term
  | `(pl_exp|($e : $τ)) => do
      `(Exp.annotated pl_ty($τ) $(← elabPL env st e))
  | `(pl_exp|($e))         => elabPL env st e
  | `(pl_exp|{$t})         => `(($t : Exp))
  | `(pl_exp|# $n:num)     => `(Exp.lit (.int $n))
  | `(pl_exp|#true)        => `(Exp.lit (.bool true))
  | `(pl_exp|#false)       => `(Exp.lit (.bool false))
  | `(pl_exp|# $e)         => `(Exp.lit $e)
  | `(pl_exp|$i:ident)     => do
      checkNotReserved i
      let atomStr := env.find? i.getId |>.getD i.getId.toString
      `(Exp.fvar $(← quoteVar atomStr))
  -- Binary / unary ops
  | `(pl_exp|$e1 + $e2)    => do `(Exp.binop .plus  $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 - $e2)    => do `(Exp.binop .minus $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 * $e2)    => do `(Exp.binop .mult  $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 / $e2)    => do `(Exp.binop .div   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 % $e2)    => do `(Exp.binop .mod   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 < $e2)    => do `(Exp.binop .lt    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 <= $e2)   => do `(Exp.binop .le    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 && $e2)   => do `(Exp.binop .and   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 || $e2)   => do `(Exp.binop .or    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 ^^ $e2)   => do `(Exp.binop .xor   $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|$e1 = $e2)    => do `(Exp.binop .eq    $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|~$e)          => do `(Exp.unop  .neg   $(← elabPL env st e))
  | `(pl_exp|-$e)          => do `(Exp.unop  .minus $(← elabPL env st e))
  | `(pl_exp|if $ec then $et else $ef) => do
      `(Exp.cond $(← elabPL env st ec) $(← elabPL env st et) $(← elabPL env st ef))
  | `(pl_exp|$e1 $e2)      => do `(Exp.app $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|fun $x:pl_arg $xs:pl_arg* , $body) => do
      -- Curry extra args into nested `fun`s; delegate each binder to `elabBindArg`.
      let body' ← if xs.size = 0 then pure body else `(pl_exp|fun $xs*, $body)
      elabBindArg env st x body' mkNamedLam
  | `(pl_exp|rec $f:pl_arg $x:pl_arg $xs:pl_arg* := $body) => do
      -- `rec f x ...` desugars to `fix (λ f. λ x. ...)`. `f`'s binder uses
      -- `Exp.fix`; `x` and any extras nest inside as regular `fun`s.
      let lamBody : TSyntax `pl_exp ← `(pl_exp|fun $x $xs*, $body)
      elabBindArg env st f lamBody mkNamedFix
  | `(pl_exp|($e1, $e2))         => do `(Exp.pair $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|($e1, $e2, $es,*))  => do
      let rest ← `(pl_exp|($e2, $es,*))
      `(Exp.pair $(← elabPL env st e1) $(← elabPL env st rest))
  | `(pl_exp|fst($e))            => do `(Exp.fst $(← elabPL env st e))
  | `(pl_exp|snd($e))            => do `(Exp.snd $(← elabPL env st e))
  | `(pl_exp|inl($e))            => do `(Exp.inl $(← elabPL env st e))
  | `(pl_exp|inr($e))            => do `(Exp.inr $(← elabPL env st e))
  | `(pl_exp|alloc($e))          => do `(Exp.alloc $(← elabPL env st e))
  | `(pl_exp|! $e)               => do `(Exp.load $(← elabPL env st e))
  | `(pl_exp|$e1 ← $e2)         => do `(Exp.store $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|tape($e))           => do `(Exp.tape $(← elabPL env st e))
  | `(pl_exp|rand($e1, $e2))     => do `(Exp.rand $(← elabPL env st e1) $(← elabPL env st e2))
  | `(pl_exp|let $a:pl_arg := $e1; $e2) => do
      let v1 ← elabPL env st e1
      let lam ← elabBindArg env st a e2 mkNamedLam
      `(Exp.app $lam $v1)
  | `(pl_exp|$e1; $e2) => do
      let v1 ← elabPL env st e1
      let lam ← mkAnonLam (← elabPL env st e2)
      `(Exp.app $lam $v1)
  | `(pl_exp|scrut $e with $p)   => do `(Exp.scrut $(← elabPL env st e) pl_pat($p))
  | `(pl_exp|let! $p:pl_pat := $e; $body) => do
      -- Desugar to a single-branch `case`; the `case` arm handles everything.
      elabPL env st (← `(pl_exp|case $e | $p => $body))
  | `(pl_exp|case $e | $p:pl_pat => $b $[| $ps:pl_pat => $bs]*) => do
      -- Build `(λ scrut. <chain>) e`, where `<chain>` matches `scrut` against
      -- each pattern right-to-left, falling through to `fail`.
      let scrutAtom ← genAtom st
      let chain ← buildCaseChain env st scrutAtom (#[p] ++ ps) (#[b] ++ bs)
      let lam ← closeAnonLam chain scrutAtom
      `(Exp.app $lam $(← elabPL env st e))
  | `(pl_exp|fail)               => `(Exp.fail)
  | `(pl_exp|assert($e))         => do
      elabPL env st (← `(pl_exp|if $e then #.unit else fail))
  | e => throwErrorAt e s!"unrecognised pl expression: {e}"

/-- Elaborate `body` under a single `pl_arg` binder. Anonymous `_` wraps in
    `mkAnonLam`; a named binder allocates a fresh atom, extends `env`, and
    wraps via `named` (`mkNamedLam` or `mkNamedFix`). -/
meta partial def elabBindArg (env : NameEnv) (st : IO.Ref AtomState)
    (arg : TSyntax `pl_arg) (body : TSyntax `pl_exp)
    (named : NamedBinder → Term → TermElabM Term) : TermElabM Term := do
  match arg with
  | `(pl_arg|$i:ident) =>
      let (b, env') ← bindNamed st env i none
      named b (← elabPL env' st body)
  | `(pl_arg|$_:binderIdent) => mkAnonLam (← elabPL env st body)
  | `(pl_arg|($i:ident : $τ)) =>
      let (b, env') ← bindNamed st env i (some τ)
      named b (← elabPL env' st body)
  | _ => throwErrorAt arg "unrecognised pl_arg"

/-- Build one branch of a `case`/`let!`: allocate a fresh atom, project
    pattern variables out of it, and wrap in `λ atom. <projected>`. -/
meta partial def mkCaseBranch (env : NameEnv) (st : IO.Ref AtomState)
    (pat : TSyntax `pl_pat) (body : TSyntax `pl_exp) : TermElabM Term := do
  let atom ← genAtom st
  let projected ← projectPattern env st pat atom body
  closeAnonLam projected atom

/-- Wrap `body` in projection applications that destructure the value at
    fvar `scrutAtom` according to `pat`.

Two passes over `pat`:
  1. `collect` allocates a fresh atom for each ident the pattern binds,
     extending `env`; the body is then elaborated under the full env.
  2. `emit` walks `pat` outside-in, building nested `fst`/`snd`/identity
     projections of `scrutAtom` and wrapping `body` in one `(λ v. …) proj`
     application per ident binder. -/
meta partial def projectPattern (env : NameEnv) (st : IO.Ref AtomState)
    (pat : TSyntax `pl_pat) (scrutAtom : Var)
    (body : TSyntax `pl_exp) : TermElabM Term := do
  let rec collect (env : NameEnv) (acc : Lean.NameMap NamedBinder)
      (pat : TSyntax `pl_pat) : TermElabM (NameEnv × Lean.NameMap NamedBinder) := do
    match pat with
    | `(pl_pat|$i:ident) => do
        let (b, env') ← bindNamed st env i none
        return (env', acc.insert i.getId b)
    | `(pl_pat|($p)) | `(pl_pat|($p : $_))
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => collect env acc p
    | `(pl_pat|($p1, $p2)) => do
        let (env1, acc1) ← collect env acc p1
        collect env1 acc1 p2
    | _ => return (env, acc)
  let (envFull, binders) ← collect env ∅ pat
  let bodyTerm ← elabPL envFull st body
  let scrutExp : TSyntax `pl_exp ← `(pl_exp|{Exp.fvar $(← quoteVar scrutAtom)})
  let rec emit (pat : TSyntax `pl_pat) (proj : TSyntax `pl_exp)
      (inner : Term) : TermElabM Term := do
    match pat with
    | `(pl_pat|$i:ident) => do
        let some b := binders.find? i.getId
          | throwError "projectPattern: atom not found for {i.getId}"
        `(Exp.app $(← mkNamedLam b inner) $(← elabPL env st proj))
    | `(pl_pat|($p)) | `(pl_pat|($p : $_))
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => emit p proj inner
    | `(pl_pat|($p1, $p2)) => do
        let rhs ← emit p2 (← `(pl_exp|snd($proj))) inner
        emit p1 (← `(pl_exp|fst($proj))) rhs
    | _ => return inner
  emit pat scrutExp bodyTerm

/-- Fold the branches of `case v | p₁ => b₁ | … | pₙ => bₙ` right-to-left
    into nested `Exp.case` nodes, with `Exp.fail` as the innermost fallback.
    The scrutinee is an `Exp.fvar scrutAtom` shared across all branches. -/
meta partial def buildCaseChain (env : NameEnv) (st : IO.Ref AtomState)
    (scrutAtom : Var)
    (pats : Array (TSyntax `pl_pat)) (bodies : Array (TSyntax `pl_exp)) : TermElabM Term := do
  let scrutExp : Term ← `(Exp.fvar $(← quoteVar scrutAtom))
  let mut result : Term ← `(Exp.fail)
  for i in List.range pats.size |>.reverse do
    let branch ← mkCaseBranch env st pats[i]! bodies[i]!
    let fallback ← mkAnonLam result
    result ← `(Exp.case (Exp.scrut $scrutExp pl_pat($(pats[i]!))) $branch $fallback)
  return result

end

/-! ## Delaborator support

Display names are attached per-term via `plFvarHint!` / `plBinderHint!`
mdata wrappers (`Expr.mdata` with `ProbLang.plFvarName` / `plBinderName`
keys). The kernel ignores mdata; only delab consults it. -/

elab_rules : term
  | `(pl($e)) => do
      let st ← IO.mkRef ({} : AtomState)
      let t ← elabPL {} st e
      Lean.Elab.Term.elabTerm t none

end ProbLang

/-! ## Unexpanders (pretty-printing) -/

namespace ProbLang

open Lean Lean.PrettyPrinter

/-- Strip the `pl(...)` wrapper to get a raw `pl_exp`, or fall back to `{t}` escape. -/
meta def unpackPLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_exp)
  | `(pl($e)) => `(pl_exp|$e)
  | `($t)     => `(pl_exp|{$t})

/-- Strip the `pl_ty(...)` wrapper to get a raw `pl_ty`. -/
meta def unpackPLTy [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_ty)
  | `(pl_ty($τ)) => pure τ
  | `($_)        => panic! "unknown type"

/-- Strip the `pl_pat(...)` wrapper to get a raw `pl_pat`. -/
meta def unpackPLPat [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_pat)
  | `(pl_pat($p)) => pure p
  | `($_)         => panic! "unknown pattern"

/-- Flatten nested `fun`/`rec` for display. -/
partial def unexpFun : Term → UnexpandM Term
  | `(pl(fun $xs*, $e)) => do
    match e with
    | `(pl(fun $ys*, $body)) => unexpFun (← `(pl(fun $xs* $ys*, $body)))
    | _ => return (← `(pl(fun $xs*, $e)))
  | `(pl(rec $f $xs* := $e)) => do
    match (e : TSyntax `pl_exp) with
    | `(pl_exp| fun $ys*, $body) => unexpFun (← `(pl(rec $f $xs* $ys* := $body)))
    | _ => return (← `(pl(rec $f $xs* := $e)))
  | x => return x

/-! ### Types -/

@[app_unexpander Ty.int]
meta def unexpTyInt : Unexpander | `($_) => `(pl_ty(int))
@[app_unexpander Ty.bool]
meta def unexpTyBool : Unexpander | `($_) => `(pl_ty(bool))
@[app_unexpander Ty.unit]
meta def unexpTyUnit : Unexpander | `($_) => `(pl_ty(unit))
@[app_unexpander Ty.prod]
meta def unexpTyProd : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) × $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.sum]
meta def unexpTySum : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) + $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.arrow]
meta def unexpTyArrow : Unexpander
  | `($_ $τ1 $τ2) => do `(pl_ty($(← unpackPLTy τ1) → $(← unpackPLTy τ2)))
  | _ => throw ()
@[app_unexpander Ty.ref]
meta def unexpTyRef : Unexpander
  | `($_ $τ) => do `(pl_ty(ref($(← unpackPLTy τ))))
  | _ => throw ()
@[app_unexpander Ty.tape]
meta def unexpTyTape : Unexpander
  | `($_) => do `(pl_ty(tape))

/-! ### Patterns -/

@[app_unexpander Pat.wildcard]
meta def unexpPatWildcard : Unexpander
  | `($_) => `(pl_pat(_))

@[app_unexpander Pat.lit]
meta def unexpPatLit : Unexpander
  | `($_ $b) => `(pl_pat(# $b))
  | _ => throw ()

@[app_unexpander Pat.pair]
meta def unexpPatPair : Unexpander
  | `($_ $p1 $p2) => do `(pl_pat(($(← unpackPLPat p1), $(← unpackPLPat p2))))
  | _ => throw ()

@[app_unexpander Pat.inl]
meta def unexpPatInl : Unexpander
  | `($_ $p) => do `(pl_pat(inl($(← unpackPLPat p))))
  | _ => throw ()

@[app_unexpander Pat.inr]
meta def unexpPatInr : Unexpander
  | `($_ $p) => do `(pl_pat(inr($(← unpackPLPat p))))
  | _ => throw ()

/-! ### Literals / atomic expressions -/

@[app_unexpander Exp.lit]
meta def unexpLit : Unexpander
  | `($_ $arg) => `(pl(# $arg))
  | _ => throw ()

@[app_unexpander BaseLit.int]
meta def unexpBLInt : Unexpander
  | `($_ (Int.ofNat $n:num)) => `($n)
  | `($_ $z)                 => pure z
  | _                        => throw ()

@[app_unexpander BaseLit.bool]
meta def unexpBLBool : Unexpander
  | `($_ $b) => pure b
  | _ => throw ()

@[app_unexpander BaseLit.unit]
meta def unexpBLUnit : Unexpander := fun _ => `(())

@[app_unexpander Exp.fail]
meta def unexpFail : Unexpander
  | `($_) => do `(pl(fail))

/-! ### Operators -/

@[app_unexpander Exp.binop]
meta def unexpBinop : Unexpander
  | `($_ BinOp.plus  $e1 $e2) => do `(pl(($(← unpackPLExp e1) + $(← unpackPLExp e2))))
  | `($_ BinOp.minus $e1 $e2) => do `(pl(($(← unpackPLExp e1) - $(← unpackPLExp e2))))
  | `($_ BinOp.mult  $e1 $e2) => do `(pl(($(← unpackPLExp e1) * $(← unpackPLExp e2))))
  | `($_ BinOp.div   $e1 $e2) => do `(pl(($(← unpackPLExp e1) / $(← unpackPLExp e2))))
  | `($_ BinOp.mod   $e1 $e2) => do `(pl(($(← unpackPLExp e1) % $(← unpackPLExp e2))))
  | `($_ BinOp.lt    $e1 $e2) => do `(pl(($(← unpackPLExp e1) < $(← unpackPLExp e2))))
  | `($_ BinOp.le    $e1 $e2) => do `(pl(($(← unpackPLExp e1) <= $(← unpackPLExp e2))))
  | `($_ BinOp.and   $e1 $e2) => do `(pl(($(← unpackPLExp e1) && $(← unpackPLExp e2))))
  | `($_ BinOp.or    $e1 $e2) => do `(pl(($(← unpackPLExp e1) || $(← unpackPLExp e2))))
  | `($_ BinOp.xor   $e1 $e2) => do `(pl(($(← unpackPLExp e1) ^^ $(← unpackPLExp e2))))
  | `($_ BinOp.eq    $e1 $e2) => do `(pl(($(← unpackPLExp e1) = $(← unpackPLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.unop]
meta def unexpUnop : Unexpander
  | `($_ UnOp.neg   $e) => do `(pl(~$(← unpackPLExp e)))
  | `($_ UnOp.minus $e) => do `(pl(-$(← unpackPLExp e)))
  | _ => throw ()

@[app_unexpander Exp.cond]
meta def unexpCond : Unexpander
  | `($_ $ec $et $ef) => do
    `(pl(if $(← unpackPLExp ec) then $(← unpackPLExp et) else $(← unpackPLExp ef)))
  | _ => throw ()

/-! ### Pairs / sums / projections -/

meta partial def unexpPair' : Term → UnexpandM Term
  | `(pl(($e1, ($e2, $e3,*)))) => do unexpPair' (← `(pl(($e1, $e2, $e3,*))))
  | x => return x

@[app_unexpander Exp.pair]
meta def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' (← `(pl(($(← unpackPLExp e1), $(← unpackPLExp e2)))))
  | _ => throw ()

@[app_unexpander Exp.fst]
meta def unexpFst : Unexpander
  | `($_ $e) => do `(pl(fst($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.snd]
meta def unexpSnd : Unexpander
  | `($_ $e) => do `(pl(snd($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inl]
meta def unexpInl : Unexpander
  | `($_ $e) => do `(pl(inl($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.inr]
meta def unexpInr : Unexpander
  | `($_ $e) => do `(pl(inr($(← unpackPLExp e))))
  | _ => throw ()

/-! ### State / random / scrut -/

@[app_unexpander Exp.alloc]
meta def unexpAlloc : Unexpander
  | `($_ $e) => do `(pl(alloc($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.load]
meta def unexpLoad : Unexpander
  | `($_ $e) => do `(pl(!$(← unpackPLExp e)))
  | _ => throw ()

@[app_unexpander Exp.store]
meta def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(pl($(← unpackPLExp e1) ← $(← unpackPLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.tape]
meta def unexpTape : Unexpander
  | `($_ $e) => do `(pl(tape($(← unpackPLExp e))))
  | _ => throw ()

@[app_unexpander Exp.rand]
meta def unexpRand : Unexpander
  | `($_ $e1 $e2) => do `(pl(rand($(← unpackPLExp e1), $(← unpackPLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.scrut]
meta def unexpScrut : Unexpander
  | `($_ $e $p) => do `(pl(scrut $(← unpackPLExp e) with $(← unpackPLPat p)))
  | _ => throw ()

/-! ### Binders: `Exp.lam` / `Exp.fix` with `MData` name hints -/

/-- Construct a `pl_arg` from a name-hint string. Monad-polymorphic so it
    works in both `UnexpandM` and `DelabM`. -/
meta def buildArgFromName [Monad m] [MonadRef m] [MonadQuotation m]
    (name : String) : m (TSyntax `pl_arg) := do
  if name = "_" then
    `(pl_arg|_)
  else
    let ident := Lean.mkIdent (Name.mkSimple name)
    `(pl_arg|$ident:ident)

/-- Strip a leading `Exp.close ... <atom>` so the lam body renders without
    explicit closing. -/
meta def stripClose [Monad m] [MonadRef m] [MonadQuotation m]
    (e : Term) : m Term := do
  match e with
  | `(Exp.close $body $_) => return body
  | _                     => return e

open Lean.PrettyPrinter.Delaborator in
/-- Delaborator dispatched when the `mdata` contains exactly our
    `ProbLang.plBinderName` key. Lean routes via `mdata.<singleKey>`. -/
@[delab mdata.ProbLang.plBinderName]
meta def delabPlBinderMeta : Delab := do
  let e ← SubExpr.getExpr
  let .mdata kv inner := e | failure
  let name := kv.getString plBinderNameKey ""
  if name.isEmpty then failure
  -- The inner `Expr` is `Exp.lam <body>` or `Exp.fix <body>`. Delab its
  -- argument under the `mdata → app → arg` path.
  let delabBody : Delab := SubExpr.withMDataExpr (SubExpr.withAppArg delab)
  let arg ← buildArgFromName name
  match inner with
  | .app (.const ``Exp.lam _) _ => do
      let bodyPL ← unpackPLExp (← stripClose (← delabBody))
      `(pl(fun $arg, $bodyPL))
  | .app (.const ``Exp.fix _) _ => do
      let bodyPL ← unpackPLExp (← stripClose (← delabBody))
      `(pl(rec $arg _ := $bodyPL))
  | _ => failure

/-! ### Applications — special-cased for `let` and `;`

A unary `λ` applied to an argument displays as either `let x := arg; body`
(named binder) or `arg; body` (anonymous). Everything else renders as a
plain application. -/

@[app_unexpander Exp.app]
meta def unexpApp : Unexpander
  | `($_ $fn $arg) => do
    let rhs ← unpackPLExp arg
    match fn with
    | `(pl(fun $a:pl_arg, $body)) =>
        match a with
        | `(pl_arg|$_:ident)        => `(pl(let $a := $rhs; $body))
        | `(pl_arg|($_:ident : $_)) => `(pl(let $a := $rhs; $body))
        | _                         => `(pl($rhs; $body))
    | _ => `(pl($(← unpackPLExp fn) $rhs))
  | _ => throw ()

/-! ### `Exp.annotated` delab (gated by `pp.problang.annot`) -/

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.annotated]
meta def delabExpAnnotated : Delab := do
  let e ← SubExpr.getExpr
  unless e.getAppNumArgs == 2 do failure
  let mode := pp.problang.annot.get (← getOptions)
  let eStx ← SubExpr.withAppArg delab
  if mode ≥ 2 then
    let τStx ← SubExpr.withAppFn (SubExpr.withAppArg delab)
    let eSyn ← unpackPLExp eStx
    let τSyn ← unpackPLTy τStx
    `(pl(($eSyn : $τSyn)))
  else
    pure eStx

/-! ### Free-variable display

Since `Var = String` and free identifiers elaborate to `Exp.fvar "x"`, we
can recover the display name straight from the string literal. -/

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.fvar]
meta def delabExpFvar : Delab := do
  let e ← SubExpr.getExpr
  unless e.getAppNumArgs == 1 do failure
  let_expr Var.named sLit := e.appArg! | failure
  let .lit (.strVal s) := sLit | failure
  `(pl($(Lean.mkIdent (Name.mkSimple s)):ident))

end ProbLang
