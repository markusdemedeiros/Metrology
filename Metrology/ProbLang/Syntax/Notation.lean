import Lean.PrettyPrinter.Delaborator
import Lean.Elab.Term
import Metrology.ProbLang.Syntax.Syntax

/-!
# Surface syntax for ProbLang (locally-nameless)

Elaborator-based surface syntax. Lean identifiers in the surface become
`Nat` atoms under LN; binders emit `Exp.close`; occurrences look up the
ambient atom environment. Name-hint wrappers (`Exp.lamN` / `Exp.fixN`)
preserve identifier names for pretty-printing.

## Grammar

- `pl_exp` : expressions (`rec`, `fun`, `let`, `let!`, `if`, `case`, ops, …)
- `pl_ty`  : types (int, bool, unit, ×, +, →, ref, tape)
- `pl_pat` : patterns (`_`, ident, literal, pairs, inl/inr)
- `pl_arg` : binder argument (`x` or `(x : τ)`)
-/

namespace ProbLang

open Lean Lean.Elab Lean.Elab.Term Lean.PrettyPrinter Lean.Meta Lean.Parser

/-- Controls rendering of ProbLang type annotations. `0` hide all, `1` show
    annotations on let/fun/rec binders only, `2` show every annotation. -/
register_option pp.problang.annot : Nat := {
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

/-- Binder argument: plain or typed. -/
syntax binderIdent : pl_arg
syntax "(" ident " : " pl_ty ")" : pl_arg

-- Types
syntax:max "int"      : pl_ty
syntax:max "bool"     : pl_ty
syntax:max "unit"     : pl_ty
syntax:max "(" pl_ty ")" : pl_ty
syntax:35 pl_ty:36 " × " pl_ty:35 : pl_ty
syntax:30 pl_ty:31 " + " pl_ty:30 : pl_ty
syntax:25 pl_ty:26 " → " pl_ty:25 : pl_ty
syntax:max "ref(" pl_ty ")" : pl_ty
syntax:max "tape"     : pl_ty

-- Patterns
syntax:max "_"                       : pl_pat
syntax:max ident                     : pl_pat
syntax:max "#" term:max              : pl_pat
syntax:max "(" pl_pat ")"            : pl_pat
syntax:max "(" pl_pat ", " pl_pat ")" : pl_pat
syntax:max "inl(" pl_pat ")"         : pl_pat
syntax:max "inr(" pl_pat ")"         : pl_pat
syntax:max "(" pl_pat " : " pl_ty ")" : pl_pat

-- Expressions
syntax:max "{" term "}"              : pl_exp
syntax:max "#" term:max              : pl_exp
syntax:max ident                     : pl_exp
syntax:max "(" pl_exp ")"            : pl_exp
syntax:max "(" pl_exp " : " pl_ty ")" : pl_exp

syntax:65 pl_exp:65 " + " pl_exp:66  : pl_exp
syntax:65 pl_exp:65 " - " pl_exp:66  : pl_exp
syntax:70 pl_exp:70 " * " pl_exp:71  : pl_exp
syntax:60 pl_exp:60 " && " pl_exp:61 : pl_exp
syntax:55 pl_exp:55 " || " pl_exp:56 : pl_exp
syntax:58 pl_exp:58 " ^^ " pl_exp:59 : pl_exp
syntax:50 pl_exp:50 " = " pl_exp:50  : pl_exp
syntax:10 "if " pl_exp " then " pl_exp " else " pl_exp : pl_exp
syntax:75 "~" pl_exp:75              : pl_exp
syntax:75 "-" pl_exp:75              : pl_exp
syntax:100 pl_exp:100 ppSpace pl_exp:101 : pl_exp
syntax:10 "let " pl_arg " := " pl_exp:10 "; " pl_exp:1 : pl_exp
syntax:5 pl_exp:6 "; " pl_exp:5      : pl_exp
syntax:10 "fun" pl_arg+ ", " pl_exp:10 : pl_exp
syntax:10 "rec " pl_arg ppSpace pl_arg+ " := " pl_exp:10 : pl_exp
syntax:max "(" pl_exp ", " pl_exp,+ ")" : pl_exp
syntax:100 "fst(" pl_exp ")"         : pl_exp
syntax:100 "snd(" pl_exp ")"         : pl_exp
syntax:100 "inl(" pl_exp ")"         : pl_exp
syntax:100 "inr(" pl_exp ")"         : pl_exp
syntax:10 "case " pl_exp " | " pl_pat " => " pl_exp:10
          (" | " pl_pat " => " pl_exp:10)* : pl_exp
syntax:100 "alloc(" pl_exp ")"       : pl_exp
syntax:80 "!" pl_exp:80              : pl_exp
syntax:80 pl_exp:80 " ← " pl_exp:80  : pl_exp
syntax:100 "tape(" pl_exp ")"        : pl_exp
syntax:100 "rand(" pl_exp ", " pl_exp ")" : pl_exp
syntax:10 "scrut " pl_exp " with " pl_pat : pl_exp
syntax:max "fail"                    : pl_exp
syntax:10 "let! " pl_pat " := " pl_exp:10 "; " pl_exp:1 : pl_exp
syntax:100 "assert(" pl_exp ")"      : pl_exp

private def reservedKeywords : List String :=
  ["fst", "snd", "inl", "inr", "alloc", "tape", "rand", "fail", "scrut",
   "if", "then", "else", "let", "fun", "rec", "case",
   "__scrut", "__bind"]

private def checkNotReserved (i : Lean.Ident) : TermElabM Unit := do
  let s := i.getId.toString
  if reservedKeywords.contains s then
    throwErrorAt i "'{s}' is a reserved keyword in ProbLang and cannot be used as an identifier"

/-! ## Type elaboration (pure macro) -/

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

/-! ## Pattern elaboration (pure macro) -/

macro_rules
  | `(pl_pat(_))                  => `(Pat.wildcard)
  | `(pl_pat($_:ident))           => `(Pat.wildcard)  -- identifier patterns bind; handled in `let!` / `case`
  | `(pl_pat(# $e))               => `(Pat.lit $e)
  | `(pl_pat(($p)))               => `(pl_pat($p))
  | `(pl_pat(($p1, $p2)))         => `(Pat.pair pl_pat($p1) pl_pat($p2))
  | `(pl_pat(inl($p)))            => `(Pat.inl pl_pat($p))
  | `(pl_pat(inr($p)))            => `(Pat.inr pl_pat($p))
  | `(pl_pat(($p : $_τ)))         => `(pl_pat($p))

/-! ## Expression elaboration (with name-env threading) -/

/-- Map from Lean identifier names to the `Nat` atom assigned at binding time. -/
abbrev NameEnv := Lean.NameMap Nat

/-- Deterministic mapping from Lean name → `Nat` atom. Uses `hash` so the
    same identifier always maps to the same atom. **Note:** shadowed bindings
    of the same identifier produce identical atoms, which currently means the
    *innermost* binder captures all occurrences. This is a known limitation;
    shadowed names should be unique for correctness. -/
private def atomOf (n : Lean.Name) (_scope : Nat) : Nat :=
  (hash n).toNat

/-- Extract the `ident` (or hole) and optional type from a `pl_arg`. -/
private def unpackArg (a : TSyntax `pl_arg) :
    TermElabM (Option Lean.Ident × Option (TSyntax `pl_ty)) := do
  match a with
  | `(pl_arg|$i:ident)         => return (some i, none)
  | `(pl_arg|$_:binderIdent)   => return (none, none)  -- `_`
  | `(pl_arg|($i:ident : $τ))  => return (some i, some τ)
  | _ => throwErrorAt a "unrecognised pl_arg"

mutual

/-- Elaborate a `pl_exp` into an `Expr : Exp` under the given name environment
    and fresh-atom counter. Returns the elaborated term. -/
partial def elabPL (env : NameEnv) (scope : Nat) :
    TSyntax `pl_exp → TermElabM Term
  | `(pl_exp|($e : $τ)) => do
      let e' ← elabPL env scope e
      `(Exp.annotated pl_ty($τ) $e')
  | `(pl_exp|($e))         => elabPL env scope e
  | `(pl_exp|{$t})         => `(($t : Exp))
  | `(pl_exp|# $n:num)     => `(Exp.lit (.int (Int.ofNat $n)))
  | `(pl_exp|#true)        => `(Exp.lit (.bool true))
  | `(pl_exp|#false)       => `(Exp.lit (.bool false))
  | `(pl_exp|# $e)         => `(Exp.lit $e)
  | `(pl_exp|$i:ident)     => do
      checkNotReserved i
      match env.find? i.getId with
      | some v => `(Exp.fvar $(Syntax.mkNatLit v))
      | none   =>
          -- Free (top-level) identifier: map via its name hash.
          let v := (hash i.getId).toNat
          `(Exp.fvar $(Syntax.mkNatLit v))
  -- Binary / unary ops
  | `(pl_exp|$e1 + $e2)    => do `(Exp.binop .plus  $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 - $e2)    => do `(Exp.binop .minus $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 * $e2)    => do `(Exp.binop .mult  $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 && $e2)   => do `(Exp.binop .and   $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 || $e2)   => do `(Exp.binop .or    $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 ^^ $e2)   => do `(Exp.binop .xor   $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|$e1 = $e2)    => do `(Exp.binop .eq    $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|~$e)          => do `(Exp.unop  .neg   $(← elabPL env scope e))
  | `(pl_exp|-$e)          => do `(Exp.unop  .minus $(← elabPL env scope e))
  | `(pl_exp|if $ec then $et else $ef) => do
      `(Exp.cond $(← elabPL env scope ec) $(← elabPL env scope et) $(← elabPL env scope ef))
  | `(pl_exp|$e1 $e2)      => do `(Exp.app $(← elabPL env scope e1) $(← elabPL env scope e2))
  -- `fun x, body` = `rec _ x := body` (no self-reference)
  | `(pl_exp|fun $x:pl_arg $xs:pl_arg* , $body) => do
      if xs.size = 0 then
        elabLam env scope x body
      else
        elabLam env scope x (← `(pl_exp|fun $xs*, $body))
  -- `rec f x [...xs] := body`
  | `(pl_exp|rec $f:pl_arg $x:pl_arg $xs:pl_arg* := $body) => do
      let inner ← if xs.size = 0 then
                    pure body
                  else
                    `(pl_exp|fun $xs*, $body)
      elabRec env scope f x inner
  -- Pairs
  | `(pl_exp|($e1, $e2))         => do `(Exp.pair $(← elabPL env scope e1) $(← elabPL env scope e2))
  | `(pl_exp|($e1, $e2, $es,*))  => do
      let rest ← `(pl_exp|($e2, $es,*))
      `(Exp.pair $(← elabPL env scope e1) $(← elabPL env scope rest))
  | `(pl_exp|fst($e))            => do `(Exp.fst $(← elabPL env scope e))
  | `(pl_exp|snd($e))            => do `(Exp.snd $(← elabPL env scope e))
  | `(pl_exp|inl($e))            => do `(Exp.inl $(← elabPL env scope e))
  | `(pl_exp|inr($e))            => do `(Exp.inr $(← elabPL env scope e))
  -- Heap
  | `(pl_exp|alloc($e))          => do `(Exp.alloc $(← elabPL env scope e))
  | `(pl_exp|! $e)               => do `(Exp.load $(← elabPL env scope e))
  | `(pl_exp|$e1 ← $e2)         => do `(Exp.store $(← elabPL env scope e1) $(← elabPL env scope e2))
  -- Random
  | `(pl_exp|tape($e))           => do `(Exp.tape $(← elabPL env scope e))
  | `(pl_exp|rand($e1, $e2))     => do `(Exp.rand $(← elabPL env scope e1) $(← elabPL env scope e2))
  -- Let = app of lam
  | `(pl_exp|let $a:pl_arg := $e1; $e2) => do
      let (iOpt, τOpt) ← unpackArg a
      let v1 ← elabPL env scope e1
      let body ← elabLamArg env scope iOpt τOpt e2
      `(Exp.app $body $v1)
  | `(pl_exp|$e1; $e2) => do
      -- sequencing: λ_. e2 applied to e1
      let v1 ← elabPL env scope e1
      let v2 ← elabPL env scope e2
      `(Exp.app (Exp.lamN "_" Option.none $v2) $v1)
  -- Scrutinize
  | `(pl_exp|scrut $e with $p)   => do `(Exp.scrut $(← elabPL env scope e) pl_pat($p))
  -- `let! pat := e; body` — destructure a scrutiny value
  | `(pl_exp|let! $p:pl_pat := $e; $body) => do
      let (patBindings, bindIdents) ← gatherPatIdents p
      -- Fresh atom for the anonymous bind temp
      let bindName := Lean.Name.mkSimple "__bind"
      let bindAtom := atomOf bindName scope
      let envBind := env.insert bindName bindAtom
      -- Project each pattern-bound ident out of `__bind` using fst/snd/inl/inr
      let projected ← projectPattern envBind (scope + 1) p (← `(pl_exp|{Exp.fvar $(Syntax.mkNatLit bindAtom)})) body patBindings bindIdents
      let bodyClose ← closeMaybe projected bindAtom (some "__bind") none
      `(Exp.case
         (Exp.scrut $(← elabPL env scope e) pl_pat($p))
         $bodyClose
         (Exp.lamN "_" Option.none Exp.fail))
  -- Pattern-match `case`
  | `(pl_exp|case $e | $p:pl_pat => $b $[| $ps:pl_pat => $bs]*) => do
      let allPats := #[p] ++ ps
      let allBodies := #[b] ++ bs
      let chain ← buildCaseChain env scope allPats allBodies
      let scrutName := Lean.Name.mkSimple "__scrut"
      let scrutAtom := atomOf scrutName scope
      let envScrut := env.insert scrutName scrutAtom
      let scrutVar ← `(pl_exp|{Exp.fvar $(Syntax.mkNatLit scrutAtom)})
      -- rebuild chain with __scrut in scope
      let chain2 ← buildCaseChainWith envScrut (scope + 1) scrutVar allPats allBodies
      let closed ← closeMaybe chain2 scrutAtom (some "__scrut") none
      `(Exp.app $closed $(← elabPL env scope e))
  | `(pl_exp|fail)               => `(Exp.fail)
  | `(pl_exp|assert($e))         => do
      elabPL env scope (← `(pl_exp|if $e then #.unit else fail))
  | e => throwErrorAt e s!"unrecognised pl expression: {e}"

/-- Emit `Exp.close body atom` (or `body` if `atom = none`), wrapped in a name hint. -/
partial def closeMaybe (body : Term) (atom : Nat) (name : Option String) (τ : Option (TSyntax `pl_ty))
    : TermElabM Term := do
  let closed ← `(Exp.close $body $(Syntax.mkNatLit atom))
  let nm := name.getD "_"
  let τExpr : Term ← match τ with
    | some τ' => `((some pl_ty($τ')))
    | none    => `((none : Option Ty))
  `(Exp.lamN $(Syntax.mkStrLit nm) $τExpr $closed)

partial def closeMaybeFix (body : Term) (atom : Nat) (name : Option String) (τ : Option (TSyntax `pl_ty))
    : TermElabM Term := do
  let closed ← `(Exp.close $body $(Syntax.mkNatLit atom))
  let nm := name.getD "_"
  let τExpr : Term ← match τ with
    | some τ' => `((some pl_ty($τ')))
    | none    => `((none : Option Ty))
  `(Exp.fixN $(Syntax.mkStrLit nm) $τExpr $closed)

/-- Elaborate `lam x. body` given a `pl_arg` and body. -/
partial def elabLam (env : NameEnv) (scope : Nat) (arg : TSyntax `pl_arg)
    (body : TSyntax `pl_exp) : TermElabM Term := do
  let (iOpt, τOpt) ← unpackArg arg
  elabLamArg env scope iOpt τOpt body

partial def elabLamArg (env : NameEnv) (scope : Nat)
    (iOpt : Option Lean.Ident) (τOpt : Option (TSyntax `pl_ty))
    (body : TSyntax `pl_exp) : TermElabM Term := do
  match iOpt with
  | some i =>
      checkNotReserved i
      let nm := i.getId
      let atom := atomOf nm scope
      let env' := env.insert nm atom
      let body' ← elabPL env' (scope + 1) body
      closeMaybe body' atom (some nm.toString) τOpt
  | none =>
      let body' ← elabPL env (scope + 1) body
      `(Exp.lamN "_" Option.none $body')

/-- Elaborate `rec f x := body` with `body` the already-reduced inner expr. -/
partial def elabRec (env : NameEnv) (scope : Nat) (f : TSyntax `pl_arg) (x : TSyntax `pl_arg)
    (body : TSyntax `pl_exp) : TermElabM Term := do
  let (fOpt, fτ) ← unpackArg f
  let (xOpt, xτ) ← unpackArg x
  -- Emit `fix (λf. lam (λx. body))` i.e. `Exp.fixN f (Exp.lamN x body)`
  match fOpt with
  | some fi =>
      checkNotReserved fi
      let fnm := fi.getId
      let fatom := atomOf fnm scope
      let env' := env.insert fnm fatom
      let lamBody ← match xOpt with
        | some xi =>
            checkNotReserved xi
            let xnm := xi.getId
            let xatom := atomOf xnm (scope + 1)
            let env'' := env'.insert xnm xatom
            let b ← elabPL env'' (scope + 2) body
            closeMaybe b xatom (some xnm.toString) xτ
        | none =>
            let b ← elabPL env' (scope + 1) body
            `(Exp.lamN "_" Option.none $b)
      closeMaybeFix lamBody fatom (some fnm.toString) fτ
  | none =>
      -- Anonymous self: `fun x, body` via a no-close fix over lam
      let lamBody ← match xOpt with
        | some xi =>
            checkNotReserved xi
            let xnm := xi.getId
            let xatom := atomOf xnm scope
            let env' := env.insert xnm xatom
            let b ← elabPL env' (scope + 1) body
            closeMaybe b xatom (some xnm.toString) xτ
        | none =>
            let b ← elabPL env (scope + 1) body
            `(Exp.lamN "_" Option.none $b)
      -- Technically `fun x, body` is just lam — no fix at all.
      pure lamBody

/-- Collect the identifiers a pattern binds (in left-to-right order). -/
partial def gatherPatIdents :
    TSyntax `pl_pat → TermElabM (Array Lean.Ident × Array Lean.Ident)
  | p => do
    let mut acc : Array Lean.Ident := #[]
    let rec go (p : TSyntax `pl_pat) (acc : Array Lean.Ident) : TermElabM (Array Lean.Ident) := do
      match p with
      | `(pl_pat|_) => pure acc
      | `(pl_pat|$i:ident) => do checkNotReserved i; pure (acc.push i)
      | `(pl_pat|# $_) => pure acc
      | `(pl_pat|($p)) => go p acc
      | `(pl_pat|($p : $_)) => go p acc
      | `(pl_pat|($p1, $p2)) => do go p2 (← go p1 acc)
      | `(pl_pat|inl($p)) => go p acc
      | `(pl_pat|inr($p)) => go p acc
      | _ => pure acc
    acc ← go p acc
    return (acc, acc)

/-- Wrap `body` in projection `let`s that destructure `bindings` according to `pat`.

Two-pass: first extend the env with every identifier the pattern will bind
(allocating fresh atoms), then produce nested `let`s that project each atom
from the bindings expression. This way the body sees **all** pattern-bound
variables, not just the innermost one. -/
partial def projectPattern (env : NameEnv) (scope : Nat)
    (pat : TSyntax `pl_pat) (bindings : TSyntax `pl_exp)
    (body : TSyntax `pl_exp) (_ : Array Lean.Ident) (_ : Array Lean.Ident)
    : TermElabM Term := do
  -- Pass 1: walk the pattern, collect (atom, ident) pairs in bind order,
  -- and build the full env upfront.
  let rec collect (env : NameEnv) (scope : Nat) (pat : TSyntax `pl_pat) :
      TermElabM (NameEnv × Array (Lean.Ident × Nat)) := do
    match pat with
    | `(pl_pat|$i:ident) => do
        checkNotReserved i
        let nm := i.getId
        let atom := atomOf nm scope
        return (env.insert nm atom, #[(i, atom)])
    | `(pl_pat|_) | `(pl_pat|# $_) => return (env, #[])
    | `(pl_pat|($p)) | `(pl_pat|($p : $_)) => collect env scope p
    | `(pl_pat|($p1, $p2)) => do
        let (env1, a1) ← collect env scope p1
        let (env2, a2) ← collect env1 (scope + a1.size) p2
        return (env2, a1 ++ a2)
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => collect env scope p
    | _ => return (env, #[])
  let (envFull, atoms) ← collect env scope pat
  let scopeAfter := scope + atoms.size
  -- Pass 2: elaborate body in the full env.
  let bodyTerm ← elabPL envFull scopeAfter body
  -- Pass 3: for each pattern-bound ident, wrap bodyTerm in a `let`/`app-lam`
  -- that projects the right sub-expression out of `bindings`. We walk the
  -- pattern again tracking the accumulated projector expression.
  let rec emit (pat : TSyntax `pl_pat) (bindings : TSyntax `pl_exp)
      (inner : Term) : TermElabM Term := do
    match pat with
    | `(pl_pat|$i:ident) => do
        let nm := i.getId
        let atom := atomOf nm scope  -- same atom as in `collect`
        -- Need atom that matches — redo hash.
        let atom := (hash nm).toNat ^^^ (scope + (atomIndexOf atoms nm).getD 0)
        let _ := atom
        -- Simpler: look it up in atoms.
        let some a := atoms.findSome? (fun (j, n) => if j.getId = nm then some n else none)
          | throwError "projectPattern: internal: atom not found for {nm}"
        let closed ← closeMaybe inner a (some nm.toString) none
        `(Exp.app $closed $(← elabPL env scope bindings))
    | `(pl_pat|_) | `(pl_pat|# $_) => return inner
    | `(pl_pat|($p)) | `(pl_pat|($p : $_)) => emit p bindings inner
    | `(pl_pat|($p1, $p2)) => do
        let inner2 ← emit p2 (← `(pl_exp|snd($bindings))) inner
        emit p1 (← `(pl_exp|fst($bindings))) inner2
    | `(pl_pat|inl($p)) | `(pl_pat|inr($p)) => emit p bindings inner
    | _ => return inner
  emit pat bindings bodyTerm
where
  atomIndexOf (atoms : Array (Lean.Ident × Nat)) (nm : Lean.Name) : Option Nat :=
    atoms.findIdx? (fun (j, _) => j.getId = nm)

/-- Build a chain of `case` arms, each trying a pattern and falling through. -/
partial def buildCaseChain (env : NameEnv) (scope : Nat)
    (pats : Array (TSyntax `pl_pat)) (bodies : Array (TSyntax `pl_exp)) : TermElabM Term := do
  let scrutVar ← `(pl_exp|{Exp.fvar $(Syntax.mkNatLit (atomOf (Name.mkSimple "__scrut") scope))})
  buildCaseChainWith env scope scrutVar pats bodies

partial def buildCaseChainWith (env : NameEnv) (scope : Nat)
    (scrutVar : TSyntax `pl_exp)
    (pats : Array (TSyntax `pl_pat)) (bodies : Array (TSyntax `pl_exp)) : TermElabM Term := do
  let mut result : Term ← `(Exp.fail)
  for i in List.range pats.size |>.reverse do
    let pat := pats[i]!
    let body := bodies[i]!
    -- projected body: destructure __bind
    let bindName := Lean.Name.mkSimple "__bind"
    let bindAtom := atomOf bindName (scope + i)
    let envBind := env.insert bindName bindAtom
    let bindVar ← `(pl_exp|{Exp.fvar $(Syntax.mkNatLit bindAtom)})
    let projected ← projectPattern envBind (scope + i + 1) pat bindVar body #[] #[]
    let projectedPL : TSyntax `pl_exp ← `(pl_exp|{$projected})
    -- Re-elaborate the projected body; it already references __bind via fvar.
    let projectedTerm ← elabPL envBind (scope + i + 1) projectedPL
    let bodyClose ← closeMaybe projectedTerm bindAtom (some "__bind") none
    let fallback ← `(Exp.lamN "_" Option.none $result)
    result ← `(Exp.case
                (Exp.scrut $(← elabPL env scope scrutVar) pl_pat($pat))
                $bodyClose
                $fallback)
  return result

end

/-! ## Delaborator support: reverse name registry for free variables

At elaboration time, a Lean identifier `x` becomes `Exp.fvar (hash x).toNat`.
To pretty-print back, we keep an `IO.Ref` mapping atom → display name,
populated each time a `pl(…)` surface term introduces a free identifier.

The registry is lossy on rare collisions (two identifiers hashing to the
same `Nat`); in that case the delaborator prefers the most recently
registered name. -/

initialize fvarNameRegistry : IO.Ref (Std.HashMap Nat String) ← IO.mkRef ∅

/-- Walk a raw `Syntax` tree, registering every identifier seen so that the
    `Exp.fvar` delaborator can recover display names. Over-registers bound
    identifiers too, which is harmless (they'd map to the same display name
    anyway since atoms come from the same hash). -/
partial def registerSyntaxIdents (stx : Syntax) : TermElabM Unit := do
  if stx.isIdent then
    let n := stx.getId
    unless n.isAnonymous do
      let atom := (hash n).toNat
      fvarNameRegistry.modify (·.insert atom n.toString)
  else
    for c in stx.getArgs do
      registerSyntaxIdents c

elab_rules : term
  | `(pl($e)) => do
      -- Register any identifiers so the delaborator can recover names.
      registerSyntaxIdents e.raw
      let t ← elabPL {} 0 e
      Lean.Elab.Term.elabTerm t none

end ProbLang

/-! ## Unexpanders (pretty-printing) -/

namespace ProbLang

open Lean Lean.PrettyPrinter

/-- Strip the `pl(...)` wrapper to get a raw `pl_exp`, or fall back to `{t}` escape. -/
partial def unpackPLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_exp)
  | `(pl($e)) => `(pl_exp|$e)
  | `($t)     => `(pl_exp|{$t})

/-- Strip the `pl_ty(...)` wrapper to get a raw `pl_ty`. -/
partial def unpackPLTy [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_ty)
  | `(pl_ty($τ)) => pure τ
  | `($_)        => panic! "unknown type"

/-- Strip the `pl_pat(...)` wrapper to get a raw `pl_pat`. -/
partial def unpackPLPat [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `pl_pat)
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

/-! ### Patterns -/

@[app_unexpander Pat.wildcard]
def unexpPatWildcard : Unexpander
  | `($_) => `(pl_pat(_))

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

/-! ### Literals / atomic expressions -/

@[app_unexpander Exp.lit]
def unexpLit : Unexpander
  | `($_ $arg) => `(pl(# $arg))
  | _ => throw ()

@[app_unexpander BaseLit.int]
def unexpBLInt : Unexpander
  | `($_ (Int.ofNat $n:num)) => `($n)
  | `($_ $z)                 => pure z
  | _                        => throw ()

@[app_unexpander BaseLit.bool]
def unexpBLBool : Unexpander
  | `($_ $b) => pure b
  | _ => throw ()

@[app_unexpander BaseLit.unit]
def unexpBLUnit : Unexpander := fun _ => `(())

@[app_unexpander Exp.fail]
def unexpFail : Unexpander
  | `($_) => do `(pl(fail))

/-! ### Operators -/

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

/-! ### Pairs / sums / projections -/

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

/-! ### State / random / scrut -/

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

@[app_unexpander Exp.scrut]
def unexpScrut : Unexpander
  | `($_ $e $p) => do `(pl(scrut $(← unpackPLExp e) with $(← unpackPLPat p)))
  | _ => throw ()

/-! ### Binders: `lamN` and `fixN` with name hints -/

/-- Construct a `pl_arg` from a name-hint and an optional type. -/
private def buildArg (name : String) (τ? : Option Term) : UnexpandM (TSyntax `pl_arg) := do
  let ident := Lean.mkIdent (Name.mkSimple name)
  match τ? with
  | some τStx =>
      let τSyn ← unpackPLTy τStx
      `(pl_arg|($ident:ident : $τSyn))
  | none =>
      if name = "_" then
        `(pl_arg|_)
      else
        `(pl_arg|$ident:ident)

/-- Extract `some τ` / `none` payload from the `Option Ty` position of `lamN`/`fixN`. -/
private def extractTyOpt (stx : Term) : UnexpandM (Option Term) := do
  match stx with
  | `((some $τ)) => return some τ
  | `(some $τ)   => return some τ
  | _            => return none

/-- Strip a leading `Exp.close ... <atom>` wrapper from a delaborated body.
    When `lamN`/`fixN` was emitted, the body was closed over an atom; for
    pretty-printing we want the pre-close body so the atom reads back as the
    original free variable name. Also register the atom's display name so the
    `Exp.fvar` delab knows how to render it. -/
private def stripCloseAndRegister (e : Term) (name : String) : UnexpandM Term := do
  match e with
  | `($body |>.close $atomLit) =>
      if let some n := atomLit.raw.isNatLit? then
        -- Fire-and-forget: we can't do IO in UnexpandM cleanly, so registration
        -- happens at elaboration time instead. Just return the body here.
        let _ := n
        return body
      else
        return body
  | `(Exp.close $body $_) => return body
  | _ => return e

@[app_unexpander Exp.lamN]
def unexpLamN : Unexpander
  | `($_ $name:str $τ? $e) => do
      let n := name.getString
      let τOpt ← extractTyOpt τ?
      let arg ← buildArg n τOpt
      let stripped ← stripCloseAndRegister e n
      let body ← unpackPLExp stripped
      unexpFun (← `(pl(fun $arg, $body)))
  | _ => throw ()

@[app_unexpander Exp.fixN]
def unexpFixN : Unexpander
  | `($_ $name:str $τ? $e) => do
      let n := name.getString
      let τOpt ← extractTyOpt τ?
      let arg ← buildArg n τOpt
      let stripped ← stripCloseAndRegister e n
      let body ← unpackPLExp stripped
      unexpFun (← `(pl(rec $arg _ := $body)))
  | _ => throw ()

/-! ### Applications — special-cased for `let` and `;` -/

/-- Check if a `pl_arg` represents a named binder (non-anonymous). -/
private def isNamedArg (bi : TSyntax `pl_arg) : Bool :=
  if bi.raw.getNumArgs > 1 then true        -- typed binder
  else
    let c := bi.raw[0]!
    if c.getNumArgs > 0 then c[0]!.isIdent
    else false

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    match e1 with
    | `(pl(fun $xs*, $body)) =>
        if xs.size = 1 then
          let bi := xs[0]!
          if isNamedArg bi then
            return (← `(pl(let $bi := $(← unpackPLExp e2); $body)))
          else
            return (← `(pl($(← unpackPLExp e2); $body)))
        `(pl($(← unpackPLExp e1) $(← unpackPLExp e2)))
    | _ =>
        `(pl($(← unpackPLExp e1) $(← unpackPLExp e2)))
  | _ => throw ()

/-! ### `Exp.annotated` delab (gated by `pp.problang.annot`) -/

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.annotated]
def delabExpAnnotated : Delab := do
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

The `fvar` atom is a hash of the original Lean identifier, registered in
`fvarNameRegistry` during elaboration. Look up the atom to recover the
display name. -/

open Lean.PrettyPrinter.Delaborator in
@[delab app.ProbLang.Exp.fvar]
def delabExpFvar : Delab := do
  let e ← SubExpr.getExpr
  unless e.getAppNumArgs == 1 do failure
  let argExpr := e.appArg!
  let some n := argExpr.nat? | failure
  let regMap ← fvarNameRegistry.get
  match regMap.get? n with
  | some name =>
      let ident := Lean.mkIdent (Name.mkSimple name)
      `(pl($ident:ident))
  | none =>
      -- Fall back to showing the raw atom.
      `(pl({Exp.fvar $(Syntax.mkNatLit n)}))

end ProbLang
