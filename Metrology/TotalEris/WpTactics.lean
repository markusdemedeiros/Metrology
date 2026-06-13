module

public import Metrology.TotalEris.TotalLifting
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-!
# Elaborator-based `twp_*` tactics for `tglWp`

Port of iris-lean's `HeapLang/Tactic.lean` + `HeapLang/ProofMode.lean`,
specialised to ProbLang's `tglWp`. Unlike the previous macro layer (which
expanded to a single `iapply` and required the user to supply the evaluation
context `K` by hand), these are real `elab` tactics that:

* destructure the `tglWp E e Φ` goal once into a typed `TglWpGoal` (`runTacticTglWp`);
* mechanically decompose `e` into a list of `EctxItem`s and search for a redex
  matching a focus pattern (`extractEctxItem` / `findECtx`), so `twp_bind`/`twp_pure`
  never need an explicit `K`.

ProbLang has no language hierarchy, so we match the concrete `tglWp` head directly
rather than going through iris's `Wp`/`IrisGS_gen` abstractions.
-/

namespace ProbLang.TotalEris

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode

/-! ## Evaluation-context engine (mirrors `HeapLang/Tactic.lean`)

`extractEctxItem e` peels the outermost evaluation-context frame off `e`,
returning the frame and the sub-expression in its hole (mirrors
`Exp.decompItem`). `findECtx` searches the resulting frame stack for a
sub-expression satisfying a predicate. -/

/-- Peel one evaluation-context frame off `e`. Returns `(some Ki, e')` with
`Ki.fillItem e' = e` when `e` has a redex position, else `(none, e)`. -/
meta partial def extractEctxItem {α : Q(Type)} :
    Q(Exp $α) → MetaM (Option Q(EctxItem $α) × Q(Exp $α))
  | ~q(.app $e (.ofVal $v₂))   => return (some q(.appL $v₂), e)
  | ~q(.app $e₁ $e)            => return (some q(.appR $e₁), e)
  | ~q(.unop $op $e)           => return (some q(.unop $op), e)
  | ~q(.binop $op $e (.ofVal $v₂)) => return (some q(.binopL $op $v₂), e)
  | ~q(.binop $op $e₁ $e)      => return (some q(.binopR $op $e₁), e)
  | ~q(.cond $e $e₁ $e₂)       => return (some q(.condC $e₁ $e₂), e)
  | ~q(.pair $e (.ofVal $v₂))  => return (some q(.pairL $v₂), e)
  | ~q(.pair $e₁ $e)           => return (some q(.pairR $e₁), e)
  | ~q(.fst $e)                => return (some q(.fst), e)
  | ~q(.snd $e)                => return (some q(.snd), e)
  | ~q(.inl $e)                => return (some q(.inl), e)
  | ~q(.inr $e)                => return (some q(.inr), e)
  | ~q(.case $e $e₁ $e₂)       => return (some q(.case $e₁ $e₂), e)
  | ~q(.alloc $e)              => return (some q(.alloc), e)
  | ~q(.load $e)               => return (some q(.load), e)
  | ~q(.store $e (.ofVal $v₂)) => return (some q(.storeL $v₂), e)
  | ~q(.store $e₁ $e)          => return (some q(.storeR $e₁), e)
  | ~q(.tape $e)               => return (some q(.tape), e)
  | ~q(.rand $e (.ofVal $v₂))  => return (some q(.randL $v₂), e)
  | ~q(.rand $e₁ $e)           => return (some q(.randR $e₁), e)
  | ~q(.scrut $e $p)           => return (some q(.scrut $p), e)
  | e => return (none, e)

/-- Fully decompose `e` into a frame stack `[innermost, …, outermost]` and the
innermost non-context sub-expression. The list order matches `Ectx.fill`
(`foldl (flip fillItem)`), so `Ectx.fill result.1 result.2 = e`. -/
meta partial def extractAllEctxItems {α : Q(Type)} (e : Q(Exp $α))
    (acc : List Q(EctxItem $α) := []) : MetaM (List Q(EctxItem $α) × Q(Exp $α)) := do
  match ← extractEctxItem e with
  | (some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (none, e) => return (acc, e)

/-- Plug `e` into a single frame `Ki` (mirrors `EctxItem.fillItem`). -/
meta def fillItem {α : Q(Type)} (e : Q(Exp $α)) : Q(EctxItem $α) → MetaM Q(Exp $α)
  | ~q(.appL $v₂)     => return q(.app $e (.ofVal $v₂))
  | ~q(.appR $e₁)     => return q(.app $e₁ $e)
  | ~q(.unop $op)     => return q(.unop $op $e)
  | ~q(.binopL $op $v₂) => return q(.binop $op $e (.ofVal $v₂))
  | ~q(.binopR $op $e₁) => return q(.binop $op $e₁ $e)
  | ~q(.condC $e₁ $e₂) => return q(.cond $e $e₁ $e₂)
  | ~q(.pairL $v₂)    => return q(.pair $e (.ofVal $v₂))
  | ~q(.pairR $e₁)    => return q(.pair $e₁ $e)
  | ~q(.fst)          => return q(.fst $e)
  | ~q(.snd)          => return q(.snd $e)
  | ~q(.inl)          => return q(.inl $e)
  | ~q(.inr)          => return q(.inr $e)
  | ~q(.case $e₁ $e₂) => return q(.case $e $e₁ $e₂)
  | ~q(.alloc)        => return q(.alloc $e)
  | ~q(.load)         => return q(.load $e)
  | ~q(.storeL $v₂)   => return q(.store $e (.ofVal $v₂))
  | ~q(.storeR $e₁)   => return q(.store $e₁ $e)
  | ~q(.tape)         => return q(.tape $e)
  | ~q(.randL $v₂)    => return q(.rand $e (.ofVal $v₂))
  | ~q(.randR $e₁)    => return q(.rand $e₁ $e)
  | ~q(.scrut $p)     => return q(.scrut $e $p)

/-- Quote a `List` of quoted `EctxItem`s as a quoted `Ectx`. -/
meta def quoteList {α : Q(Type)} : List Q(EctxItem $α) → Q(Ectx $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

/-- A decomposition `e = Ectx.fill K e'` together with a result `a` computed at
the focus `e'`. -/
meta structure ECtxResultOf (α : Q(Type)) (β : Type) where
  result : β
  K : Q(Ectx $α)
  e' : Q(Exp $α)

/-- Walk the frame stack of `ogE` from innermost outward, returning the first
focus `e'` at which `pred e'` succeeds, together with the surrounding context. -/
meta partial def findECtx {α : Q(Type)} {β : Type} (ogE : Q(Exp $α))
    (pred : Q(Exp $α) → MetaM β) : MetaM (Option (ECtxResultOf α β)) := do
  let (Kis, inner) ← extractAllEctxItems ogE
  go inner Kis
where
  go (e : Q(Exp $α)) (Kis : List Q(EctxItem $α)) :
      MetaM (Option (ECtxResultOf α β)) := do
    if let some a ← observing? <| pred e then
      return some { result := a, K := quoteList Kis, e' := e }
    let Ki :: Kis' := Kis | return none
    go (← fillItem e Ki) Kis'

/-! ## WP-goal runner (mirrors `runTacticWp`)

Destructures an iris proof-mode goal `ehyps ⊢ tglWp E e Φ` into its typed
components. ProbLang has no language hierarchy, so we match the concrete
`ErisWpGS.tglWp` head directly. -/

/-- A proof-mode goal whose conclusion is `tglWp E e Φ`. -/
meta structure TglWpGoal where
  {u : Level}
  {α : Q(Type)}
  instPL : Q(ProbLang.ProbLangℝ $α)
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  instWp : Q(ErisWpGS (rT := $α) $GF)
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  E : Q(CoPset)
  e : Q(Exp $α)
  Φ : Q(Val $α → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

/-- Run `k` against the current goal, requiring it to be `ehyps ⊢ tglWp E e Φ`. -/
meta def runTacticTglWp {β : Type} (k : MVarId → TglWpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    -- Binding `$GF` here refines `prop` to `IProp GF`, so `hyps`' carrier is concrete
    -- for `addBIGoal` downstream.
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    -- Extract the `tglWp` arguments structurally (`tglWp` is `@[reducible]`, so a
    -- typed `~q` match against `$prop` does not refine; read the application spine).
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ProbLang.TotalEris.ErisWpGS.tglWp do
      throwError "the goal {goal} must be a `tglWp`"
    let args := goalE.getAppArgs
    unless args.size == 7 do
      throwError "unexpected `tglWp` arity ({args.size}) in goal {goal}"
    have α : Q(Type) := args[0]!
    have instPL : Q(ProbLang.ProbLangℝ $α) := args[1]!
    have instWp : Q(ErisWpGS (rT := $α) $GF) := args[3]!
    have E : Q(CoPset) := args[4]!
    have e : Q(Exp $α) := args[5]!
    have Φ : Q(Val $α → IProp $GF) := args[6]!
    k mvar { instPL, instWp, hyps, E, e, Φ, hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩ }

/-! ## `twp_bind` — focus on a subexpression by auto-discovering its context -/

/-- `twp_bind e` rebases the goal `tglWp E (K.fill e) Φ` to `tglWp E e (…)`, with
the evaluation context `K` discovered automatically (no manual `K`). -/
elab "twp_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `twp_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    have e' : Q(Exp $α) := res.e'
    -- Φ' v := tglWp E (K.fill (ofVal v)) Φ
    let Φc : Q(Val $α → IProp $GF) ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        mkLambdaFVars #[v]
          q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E
              (Ectx.fill $K (Exp.ofVal $v)) $Φ)
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $e' $Φc)
    -- Build the proof with raw `mkApp*` rather than `q(…)`: `tglWp` is
    -- `@[reducible, expose]`, so quoting `tglWp_bind`'s statement makes Qq `whnf` it
    -- into `bi_least_fixpoint` at elaboration time (heartbeat blow-up). `mkAppOptM`
    -- type-checks lazily and avoids that.
    let bindPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_bind
      (#[α, instPL, GF, instWp, K, E, e', Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

end ProbLang.TotalEris
