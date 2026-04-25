import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.Compatibility
import Metrology.Approxis.AppRelRules
import Metrology.Approxis.RelTactics
import Metrology.Approxis.Interp

/-!
# Fundamental Theorem

Fundamental theorem of the logical relation: well-typed terms are related to themselves.

```
Theorem fundamental (Δ : TyEnv) (Γ : RelCtx) (e : Exp) (τ : Ty) :
  Γ ⊢ₜ e : τ → ⊢ E; Δ; Γ ⊨ e ≤log≤ e : τ
```

## Rocq source
`clutch/theories/approxis/fundamental.v` (33 `bin_log_related_*` lemmas + the
fundamental theorem + `bin_log_related_under_typed_ctx` / `refines_typed`).

## Port status (2026-04-25)

**Statement-only stubs.** Every `bin_log_related_*` declaration is in place
with a `sorry` body. The plumbing (`Tctx → RelCtx` lift, substMap-distributivity
lemmas, free-variable bookkeeping) is what each proof needs and is mostly
unimplemented. The `refines_*` building blocks all exist in `Compatibility.lean`,
`AppRelRules.lean`, and the new `refines_rand_*_int` in this session — so each
stub here is an exercise in typing-context bookkeeping plus a final `iapply`
to the corresponding `refines_*` lemma.

## What's blocking each proof

- **`substMap` congruences** — `Exp.substMap_pair`, `_app`, `_lam`, `_alloc`,
  `_load`, `_store`, `_rand`, etc. None are currently in `Metatheory.lean`.
  Each is a one-line induction on the substitution list.
- **`Tctx → RelCtx` lift** — `Typed`'s `Tctx := Var → Option Ty` doesn't directly
  feed `bin_log_related`'s `RelCtx := List (Var × lrel GF)`. Need a lift
  `Tctx.toRelCtx (Δ : TyEnv GF) : Tctx → RelCtx GF`.
- **`env_ltyped2_lookup` for free-variable case** — already exists in `Interp.lean`.
- **Recursive cases** (`rec`, `tlam`, `unpack`) — additionally need Löb induction
  and binder-shifting reasoning.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

open Cslib Exp

section Fundamental
variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS hlc GF]

/-! ## Tctx → RelCtx lifting

The fundamental theorem operates on `Typed`'s `Tctx` (function-encoded), but
`bin_log_related` consumes `RelCtx` (list-of-pairs). We bridge by keeping the
typing premise on `Tctx` and the relational interpretation on `RelCtx`,
related pointwise via `interp τ Δ` for each binding.

Since `Tctx := Var → Option Ty` has no enumerable list of bindings, we instead
operate on `RelCtx GF` directly throughout, requiring callers to provide the
lifted form. The connection to `Typed`'s `Tctx` happens at the top-level
`fundamental` theorem via a `TctxRelated` helper. -/

/-- `TctxRelated Δ Γtc Γrc` asserts that the relational context `Γrc` is the
pointwise lift of the syntactic context `Γtc` through `interp · Δ`. -/
def TctxRelated (Δ : TyEnv GF) (Γtc : Tctx) (Γrc : RelCtx GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp τ Δ) = Γrc.lookup x

/-! ## Compatibility lemmas (statement stubs)

Each lemma mirrors `bin_log_related_*` from `fundamental.v`. All bodies are
`sorry` pending the `substMap` infrastructure (see file header). -/

theorem bin_log_related_var (Δ : TyEnv GF) (Γ : RelCtx GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp τ Δ)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  -- Use env_ltyped2_lookup to extract the lookup pair + A-relation.
  ihave HEx := env_ltyped2_lookup Γ vs x (interp τ Δ) hΓ $$ Hvs
  icases HEx with ⟨%v1, %v2, %hvs_eq, HA⟩
  ihave %Hclosed := env_ltyped2_allClosed Γ vs $$ Hvs
  have hfst_lookup : SubstMap.lookup vs.fst x = some v1.1 := by
    rw [ValSubstMap.fst_lookup, hvs_eq]; rfl
  have hsnd_lookup : SubstMap.lookup vs.snd x = some v2.1 := by
    rw [ValSubstMap.snd_lookup, hvs_eq]; rfl
  have hfst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hclosed (z, w1, w2) hmem).1
  have hsnd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hclosed (z, w1, w2) hmem).2
  rw [Exp.substMap_fvar_lookup_some _ _ hfst_closed hfst_lookup,
      Exp.substMap_fvar_lookup_some _ _ hsnd_closed hsnd_lookup]
  iapply (refines_ret (v1 := v1) (v2 := v2) (hv1 := rfl) (hv2 := rfl))
  imodintro
  iexact HA

theorem bin_log_related_pair (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e2 e1' e2' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ1) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ2 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.pair e1 e2) (.pair e1' e2')
          (.prod τ1 τ2)) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  -- Push substMap through .pair on both sides.
  rw [Exp.substMap_pair, Exp.substMap_pair]
  -- interp .prod = lrel_prod (interp τ1) (interp τ2) by def.
  have hprod : (interp (Ty.prod τ1 τ2) Δ : lrel GF) =
      lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl
  rw [hprod]
  -- refines_pair takes Ectx.fill [pairR e1] e2 form, def-eq to .pair e1 e2.
  have hbridge1 : Exp.pair (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
      Ectx.fill [EctxItem.pairR (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) := rfl
  have hbridge2 : Exp.pair (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
      Ectx.fill [EctxItem.pairR (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') := rfl
  rw [hbridge1, hbridge2]
  iapply (refines_pair (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH1']
  · iexact IH1'
  iexact IH2'

theorem bin_log_related_fst (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.fst e) (.fst e') τ1 := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_fst, Exp.substMap_fst]
  have hprod : (interp (Ty.prod τ1 τ2) Δ : lrel GF) =
      lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_prod (interp τ1 Δ) (interp τ2 Δ))) $$ [IH']
  · rw [← hprod]; iexact IH'
  iapply (refines_fst (A := interp τ1 Δ) (B := interp τ2 Δ))
  iexact IH''

theorem bin_log_related_snd (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.snd e) (.snd e') τ2 := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_snd, Exp.substMap_snd]
  have hprod : (interp (Ty.prod τ1 τ2) Δ : lrel GF) =
      lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_prod (interp τ1 Δ) (interp τ2 Δ))) $$ [IH']
  · rw [← hprod]; iexact IH'
  iapply (refines_snd (A := interp τ1 Δ) (B := interp τ2 Δ))
  iexact IH''

theorem bin_log_related_injl (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ1) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_inl, Exp.substMap_inl]
  have hsum : (interp (Ty.sum τ1 τ2) Δ : lrel GF) =
      lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
  rw [hsum]
  iapply (refines_injl (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_injr (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ2) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inr e) (.inr e') (.sum τ1 τ2) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_inr, Exp.substMap_inr]
  have hsum : (interp (Ty.sum τ1 τ2) Δ : lrel GF) =
      lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
  rw [hsum]
  iapply (refines_injr (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_case (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e0 e1 e2 e0' e1' e2' : Exp} {τ1 τ2 τ3 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e0 e0' (.sum τ1 τ2)) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.arrow τ1 τ3) -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' (.arrow τ2 τ3) -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.case e0 e1 e2) (.case e0' e1' e2') τ3) := by
  iintro IH0 IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH0' := IH0 $$ %vs Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_case, Exp.substMap_case]
  have hsum : (interp (Ty.sum τ1 τ2) Δ : lrel GF) =
      lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
  have harr1 : (interp (Ty.arrow τ1 τ3) Δ : lrel GF) =
      lrel_arr (interp τ1 Δ) (interp τ3 Δ) := rfl
  have harr2 : (interp (Ty.arrow τ2 τ3) Δ : lrel GF) =
      lrel_arr (interp τ2 Δ) (interp τ3 Δ) := rfl
  ihave IH0'' : iprop(refines ⊤ (Exp.substMap vs.fst e0) (Exp.substMap vs.snd e0')
      (lrel_sum (interp τ1 Δ) (interp τ2 Δ))) $$ [IH0']
  · rw [← hsum]; iexact IH0'
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_arr (interp τ1 Δ) (interp τ3 Δ))) $$ [IH1']
  · rw [← harr1]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      (lrel_arr (interp τ2 Δ) (interp τ3 Δ))) $$ [IH2']
  · rw [← harr2]; iexact IH2'
  ihave HRcaseApp := refines_case (A := interp τ1 Δ) (B := interp τ2 Δ) (C := interp τ3 Δ)
    (e0 := Exp.substMap vs.fst e0) (e0' := Exp.substMap vs.snd e0')
    (e1 := Exp.substMap vs.fst e1) (e1' := Exp.substMap vs.snd e1')
    (e2 := Exp.substMap vs.fst e2) (e2' := Exp.substMap vs.snd e2') $$ [IH0'']
  · iexact IH0''
  ihave HRcaseApp1 := HRcaseApp $$ [IH1'']
  · iexact IH1''
  iapply HRcaseApp1
  iexact IH2''

theorem bin_log_related_if (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e0 e1 e2 e0' e1' e2' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e0 e0' .bool) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.cond e0 e1 e2) (.cond e0' e1' e2') τ) := by
  iintro IH0 IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH0' := IH0 $$ %vs Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_cond, Exp.substMap_cond]
  have hbool : (interp Ty.bool Δ : lrel GF) = lrel_bool := rfl
  ihave IH0'' : iprop(refines ⊤ (Exp.substMap vs.fst e0) (Exp.substMap vs.snd e0')
      lrel_bool) $$ [IH0']
  · rw [← hbool]; iexact IH0'
  -- Refines_if takes 3 args: IH0 (entailment LHS) + 2 wand args (IH1, IH2).
  -- Pre-apply IH1, IH2 into IH0''-applied form to avoid bullet-scoping issues.
  ihave HRifApplied := refines_if (A := interp τ Δ) (e0 := Exp.substMap vs.fst e0)
    (e0' := Exp.substMap vs.snd e0') (e1 := Exp.substMap vs.fst e1)
    (e1' := Exp.substMap vs.snd e1') (e2 := Exp.substMap vs.fst e2)
    (e2' := Exp.substMap vs.snd e2') $$ [IH0'']
  · iexact IH0''
  ihave HRif1 := HRifApplied $$ [IH1']
  · iexact IH1'
  iapply HRif1
  iexact IH2'

theorem bin_log_related_app (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e2 e1' e2' : Exp} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.arrow τ1 τ2)) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ1 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.app e1 e2) (.app e1' e2') τ2) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_app, Exp.substMap_app]
  have hb1 : Exp.app (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
      Ectx.fill [EctxItem.appR (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) := rfl
  have hb2 : Exp.app (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
      Ectx.fill [EctxItem.appR (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') := rfl
  rw [hb1, hb2]
  -- Rebrand IH1' from `(interp .arrow ...) v v'` to `(lrel_arr ...) v v'` via def-eq.
  have harr : (interp (Ty.arrow τ1 τ2) Δ : lrel GF) =
      lrel_arr (interp τ1 Δ) (interp τ2 Δ) := rfl
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_arr (interp τ1 Δ) (interp τ2 Δ))) $$ [IH1']
  · rw [← harr]; iexact IH1'
  iapply (refines_app (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH1'']
  · iexact IH1''
  iexact IH2'

theorem bin_log_related_lam (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} (L : Finset Var)
    (Hbody : ∀ x ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ ((x, interp τ1 Δ) :: Γ)
        (Exp.open' e (.fvar x)) (Exp.open' e' (.fvar x)) τ2) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.lam e) (.lam e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  rw [Exp.substMap_lam, Exp.substMap_lam]
  have harr : (interp (Ty.arrow τ1 τ2) Δ : lrel GF) =
      lrel_arr (interp τ1 Δ) (interp τ2 Δ) := rfl
  rw [harr]
  -- Use refines_arrow_val: the .lam value pair is in lrel_arr if applying it
  -- to A-related values yields B-related results.
  iapply (refines_arrow_val
    (v := ⟨Exp.lam (Exp.substMap vs.fst e), IsVal.lam⟩)
    (v' := ⟨Exp.lam (Exp.substMap vs.snd e'), IsVal.lam⟩))
  iintro !> %v1 %v2 #HA
  -- Goal: refines ⊤ (.app (.lam (substMap vs.fst e)) v1.1)
  --                (.app (.lam (substMap vs.snd e')) v2.1) (interp τ2 Δ).
  -- The full proof requires picking a fresh atom and reasoning about
  -- substitution-open commutation. Deferred.
  sorry

theorem bin_log_related_fix (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ1 τ2 : Ty} (L : Finset Var)
    (Hbody : ∀ f ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
        ((f, interp (.arrow τ1 τ2) Δ) :: Γ)
        (Exp.open' e (.fvar f)) (Exp.open' e' (.fvar f)) (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.fix e) (.fix e')
      (.arrow τ1 τ2) := by
  sorry

theorem bin_log_related_alloc (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.alloc e) (.alloc e') (.ref τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_alloc, Exp.substMap_alloc]
  have href : (interp (Ty.ref τ) Δ : lrel GF) = lrel_ref (interp τ Δ) := rfl
  rw [href]
  iapply (refines_alloc (A := interp τ Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_load (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e e' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.ref τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.load e) (.load e') τ := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_load, Exp.substMap_load]
  have href : (interp (Ty.ref τ) Δ : lrel GF) = lrel_ref (interp τ Δ) := rfl
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_ref (interp τ Δ))) $$ [IH']
  · rw [← href]; iexact IH'
  iapply (refines_load (A := interp τ Δ)) $$ [IH'']
  iexact IH''

theorem bin_log_related_store (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e2 e1' e2' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.ref τ)) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.store e1 e2) (.store e1' e2') .unit) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_store, Exp.substMap_store]
  have hunit : (interp Ty.unit Δ : lrel GF) = lrel_unit := rfl
  rw [hunit]
  have href : (interp (Ty.ref τ) Δ : lrel GF) = lrel_ref (interp τ Δ) := rfl
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_ref (interp τ Δ))) $$ [IH1']
  · rw [← href]; iexact IH1'
  iapply (refines_store (A := interp τ Δ)) $$ [IH1'']
  · iexact IH1''
  iexact IH2'

theorem bin_log_related_alloctape (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.tape e) (.tape e') .tape := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_tape, Exp.substMap_tape]
  have hint : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
  have htape : (interp Ty.tape Δ : lrel GF) = lrel_tape := rfl
  rw [htape]
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      lrel_int) $$ [IH']
  · rw [← hint]; iexact IH'
  iapply refines_alloctape
  iexact IH''

/-- `bin_log_related_rand_tape`: ports the labeled-rand compatibility from
`fundamental.v:289`, but at `lrel_int` (not `lrel_nat` as in Rocq), to match
Lean's `Typed.rand` signature. Discharges via `refines_rand_tape_int` from
`Compatibility.lean`. -/
theorem bin_log_related_rand_tape (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e1' e2 e2' : Exp} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .tape -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_rand, Exp.substMap_rand]
  have hint : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
  rw [hint]
  have htape : (interp Ty.tape Δ : lrel GF) = lrel_tape := rfl
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_tape) $$ [IH2']
  · rw [← htape]; iexact IH2'
  iapply refines_rand_tape_int $$ [IH1']
  · iexact IH1'
  iexact IH2''

/-- `bin_log_related_rand_unit`: ports unlabeled-rand compatibility, at
`lrel_int`. Discharges via `refines_rand_unit_int`. -/
theorem bin_log_related_rand_unit (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e1' e2 e2' : Exp} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .unit -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_rand, Exp.substMap_rand]
  -- Bind e2/e2' (unit-typed) first to consume IH2', then derive the rand step
  -- from refines_rand_unit_int. Actually we'd want lrel_unit-bound e2/e2'
  -- to reduce to .lit .unit so the rand has the right shape.
  -- Strategy: use refines_bind on e2/e2' under [randR e1] to get value pair
  -- (which by lrel_unit_unfold are both .lit .unit), then rewrite and apply
  -- refines_rand_unit_int on what remains.
  have hb1 : Exp.rand (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
      Ectx.fill [EctxItem.randR (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) := rfl
  have hb2 : Exp.rand (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
      Ectx.fill [EctxItem.randR (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') := rfl
  rw [hb1, hb2]
  have hunit : (interp Ty.unit Δ : lrel GF) = lrel_unit := rfl
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_unit) $$ [IH2']
  · rw [← hunit]; iexact IH2'
  iapply (refines_bind [EctxItem.randR (Exp.substMap vs.fst e1)]
    [EctxItem.randR (Exp.substMap vs.snd e1')] (A := lrel_unit)) $$ [IH2'']
  · iexact IH2''
  iintro %v2 %v2' Hu
  -- Hu : lrel_unit.car v2 v2'. By def-eq, this is the pure conjunction.
  have hunit_unfold : (lrel_unit (GF := GF)).car v2 v2' =
      iprop(⌜v2.1 = .lit .unit ∧ v2'.1 = .lit .unit⌝) := rfl
  ihave %Hu' : (⌜v2.1 = .lit .unit ∧ v2'.1 = .lit .unit⌝ : IProp GF) $$ [Hu]
  · rw [← hunit_unfold]; iexact Hu
  obtain ⟨hv2, hv2'⟩ := Hu'
  rw [hv2, hv2']
  have hint : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
  rw [hint]
  -- After rewriting, goal is `refines ⊤ ([randR e1].fill (.lit .unit)) ([randR e1'].fill (.lit .unit)) lrel_int`.
  -- Bridge to `.rand e1 (.lit .unit)` form expected by refines_rand_unit_int.
  have hbk1 : Ectx.fill [EctxItem.randR (Exp.substMap vs.fst e1)] (Exp.lit .unit) =
      Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.fst e1) := rfl
  have hbk2 : Ectx.fill [EctxItem.randR (Exp.substMap vs.snd e1')] (Exp.lit .unit) =
      Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.snd e1') := rfl
  rw [hbk1, hbk2]
  iapply refines_rand_unit_int
  iexact IH1'

/-! ### Polymorphic / recursive type compatibility -/

theorem bin_log_related_tlam (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} {τ : Ty}
    (Hbody : ∀ A : lrel GF,
      ⊢@{IProp GF} □ (bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ) Γ e e' τ)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.lam e) (.lam e') (.forall' τ) := by
  sorry

theorem bin_log_related_tapp (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} {τ τ' : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.forall' τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ
        (.app e (.lit .unit)) (.app e' (.lit .unit)) (τ.single τ') := by
  sorry

theorem bin_log_related_fold (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (τ.single (.rec' τ))) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.rec' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  -- IH' has type `refines ⊤ ... (interp (τ.single (rec' τ)) Δ)`.
  -- Goal is `refines ⊤ ... (interp (rec' τ) Δ)`.
  -- The two interp values are OFE-equivalent via interp_subst applied at
  -- the recursive position. Use refines_wand to convert.
  -- Actually simpler: refines is OFE-nonexpansive in A, and ≡ → entails-bidirectional.
  -- The Rocq proof applies `value_case` (= refines_ret after binding), then
  -- rewrites by lrel_rec_unfold and interp_subst. Both can be done via
  -- pointwise reasoning.
  -- Without setoid-rewrite machinery in iris-lean, we'd need to bridge
  -- (interp τ.single (rec' τ) Δ).car v v' → (interp (rec' τ) Δ).car v v' manually.
  -- Skipped pending a clean OFE-rewrite pattern.
  sorry

theorem bin_log_related_unfold (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.rec' τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ
        (.app recUnfold e) (.app recUnfold e') (τ.single (.rec' τ)) := by
  sorry

theorem bin_log_related_pack (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp} {τ τ' : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (τ.single τ')) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.exists' τ) := by
  sorry

theorem bin_log_related_unpack (Δ : TyEnv GF) (Γ : RelCtx GF) (L : Finset Var)
    {e1 e1' e2 e2' : Exp} {τ τ2 : Ty}
    (HIH1 : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (Ty.exists' τ))
    (HIH2 : ∀ A : lrel GF, ∀ x ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ) ((x, A) :: Γ)
        (Exp.open' e2 (.fvar x)) (Exp.open' e2' (.fvar x)) τ2) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ
      (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 := by
  sorry

/-! ### Operator / scrut compatibility -/

theorem bin_log_related_int_binop (Δ : TyEnv GF) (Γ : RelCtx GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp} {τ : Ty}
    (Hres : op.intResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .int -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_binop, Exp.substMap_binop]
  have hint : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      lrel_int) $$ [IH1']
  · rw [← hint]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_int) $$ [IH2']
  · rw [← hint]; iexact IH2'
  -- Bind e2/e2' first, then e1/e1', getting both int values n1, n2.
  rw [show Exp.binop op (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
        Ectx.fill [EctxItem.binopR op (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) from rfl,
      show Exp.binop op (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
        Ectx.fill [EctxItem.binopR op (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') from rfl]
  iapply (refines_bind [EctxItem.binopR op (Exp.substMap vs.fst e1)]
    [EctxItem.binopR op (Exp.substMap vs.snd e1')] (A := lrel_int)) $$ [IH2'']
  · iexact IH2''
  iintro %v2 %v2' Hint2
  ihave Hv2Ex := lrel_int_unfold v2 v2' $$ Hint2
  icases Hv2Ex with ⟨%n2, %hv2, %hv2'⟩
  rw [show Ectx.fill [EctxItem.binopR op (Exp.substMap vs.fst e1)] v2.1 =
        Exp.binop op (Exp.substMap vs.fst e1) v2.1 from rfl,
      show Ectx.fill [EctxItem.binopR op (Exp.substMap vs.snd e1')] v2'.1 =
        Exp.binop op (Exp.substMap vs.snd e1') v2'.1 from rfl,
      hv2, hv2']
  rw [show Exp.binop op (Exp.substMap vs.fst e1) (Exp.lit (.int n2)) =
        Ectx.fill [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩] (Exp.substMap vs.fst e1) from rfl,
      show Exp.binop op (Exp.substMap vs.snd e1') (Exp.lit (.int n2)) =
        Ectx.fill [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩] (Exp.substMap vs.snd e1') from rfl]
  iapply (refines_bind [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩]
    [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩] (A := lrel_int)) $$ [IH1'']
  · iexact IH1''
  iintro %v1 %v1' Hint1
  ihave Hv1Ex := lrel_int_unfold v1 v1' $$ Hint1
  icases Hv1Ex with ⟨%n1, %hv1, %hv1'⟩
  rw [show Ectx.fill [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩] v1.1 =
        Exp.binop op v1.1 (Exp.lit (.int n2)) from rfl,
      show Ectx.fill [EctxItem.binopL op ⟨.lit (.int n2), IsVal.lit⟩] v1'.1 =
        Exp.binop op v1'.1 (Exp.lit (.int n2)) from rfl,
      hv1, hv1']
  -- Goal: refines ⊤ (.binop op #n1 #n2) (.binop op #n1 #n2) (interp τ Δ).
  -- Per-op bridge: int-result ops (plus, minus, mult, div, mod) → lrel_int;
  -- bool-result ops (eq, lt, le) → lrel_bool. div/mod additionally need
  -- 0-divisor case-split.
  have hbridge_int : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
  have hbridge_bool : (interp Ty.bool Δ : lrel GF) = lrel_bool := rfl
  cases op
  case plus =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_int]
    iapply (refines_binop_pure .plus _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 + n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case minus =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_int]
    iapply (refines_binop_pure .minus _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 - n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case mult =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_int]
    iapply (refines_binop_pure .mult _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 * n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case div =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_int]
    by_cases hn2 : n2 = 0
    · -- div by zero: BinOp.eval gives none → headStep stuck. Vacuously refines.
      sorry
    · -- div with n2 ≠ 0: just leave as sorry for now (eval-pattern reduction
      -- needs more delicate handling).
      sorry
  case mod =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_int]
    by_cases hn2 : n2 = 0
    · sorry
    · sorry
  case and => simp [BinOp.intResTy] at Hres
  case or  => simp [BinOp.intResTy] at Hres
  case xor => simp [BinOp.intResTy] at Hres
  case eq =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_bool]
    iapply (refines_binop_pure .eq _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide ((BaseLit.int n1) = .int n2))
    ipure_intro
    exact ⟨rfl, rfl⟩
  case lt =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_bool]
    iapply (refines_binop_pure .lt _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide (n1 < n2))
    ipure_intro
    exact ⟨rfl, rfl⟩
  case le =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [hbridge_bool]
    iapply (refines_binop_pure .le _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide (n1 ≤ n2))
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_bool_binop (Δ : TyEnv GF) (Γ : RelCtx GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp} {τ : Ty}
    (Hres : op.boolResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .bool) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .bool -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_binop, Exp.substMap_binop]
  have hbool : (interp Ty.bool Δ : lrel GF) = lrel_bool := rfl
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      lrel_bool) $$ [IH1']
  · rw [← hbool]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_bool) $$ [IH2']
  · rw [← hbool]; iexact IH2'
  -- Bind e2/e2' first, then e1/e1'.
  rw [show Exp.binop op (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
        Ectx.fill [EctxItem.binopR op (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) from rfl,
      show Exp.binop op (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
        Ectx.fill [EctxItem.binopR op (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') from rfl]
  iapply (refines_bind [EctxItem.binopR op (Exp.substMap vs.fst e1)]
    [EctxItem.binopR op (Exp.substMap vs.snd e1')] (A := lrel_bool)) $$ [IH2'']
  · iexact IH2''
  iintro %v2 %v2' Hbool2
  ihave Hv2Ex := lrel_bool_unfold v2 v2' $$ Hbool2
  icases Hv2Ex with ⟨%b2, %hv2, %hv2'⟩
  rw [show Ectx.fill [EctxItem.binopR op (Exp.substMap vs.fst e1)] v2.1 =
        Exp.binop op (Exp.substMap vs.fst e1) v2.1 from rfl,
      show Ectx.fill [EctxItem.binopR op (Exp.substMap vs.snd e1')] v2'.1 =
        Exp.binop op (Exp.substMap vs.snd e1') v2'.1 from rfl,
      hv2, hv2']
  rw [show Exp.binop op (Exp.substMap vs.fst e1) (Exp.lit (.bool b2)) =
        Ectx.fill [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩] (Exp.substMap vs.fst e1) from rfl,
      show Exp.binop op (Exp.substMap vs.snd e1') (Exp.lit (.bool b2)) =
        Ectx.fill [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩] (Exp.substMap vs.snd e1') from rfl]
  iapply (refines_bind [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩]
    [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩] (A := lrel_bool)) $$ [IH1'']
  · iexact IH1''
  iintro %v1 %v1' Hbool1
  ihave Hv1Ex := lrel_bool_unfold v1 v1' $$ Hbool1
  icases Hv1Ex with ⟨%b1, %hv1, %hv1'⟩
  rw [show Ectx.fill [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩] v1.1 =
        Exp.binop op v1.1 (Exp.lit (.bool b2)) from rfl,
      show Ectx.fill [EctxItem.binopL op ⟨.lit (.bool b2), IsVal.lit⟩] v1'.1 =
        Exp.binop op v1'.1 (Exp.lit (.bool b2)) from rfl,
      hv1, hv1']
  -- Bool-binops: and, or, xor, eq → all return bool. plus/minus/etc → none.
  cases op
  case plus  => simp [BinOp.boolResTy] at Hres
  case minus => simp [BinOp.boolResTy] at Hres
  case mult  => simp [BinOp.boolResTy] at Hres
  case div   => simp [BinOp.boolResTy] at Hres
  case mod   => simp [BinOp.boolResTy] at Hres
  case lt =>
    -- lt with bool args: BinOp.eval gives none → headStep stuck; deferred.
    sorry
  case le =>
    sorry
  case and =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [hbool]
    iapply (refines_binop_pure .and _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 && b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case or =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [hbool]
    iapply (refines_binop_pure .or _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 || b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case xor =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [hbool]
    iapply (refines_binop_pure .xor _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 ^^ b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case eq =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [hbool]
    iapply (refines_binop_pure .eq _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide ((BaseLit.bool b1) = .bool b2))
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_int_unop (Δ : TyEnv GF) (Γ : RelCtx GF)
    (op : UnOp) {e e' : Exp} {τ : Ty}
    (Hres : op.intResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.unop op e) (.unop op e') τ := by
  -- Only `op = .minus` is consistent with `op.intResTy = some τ`, with τ = .int.
  cases op with
  | neg => simp [UnOp.intResTy] at Hres
  | minus =>
    simp [UnOp.intResTy] at Hres; subst Hres
    iintro IH
    unfold bin_log_related_ty bin_log_related
    iintro %vs #Hvs
    ihave IH' := IH $$ %vs Hvs
    rw [Exp.substMap_unop, Exp.substMap_unop]
    have hint : (interp Ty.int Δ : lrel GF) = lrel_int := rfl
    rw [hint]
    ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
        lrel_int) $$ [IH']
    · rw [← hint]; iexact IH'
    -- Bind e/e' to extract the int value n.
    rw [show Exp.unop UnOp.minus (Exp.substMap vs.fst e) =
          Ectx.fill [EctxItem.unop UnOp.minus] (Exp.substMap vs.fst e) from rfl,
        show Exp.unop UnOp.minus (Exp.substMap vs.snd e') =
          Ectx.fill [EctxItem.unop UnOp.minus] (Exp.substMap vs.snd e') from rfl]
    iapply (refines_bind [EctxItem.unop UnOp.minus] [EctxItem.unop UnOp.minus]
      (A := lrel_int)) $$ [IH'']
    · iexact IH''
    iintro %v %v' Hint
    ihave HvEx := lrel_int_unfold v v' $$ Hint
    icases HvEx with ⟨%n, %hv, %hv'⟩
    rw [show Ectx.fill [EctxItem.unop UnOp.minus] v.1 = Exp.unop UnOp.minus v.1 from rfl,
        show Ectx.fill [EctxItem.unop UnOp.minus] v'.1 = Exp.unop UnOp.minus v'.1 from rfl,
        hv, hv']
    -- Goal: refines ⊤ (.unop minus #n) (.unop minus #n) lrel_int.
    have heval : UnOp.eval .minus (Exp.lit (.int n)) = some (Exp.lit (.int n.neg)) := rfl
    have hφ : (Exp.lit (.int n)).isValue ∧ UnOp.eval .minus (Exp.lit (.int n)) = some _ :=
      ⟨IsVal.lit.toIsValue, heval⟩
    have hf1 : Exp.unop .minus (.lit (.int n)) =
        Ectx.fill [] (Exp.unop .minus (.lit (.int n))) := rfl
    rw [hf1]
    iapply (refines_pure_l (K := []) (Hex := pureExec_unop) hφ)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_unop) hφ)
    iapply refines_ret (e1 := Ectx.fill [] (Exp.lit (.int n.neg)))
      (e2 := Ectx.fill [] (Exp.lit (.int n.neg)))
      (v1 := ⟨.lit (.int n.neg), IsVal.lit⟩) (v2 := ⟨.lit (.int n.neg), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    unfold lrel_int
    iexists n.neg
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_bool_unop (Δ : TyEnv GF) (Γ : RelCtx GF)
    (op : UnOp) {e e' : Exp} {τ : Ty}
    (Hres : op.boolResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .bool) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.unop op e) (.unop op e') τ := by
  -- Only `op = .neg` is consistent with `op.boolResTy = some τ`, with τ = .bool.
  cases op with
  | minus => simp [UnOp.boolResTy] at Hres
  | neg =>
    simp [UnOp.boolResTy] at Hres; subst Hres
    iintro IH
    unfold bin_log_related_ty bin_log_related
    iintro %vs #Hvs
    ihave IH' := IH $$ %vs Hvs
    rw [Exp.substMap_unop, Exp.substMap_unop]
    have hbool : (interp Ty.bool Δ : lrel GF) = lrel_bool := rfl
    rw [hbool]
    ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
        lrel_bool) $$ [IH']
    · rw [← hbool]; iexact IH'
    rw [show Exp.unop UnOp.neg (Exp.substMap vs.fst e) =
          Ectx.fill [EctxItem.unop UnOp.neg] (Exp.substMap vs.fst e) from rfl,
        show Exp.unop UnOp.neg (Exp.substMap vs.snd e') =
          Ectx.fill [EctxItem.unop UnOp.neg] (Exp.substMap vs.snd e') from rfl]
    iapply (refines_bind [EctxItem.unop UnOp.neg] [EctxItem.unop UnOp.neg]
      (A := lrel_bool)) $$ [IH'']
    · iexact IH''
    iintro %v %v' Hbool
    ihave HvEx := lrel_bool_unfold v v' $$ Hbool
    icases HvEx with ⟨%b, %hv, %hv'⟩
    rw [show Ectx.fill [EctxItem.unop UnOp.neg] v.1 = Exp.unop UnOp.neg v.1 from rfl,
        show Ectx.fill [EctxItem.unop UnOp.neg] v'.1 = Exp.unop UnOp.neg v'.1 from rfl,
        hv, hv']
    have heval : UnOp.eval .neg (Exp.lit (.bool b)) = some (Exp.lit (.bool (¬b))) := rfl
    have hφ : (Exp.lit (.bool b)).isValue ∧ UnOp.eval .neg (Exp.lit (.bool b)) = some _ :=
      ⟨IsVal.lit.toIsValue, heval⟩
    have hf1 : Exp.unop .neg (.lit (.bool b)) =
        Ectx.fill [] (Exp.unop .neg (.lit (.bool b))) := rfl
    rw [hf1]
    iapply (refines_pure_l (K := []) (Hex := pureExec_unop) hφ)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_unop) hφ)
    iapply refines_ret (e1 := Ectx.fill [] (Exp.lit (.bool (¬b))))
      (e2 := Ectx.fill [] (Exp.lit (.bool (¬b))))
      (v1 := ⟨.lit (.bool (¬b)), IsVal.lit⟩) (v2 := ⟨.lit (.bool (¬b)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    unfold lrel_bool
    iexists (¬b)
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_unboxed_eq (Δ : TyEnv GF) (Γ : RelCtx GF)
    {e1 e2 e1' e2' : Exp} {τ : Ty}
    (HUnboxed : UnboxedType τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool) := by
  sorry

theorem bin_log_related_scrut (Δ : TyEnv GF) (Γ : RelCtx GF) {e e' : Exp}
    {p : Pat} {τs τb : Ty} (Hpat : PatTyped τs p τb) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τs) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.scrut e p) (.scrut e' p) (.sum τb .unit) := by
  sorry

theorem bin_log_related_fail (Δ : TyEnv GF) (Γ : RelCtx GF) {τ : Ty} :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ .fail .fail τ := by
  sorry

/-! ## The fundamental theorem

Every well-typed expression is logically related to itself. -/

/-- **Fundamental theorem of the logical relation.** Induction on `Typed`
dispatching each case to its `bin_log_related_*` lemma. The recursive
binder cases (`lam`, `fix`, `tlam`, `tunpack`) recurse on the body's typing
under an extended context. -/
theorem fundamental (Δ : TyEnv GF) (Γtc : Tctx) (Γrc : RelCtx GF)
    (HCtx : TctxRelated Δ Γtc Γrc)
    {e : Exp} {τ : Ty} (Hty : Typed Γtc e τ) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e e τ := by
  -- Full induction on Typed; ~30 cases, most needing the corresponding
  -- bin_log_related_* lemma. Sorried as a whole pending those.
  sorry

/-- Closed specialization: `∅ ⊢ₜ e : τ → ⊢ REL e << e : interp τ Δ`. -/
theorem refines_typed (Δ : TyEnv GF) {e : Exp} {τ : Ty}
    (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines (⊤ : CoPset) e e (interp τ Δ) := by
  have HRel : TctxRelated Δ Tctx.empty ([] : RelCtx GF) := by
    intro x; simp [Tctx.empty, RelCtx.lookup]
  have Hfund := fundamental Δ Tctx.empty [] HRel Hty
  -- Hfund : ⊢ bin_log_related_ty ⊤ Δ [] e e τ
  --       = ⊢ ∀ vs, env_ltyped2 [] vs -∗ refines ⊤ (substMap vs.fst e) (substMap vs.snd e) ...
  -- Specialize at vs := [].
  unfold bin_log_related_ty bin_log_related at Hfund
  -- substMap [] e = e by `Exp.substMap_empty` (applied via ValSubstMap.{fst,snd} of []).
  have h1 : Exp.substMap (ValSubstMap.fst ([] : ValSubstMap)) e = e := rfl
  have h2 : Exp.substMap (ValSubstMap.snd ([] : ValSubstMap)) e = e := rfl
  ihave Hf := Hfund
  -- Goal `refines ⊤ e e (interp τ Δ)` is def-eq to
  -- `refines ⊤ (substMap [].fst e) (substMap [].snd e) (interp τ Δ)`.
  have hgoal_eq : (refines (⊤ : CoPset) e e (interp τ Δ) : IProp GF) =
      refines (⊤ : CoPset)
        (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap)) e)
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap)) e)
        (interp τ Δ) := rfl
  rw [hgoal_eq]
  iapply Hf $$ %([] : ValSubstMap)
  iapply env_ltyped2_empty

end Fundamental

end ProbLang
