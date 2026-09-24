module

public import Metrology.Approxis.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.Model
public import Metrology.Approxis.Compatibility
public import Metrology.Approxis.AppRelRules
public import Metrology.Approxis.ContinuousSampler
public import Metrology.Approxis.RelTactics
public import Metrology.Approxis.Interp

@[expose] public section


/-! # Fundamental Theorem

Fundamental theorem of the logical relation: well-typed terms are related to themselves,
plus per-constructor `bin_log_related_*` compatibility lemmas. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-! ## Tctx → RelCtx lifting -/

/-- `TctxRelated Δ Γtc Γrc` asserts that the relational context `Γrc` is the
pointwise lift of the syntactic context `Γtc` through `interp · Δ`. -/
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp τ Δ) = Γrc.lookup x

/-! ## Compatibility lemmas -/

/-! ### Intro and elim for the literal value relations

`lrel_unit`, `lrel_int`, `lrel_bool` and `lrel_real` each relate two values exactly
when both are the *same* literal. These are the two directions of that reading. -/

theorem bin_log_related_var (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp τ Δ)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup Γ vs x (interp τ Δ) hΓ $$ Hvs with ⟨%v1, %v2, %hvs_eq, HA⟩
  ihave %hfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hfst_lookup : SubstMap.lookup vs.fst x = some v1.1 := by
    rw [ValSubstMap.fst_lookup, hvs_eq]; rfl
  have hsnd_lookup : SubstMap.lookup vs.snd x = some v2.1 := by
    rw [ValSubstMap.snd_lookup, hvs_eq]; rfl
  rw [Exp.substMap_fvar_lookup_some _ _ hfst_closed hfst_lookup,
      Exp.substMap_fvar_lookup_some _ _ hsnd_closed hsnd_lookup]
  iapply (refines_ret (hv1 := rfl) (hv2 := rfl))
  imodintro
  iexact HA

/-- The fresh-atom bridge shared by the binder cases (`lam`, `fix`, `unpack`). Extending
`vs` at a fresh `x` with the pair `(v, v')` and then substituting into an opened body is
the same as opening the already-substituted body at `v`/`v'`. -/
private theorem substMap_open_fresh_pair {vs vs' : ValSubstMap rT} {x : Var} {v v' : Val rT}
    {e e' : Exp rT} (hvs' : vs' = (x, (v, v')) :: vs)
    (hfst : SubstMap.AllClosed vs.fst) (hsnd : SubstMap.AllClosed vs.snd)
    (hxe : x ∉ e.fv) (hxe' : x ∉ e'.fv) (hxdom : x ∉ (vs.map (·.1)).toFinset)
    (hv : v.1.isClosedEmpty) (hv' : v'.1.isClosedEmpty) :
    Exp.substMap vs'.fst (Exp.open' e (.fvar x)) = Exp.open' (Exp.substMap vs.fst e) v.1 ∧
      Exp.substMap vs'.snd (Exp.open' e' (.fvar x)) =
        Exp.open' (Exp.substMap vs.snd e') v'.1 := by
  subst hvs'
  exact ⟨Exp.substMap_open_fresh hfst hxe
      (ValSubstMap.fst_lookup_eq_none_of_not_mem hxdom) hv.1,
    Exp.substMap_open_fresh hsnd hxe'
      (ValSubstMap.snd_lookup_eq_none_of_not_mem hxdom) hv'.1⟩

/-! ### Lifting `refines` compatibility to `bin_log_related`

Every non-binder compatibility lemma shares one envelope: specialise the induction
hypotheses at `vs`, push `substMap` through the constructor, then apply the matching
`refines_*` rule. `bin_log_related_lift{1,2,3}` package that envelope, parameterised
by the constructor `f` and its `substMap` commutation lemma. -/

private theorem bin_log_related_lift1 {Γ : RelCtx rT GF} {e e' : Exp rT}
    {A B : lrel rT GF} {f : Exp rT → Exp rT}
    (hf : ∀ (σ : SubstMap rT) (t : Exp rT), Exp.substMap σ (f t) = f (Exp.substMap σ t))
    (H : ∀ t t' : Exp rT, iprop(refines ⊤ t t' A) ⊢@{IProp GF} refines ⊤ (f t) (f t') B) :
    bin_log_related ⊤ Γ e e' A ⊢@{IProp GF} bin_log_related ⊤ Γ (f e) (f e') B := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [hf, hf]
  iapply (H _ _) $$ IH'

private theorem bin_log_related_lift2 {Γ : RelCtx rT GF} {e1 e2 e1' e2' : Exp rT}
    {A1 A2 B : lrel rT GF} {f : Exp rT → Exp rT → Exp rT}
    (hf : ∀ (σ : SubstMap rT) (t1 t2 : Exp rT),
      Exp.substMap σ (f t1 t2) = f (Exp.substMap σ t1) (Exp.substMap σ t2))
    (H : ∀ t1 t2 t1' t2' : Exp rT, iprop(refines ⊤ t1 t1' A1) ⊢@{IProp GF}
      refines ⊤ t2 t2' A2 -∗ refines ⊤ (f t1 t2) (f t1' t2') B) :
    bin_log_related ⊤ Γ e1 e1' A1 ⊢@{IProp GF}
      bin_log_related ⊤ Γ e2 e2' A2 -∗ bin_log_related ⊤ Γ (f e1 e2) (f e1' e2') B := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [hf, hf]
  iapply (H _ _ _ _) $$ IH1' IH2'

private theorem bin_log_related_lift3 {Γ : RelCtx rT GF} {e0 e1 e2 e0' e1' e2' : Exp rT}
    {A0 A1 A2 B : lrel rT GF} {f : Exp rT → Exp rT → Exp rT → Exp rT}
    (hf : ∀ (σ : SubstMap rT) (t0 t1 t2 : Exp rT), Exp.substMap σ (f t0 t1 t2) =
      f (Exp.substMap σ t0) (Exp.substMap σ t1) (Exp.substMap σ t2))
    (H : ∀ t0 t1 t2 t0' t1' t2' : Exp rT, iprop(refines ⊤ t0 t0' A0) ⊢@{IProp GF}
      refines ⊤ t1 t1' A1 -∗ refines ⊤ t2 t2' A2 -∗
        refines ⊤ (f t0 t1 t2) (f t0' t1' t2') B) :
    bin_log_related ⊤ Γ e0 e0' A0 ⊢@{IProp GF}
      bin_log_related ⊤ Γ e1 e1' A1 -∗ bin_log_related ⊤ Γ e2 e2' A2 -∗
        bin_log_related ⊤ Γ (f e0 e1 e2) (f e0' e1' e2') B := by
  unfold bin_log_related
  iintro IH0 IH1 IH2 %vs #Hvs
  ihave IH0' := IH0 $$ %vs Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [hf, hf]
  iapply (H _ _ _ _ _ _) $$ IH0' IH1' IH2'

/-- A literal is related to itself whenever `A` relates it to itself: substitution is
a no-op on literals, so the pair is already a value. -/
private theorem bin_log_related_lit (Γ : RelCtx rT GF) (l : BaseLit rT) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} bin_log_related ⊤ Γ (.lit l) (.lit l) A := by
  unfold bin_log_related
  iintro %vs _
  rw [Exp.substMap_lit, Exp.substMap_lit,
      show (Exp.lit l : Exp rT) = (Val.ofBaseLit l).1 from rfl]
  iapply (refines_ret (hv1 := rfl) (hv2 := rfl))
  imodintro
  iapply HA

theorem bin_log_related_pair (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ1) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ2 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.pair e1 e2) (.pair e1' e2')
          (.prod τ1 τ2) :=
  bin_log_related_lift2 Exp.substMap_pair fun _ _ _ _ => refines_pair

theorem bin_log_related_fst (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.fst e) (.fst e') τ1 :=
  bin_log_related_lift1 Exp.substMap_fst fun _ _ => refines_fst

theorem bin_log_related_snd (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.snd e) (.snd e') τ2 :=
  bin_log_related_lift1 Exp.substMap_snd fun _ _ => refines_snd

theorem bin_log_related_injl (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ1) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) :=
  bin_log_related_lift1 Exp.substMap_inl fun _ _ => refines_injl

theorem bin_log_related_injr (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ2) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inr e) (.inr e') (.sum τ1 τ2) :=
  bin_log_related_lift1 Exp.substMap_inr fun _ _ => refines_injr

theorem bin_log_related_case (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ1 τ2 τ3 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e0 e0' (.sum τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.arrow τ1 τ3) -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' (.arrow τ2 τ3) -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.case e0 e1 e2) (.case e0' e1' e2') τ3 :=
  bin_log_related_lift3 Exp.substMap_case fun _ _ _ _ _ _ => refines_case

theorem bin_log_related_if (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e0 e0' .bool) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.cond e0 e1 e2) (.cond e0' e1' e2') τ :=
  bin_log_related_lift3 Exp.substMap_cond fun _ _ _ _ _ _ => refines_if

theorem bin_log_related_app (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.arrow τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ1 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.app e1 e2) (.app e1' e2') τ2 :=
  bin_log_related_lift2 Exp.substMap_app fun _ _ _ _ => refines_app

theorem bin_log_related_lam (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} (L : Finset Var)
    (he_lc : ∀ x ∉ L, (Exp.open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ L, (Exp.open' e' (.fvar x)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset)
    (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ x ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ ((x, interp τ1 Δ) :: Γ)
        (Exp.open' e (.fvar x)) (Exp.open' e' (.fvar x)) τ2) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.lam e) (.lam e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  rw [Exp.substMap_lam, Exp.substMap_lam]
  rw [interp_arrow]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hlam_lc : (Exp.lam (Exp.substMap vs.fst e)).IsLocallyClosed :=
    Exp.lam_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc
  have hlam'_lc : (Exp.lam (Exp.substMap vs.snd e')).IsLocallyClosed :=
    Exp.lam_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [ValSubstMap.fst_dom]; exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [ValSubstMap.snd_dom]; exact he'_fv.trans hΓdomVs
  have hlam_closed : (Exp.lam (Exp.substMap vs.fst e)).isClosedEmpty ∧
      (Exp.lam (Exp.substMap vs.snd e')).isClosedEmpty :=
    ⟨⟨hlam_lc, Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst⟩,
      ⟨hlam'_lc, Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd⟩⟩
  iapply (refines_arrow_val
    (v := ⟨Exp.lam (Exp.substMap vs.fst e), IsVal.lam (by is_lc), by is_lc⟩)
    (v' := ⟨Exp.lam (Exp.substMap vs.snd e'), IsVal.lam (by is_lc), by is_lc⟩)
    (hv := hlam_closed))
  iintro !> %v1 %v2 #HA
  ihave %hv1v2_closed : iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ : IProp GF) $$ [HA]
  · iapply (interp_closed τ1 v1 v2)
    iexact HA
  obtain ⟨x, hx⟩ :=
    HasFresh.fresh_exists (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨hxL, hxFvE⟩, hxFvE'⟩, hxNotDom⟩ := hx
  have HbodyAtX := Hbody x hxL
  let vs' : ValSubstMap rT := (x, (v1, v2)) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((x, interp τ1 Δ) :: Γ) vs') $$ [HA]
  · iapply (env_ltyped2_insert Γ vs x (interp τ1 Δ) v1 v2
      hv1v2_closed.1.toFvSubsetEmpty hv1v2_closed.2.toFvSubsetEmpty)
    iframe HA
    iexact Hvs
  unfold bin_log_related_ty bin_log_related at HbodyAtX
  ihave HbodyApplied := HbodyAtX $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hxFvE hxFvE' hxNotDom hv1v2_closed.1 hv1v2_closed.2
  isimp only [hbridge_fst, hbridge_snd] at HbodyApplied
  rw [Ectx.eq_fill_nil (Exp.app (Exp.lam (Exp.substMap vs.fst e)) v1.1),
      Ectx.eq_fill_nil (Exp.app (Exp.lam (Exp.substMap vs.snd e')) v2.1)]
  iapply (refines_pure_l
    (e' := Exp.open' (Exp.substMap vs.fst e) v1.1)
    (Hex := pureExec_app_lam)
    ⟨v1.2.toIsValue, by is_lc⟩)
  inext
  iapply (refines_pure_r
    (e' := Exp.open' (Exp.substMap vs.snd e') v2.1)
    (Hex := pureExec_app_lam)
    ⟨v2.2.toIsValue, by is_lc⟩)
  simp only [Ectx.fill_nil]
  iexact HbodyApplied

theorem bin_log_related_fix (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} (L : Finset Var)
    (he_lc : ∀ f ∉ L, (Exp.open' e (.fvar f)).IsLocallyClosed)
    (he'_lc : ∀ f ∉ L, (Exp.open' e' (.fvar f)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset)
    (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ f ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
        ((f, interp (.arrow τ1 τ2) Δ) :: Γ)
        (Exp.open' e (.fvar f)) (Exp.open' e' (.fvar f)) (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.fix e) (.fix e')
      (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  rw [Exp.substMap_fix, Exp.substMap_fix, interp_arrow]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hfix_lc : (Exp.fix (Exp.substMap vs.fst e)).IsLocallyClosed :=
    Exp.fix_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc
  have hfix'_lc : (Exp.fix (Exp.substMap vs.snd e')).IsLocallyClosed :=
    Exp.fix_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc
  -- Domain agreement.
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [ValSubstMap.fst_dom]; exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [ValSubstMap.snd_dom]; exact he'_fv.trans hΓdomVs
  have hfix_closed : (Exp.fix (Exp.substMap vs.fst e)).isClosedEmpty ∧
      (Exp.fix (Exp.substMap vs.snd e')).isClosedEmpty :=
    ⟨⟨hfix_lc, Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst⟩,
      ⟨hfix'_lc, Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd⟩⟩
  obtain ⟨f, hf⟩ :=
    HasFresh.fresh_exists (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hf
  obtain ⟨⟨⟨hfL, hfFvE⟩, hfFvE'⟩, hfNotDom⟩ := hf
  iapply refines_ret
    (e1 := Exp.fix (Exp.substMap vs.fst e)) (e2 := Exp.fix (Exp.substMap vs.snd e'))
    (v1 := ⟨_, IsVal.fix (by is_lc), by is_lc⟩) (v2 := ⟨_, IsVal.fix (by is_lc), by is_lc⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply (loeb_wand (P := (lrel_arr (interp τ1 Δ) (interp τ2 Δ)).car
    ⟨Exp.fix (Exp.substMap vs.fst e), IsVal.fix (by is_lc), by is_lc⟩
    ⟨Exp.fix (Exp.substMap vs.snd e'), IsVal.fix (by is_lc), by is_lc⟩))
  iintro !>
  iintro #IH
  unfold lrel_arr
  isplitr
  · ipureintro; exact hfix_closed
  iintro !> %v1 %v2 #HA
  rw [Ectx.eq_fill_nil (Exp.app (Exp.fix (Exp.substMap vs.fst e)) v1.1),
      Ectx.eq_fill_nil (Exp.app (Exp.fix (Exp.substMap vs.snd e')) v2.1)]
  iapply (refines_pure_l
    (e' := Exp.app (Exp.open' (Exp.substMap vs.fst e) (Exp.fix (Exp.substMap vs.fst e))) v1.1)
    (Hex := pureExec_app_fix)
    ⟨v1.2.toIsValue, by is_lc⟩)
  inext
  iapply (refines_pure_r
    (e' := Exp.app (Exp.open' (Exp.substMap vs.snd e') (Exp.fix (Exp.substMap vs.snd e'))) v2.1)
    (Hex := pureExec_app_fix)
    ⟨v2.2.toIsValue, by is_lc⟩)
  let fixv : Val rT := ⟨Exp.fix (Exp.substMap vs.fst e), IsVal.fix (by is_lc), by is_lc⟩
  let fixv' : Val rT := ⟨Exp.fix (Exp.substMap vs.snd e'), IsVal.fix (by is_lc), by is_lc⟩
  let vs' : ValSubstMap rT := (f, (fixv, fixv')) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((f, interp (Ty.arrow τ1 τ2) Δ) :: Γ) vs') $$ [IH]
  · rw [interp_arrow]
    iapply (env_ltyped2_insert Γ vs f (lrel_arr (interp τ1 Δ) (interp τ2 Δ))
      fixv fixv' hfix_closed.1.toFvSubsetEmpty hfix_closed.2.toFvSubsetEmpty)
    isplitr [IH]
    · iapply (lrel_arr_fold (interp τ1 Δ) (interp τ2 Δ) fixv fixv')
      iexact IH
    iexact Hvs
  have HbodyAtF := Hbody f hfL
  unfold bin_log_related_ty bin_log_related at HbodyAtF
  ihave HbodyApplied := HbodyAtF $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hfFvE hfFvE' hfNotDom hfix_closed.1 hfix_closed.2
  isimp only [hbridge_fst, hbridge_snd] at HbodyApplied
  ihave HArgs : iprop(refines ⊤ v1.1 v2.1 (interp τ1 Δ)) $$ [HA]
  · iapply refines_ret (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HA
  isimp only [interp_arrow] at HbodyApplied
  ihave Hgoal := refines_app $$ HbodyApplied HArgs
  simp only [Ectx.fill_nil]
  iexact Hgoal

/-! ### Heap and tape cases

These are the discrete fragment: `alloc`/`load`/`store` and the bounded
integer sampler `rand`, whose step rules are stated with atoms. -/

section Discrete

theorem bin_log_related_alloc (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.alloc e) (.alloc e') (.ref τ) :=
  bin_log_related_lift1 Exp.substMap_alloc fun _ _ => refines_alloc

theorem bin_log_related_load (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.ref τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.load e) (.load e') τ :=
  bin_log_related_lift1 Exp.substMap_load fun _ _ => refines_load

theorem bin_log_related_store (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.ref τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.store e1 e2) (.store e1' e2') .unit :=
  bin_log_related_lift2 Exp.substMap_store fun _ _ _ _ => refines_store

theorem bin_log_related_alloctape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.tape e) (.tape e') .tape :=
  bin_log_related_lift1 Exp.substMap_tape fun _ _ => refines_alloctape

/-- `bin_log_related_rand_tape`: ports the labeled-rand compatibility from
`fundamental.v:289`, but at `lrel_int` (not `lrel_nat` as in Rocq), to match
Lean's `Typed.rand` signature. Discharges via `refines_rand_tape_int` from
`Compatibility.lean`. -/
theorem bin_log_related_rand_tape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .tape -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 Exp.substMap_rand fun _ _ _ _ => refines_rand_tape_int

/-- `bin_log_related_rand_unit`: ports unlabeled-rand compatibility, at `lrel_int`.
The second argument is `()`, so binding it exposes the `randL` redex that
`refines_rand_unit_int` consumes. -/
theorem bin_log_related_rand_unit (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .unit -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 Exp.substMap_rand fun t1 t2 t1' _ => by
    -- `iapply` matches syntactically, so expose `lrel_int`/`lrel_unit` first.
    rw [interp_int, interp_unit]
    iintro IH1 IH2
    rw [← Ectx.fill_randR t1, ← Ectx.fill_randR t1']
    iapply (refines_bind [EctxItem.randR t1] [EctxItem.randR t1'] (A := lrel_unit)) $$ [IH2]
    · iexact IH2
    iintro %v2 %v2' Hu
    icases lrel_unit_unfold v2 v2' $$ Hu with ⟨%hv2, %hv2'⟩
    rw [hv2, hv2',
        show Ectx.fill [EctxItem.randR t1] pl(#(.unit)) =
          Ectx.fill [EctxItem.randL .unit] t1 from rfl,
        show Ectx.fill [EctxItem.randR t1'] pl(#(.unit)) =
          Ectx.fill [EctxItem.randL .unit] t1' from rfl]
    iapply refines_rand_unit_int $$ IH1

/-! ### Polymorphic / recursive type compatibility -/

end Discrete

/-! #### OFE-rewrite helper for `bin_log_related`

Several polymorphic cases (`tapp`, `fold`, `unfold`, `pack`) need to
transport a `bin_log_related` hypothesis along an OFE-equivalence
`A = B` between the underlying lrels. This is `refines_proper` lifted
through `bin_log_related`'s `∀ vs, env_ltyped2 Γ vs -∗ refines _ _ _ A`
shape. We expose it both as an `=` (`bin_log_related_proper`) and
as an entailment (`bin_log_related_proper_entails`) for direct use
inside iris-tactics. -/

theorem bin_log_related_proper (E : CoPset) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {A B : lrel rT GF} (h : A = B) :
    bin_log_related E Γ e e' A = bin_log_related E Γ e e' B := by
  unfold bin_log_related
  refine OFE.eq_dist.mpr fun n => ?_
  refine forall_ne fun vs => ?_
  refine wand_ne.ne .rfl ?_
  exact refines_ne (OFE.eq_dist_1 h n)

theorem bin_log_related_proper_entails (E : CoPset) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {A B : lrel rT GF} (h : A = B) :
    bin_log_related E Γ e e' A ⊢@{IProp GF} bin_log_related E Γ e e' B :=
  (Iris.BI.equiv_iff.mp (bin_log_related_proper E Γ e e' h)).1

/-- Type-flavored Q2: rewrite at the level of `bin_log_related_ty` when
two interpreted types are OFE-equivalent. -/
theorem bin_log_related_ty_proper_entails (E : CoPset) (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {τ1 τ2 : Ty} (h : interp τ1 Δ = (interp τ2 Δ : lrel rT GF)) :
    bin_log_related_ty E Δ Γ e e' τ1 ⊢@{IProp GF}
      bin_log_related_ty E Δ Γ e e' τ2 :=
  bin_log_related_proper_entails E Γ e e' h

/-- Refines OFE-rewrite: bridge `refines E e e' A` and `refines E e e' B`
along an OFE-equivalence `A = B`. Useful in proof bodies where we have
a `refines` hypothesis at one relation and need it at an equivalent one. -/
theorem refines_proper_entails (E : CoPset) (e e' : Exp rT) {A B : lrel rT GF}
    (h : A = B) :
    refines E e e' A ⊢@{IProp GF} refines E e e' B :=
  (Iris.BI.equiv_iff.mp (refines_proper h)).1

omit [ProbLangℝ rT] in
/-- lrel-level OFE-rewrite at a value pair: bridge `A v v'` and `B v v'`
when `A = B`. Used for value-relation level rewrites under e.g.
`lrel_exists` instantiation. -/
theorem lrel_car_proper_entails {A B : lrel rT GF} (h : A = B) (v v' : Val rT) :
    A.car v v' ⊢@{IProp GF} B.car v v' :=
  h ▸ .rfl

/-- Unfold helper: bridge `(lrel_forall C).car v v'` to its underlying
`∀ A, (lrel_arr lrel_unit (C A)).car v v'` form. The two are defeq but
iris-tactic unification doesn't reduce through `.car`/`lrel.mk`. -/
theorem lrel_forall_unfold (C : lrel rT GF → lrel rT GF) (v v' : Val rT) :
    (lrel_forall C).car v v' ⊢@{IProp GF}
      ∀ (A : lrel rT GF), (lrel_arr lrel_unit (C A)).car v v' :=
  .rfl

theorem bin_log_related_tlam (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty}
    (he_lc : e.IsLocallyClosed) (he'_lc : e'.IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset)
    (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ A : lrel rT GF,
      ⊢@{IProp GF} □ (bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ) Γ e e' τ)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.lam e) (.lam e') (.forall' τ) := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  rw [Exp.substMap_lam, Exp.substMap_lam]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hbody_lc : (Exp.substMap vs.fst e).IsLocallyClosed :=
    Exp.substMap_lc hvsfst_closed he_lc
  have hbody'_lc : (Exp.substMap vs.snd e').IsLocallyClosed :=
    Exp.substMap_lc hvssnd_closed he'_lc
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [ValSubstMap.fst_dom]; exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [ValSubstMap.snd_dom]; exact he'_fv.trans hΓdomVs
  have hbody_fv : (Exp.substMap vs.fst e).fv = ∅ :=
    Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst
  have hbody'_fv : (Exp.substMap vs.snd e').fv = ∅ :=
    Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd
  have harr : (interp (Ty.forall' τ) Δ : lrel rT GF) =
      lrel_forall (fun A => interp τ (TyEnv.cons A Δ)) := rfl
  rw [harr]
  iapply (refines_forall (e' := Exp.substMap vs.snd e')
    (C := fun A => interp τ (TyEnv.cons A Δ))
    hbody_lc hbody'_lc hbody_fv hbody'_fv)
  iintro !> %A
  have HbodyAtA := Hbody A
  unfold bin_log_related_ty bin_log_related at HbodyAtA
  iapply HbodyAtA $$ Hvs

theorem bin_log_related_tapp (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.forall' τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ
        (.app e pl(#(.unit))) (.app e' pl(#(.unit))) (τ.single τ') := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_app, Exp.substMap_app, Exp.substMap_lit, Exp.substMap_lit]
  have hb1 : Exp.app (Exp.substMap vs.fst e) pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (Exp.substMap vs.fst e) := rfl
  have hb2 : Exp.app (Exp.substMap vs.snd e') pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (Exp.substMap vs.snd e') := rfl
  rw [hb1, hb2]
  iapply (refines_bind [EctxItem.appL .unit] [EctxItem.appL .unit] (A := interp (Ty.forall' τ) Δ)
    (A' := interp (Ty.single τ τ') Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' Hv
  have hbridge_forall : (interp (Ty.forall' τ) Δ).car v v' =
      (lrel_forall (fun A => interp τ (TyEnv.cons A Δ))).car v v' := rfl
  isimp only [hbridge_forall] at Hv
  ihave HvF := lrel_forall_unfold (fun A => interp τ (TyEnv.cons A Δ)) v v' $$ Hv
  ihave HvSpec := HvF $$ %(interp τ' Δ)
  ihave HvArr := lrel_arr_unfold_wand lrel_unit
    (interp τ (TyEnv.cons (interp τ' Δ) Δ)) v v' $$ HvSpec
  ihave HvArr2 := HvArr $$ %(.unit : Val rT) %(.unit : Val rT)
  ihave HvApp : iprop(refines ⊤ (Exp.app v.1 pl(#(.unit))) (Exp.app v'.1 pl(#(.unit)))
      (interp τ (TyEnv.cons (interp τ' Δ) Δ))) $$ [HvArr2]
  · ihave HUnit := lrel_unit_lit
    iapply HvArr2 $$ HUnit
  have hsub : interp τ (TyEnv.cons (interp τ' Δ) Δ) = interp (Ty.single τ τ') Δ :=
    (interp_subst τ' τ Δ).symm
  ihave HvAppFinal := refines_proper_entails ⊤ (Exp.app v.1 pl(#(.unit)))
    (Exp.app v'.1 pl(#(.unit))) hsub $$ HvApp
  have hbridge1 : Ectx.fill [EctxItem.appL .unit] v.1 = Exp.app v.1 pl(#(.unit)) := rfl
  have hbridge2 : Ectx.fill [EctxItem.appL .unit] v'.1 = Exp.app v'.1 pl(#(.unit)) := rfl
  rw [hbridge1, hbridge2]
  iexact HvAppFinal

/-- One-step unfolding of `interp (.rec' τ) Δ` at a value pair: `lrel_rec_unfold`
at the non-expansive functor `X ↦ interp τ (X :: Δ)`. -/
private theorem interp_rec_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp (Ty.rec' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        ▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') :=
  congrArg (fun A => A.car v v') (lrel_rec_unfold (GF := GF)
    { f := fun X => interp τ (TyEnv.cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE τ).ne (TyEnv.cons_ne_head hXY)⟩ })

/-- `interp (.exists' τ) Δ` at a value pair. -/
private theorem interp_exists_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp (Ty.exists' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        (∃ A : lrel rT GF, (interp τ (TyEnv.cons A Δ)).car v v')) :=
  rfl

theorem bin_log_related_fold (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (τ.single (.rec' τ))) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.rec' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  have hsub : interp (Ty.single τ (.rec' τ)) Δ =
      interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ) :=
    interp_subst (.rec' τ) τ Δ
  ihave IH'' := refines_proper_entails ⊤ (Exp.substMap vs.fst e)
    (Exp.substMap vs.snd e') hsub $$ IH'
  iapply refines_wand $$ IH''
  iintro %v %v' #Hv !>
  rw [interp_rec_car Δ τ v v']
  isplitr
  · iapply (interp_closed τ v v')
    iexact Hv
  imodintro
  iexact Hv

theorem bin_log_related_unfold (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.rec' τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ
        (.app recUnfold e) (.app recUnfold e') (τ.single (.rec' τ)) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_app, Exp.substMap_app]
  -- substMap on recUnfold: recUnfold = .lam (.bvar 0) is closed; substMap is a no-op.
  have hru1 : Exp.substMap vs.fst recUnfold = recUnfold := by
    show Exp.substMap vs.fst (.lam (.bvar 0)) = _
    simp [Exp.substMap_lam, Exp.substMap_bvar, recUnfold]
  have hru2 : Exp.substMap vs.snd recUnfold = recUnfold := by
    show Exp.substMap vs.snd (.lam (.bvar 0)) = _
    simp [Exp.substMap_lam, Exp.substMap_bvar, recUnfold]
  rw [hru1, hru2]
  -- Bind under [appR recUnfold] on each side to consume IH'.
  rw [← Ectx.fill_appR recUnfold, ← Ectx.fill_appR recUnfold]
  iapply (refines_bind [EctxItem.appR recUnfold] [EctxItem.appR recUnfold]
    (A := interp (Ty.rec' τ) Δ)
    (A' := interp (Ty.single τ (.rec' τ)) Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' Hv
  -- Hv : (interp (.rec' τ) Δ).car v v'.
  -- Unfold via lrel_rec_unfold: Hv = ⌜...⌝ ∗ ▷ (interp τ (cons (rec' τ) Δ) Δ).car v v'.
  isimp only [interp_rec_car Δ τ v v'] at Hv
  ihave HvL : iprop(▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') $$ [Hv]
  · icases Hv with ⟨_, HvLater⟩
    iexact HvLater
  -- Hv : ▷ (interp τ (cons (rec' τ) Δ) Δ).car v v'.
  -- Pure-step `app recUnfold v → v` on each side. The pure_l step gives a ▷-budget.
  have hfL : Ectx.fill [EctxItem.appR recUnfold] v.1 =
      Ectx.fill ([] : Ectx rT) (Exp.app (.lam (.bvar 0)) v.1) := rfl
  have hfR : Ectx.fill [EctxItem.appR recUnfold] v'.1 =
      Ectx.fill ([] : Ectx rT) (Exp.app (.lam (.bvar 0)) v'.1) := rfl
  rw [hfL, hfR]
  have hopenL : Exp.open' (.bvar 0) v.1 = v.1 := by simp [Exp.open', Exp.openRec]
  have hopenR : Exp.open' (.bvar 0) v'.1 = v'.1 := by simp [Exp.open', Exp.openRec]
  iapply (refines_pure_l
    (e' := Exp.open' (.bvar 0) v.1)
    (Hex := pureExec_app_lam)
    ⟨v.2.toIsValue, by is_lc⟩)
  inext
  -- Now HvL's ▷ has been stripped: HvL : (interp τ (cons (rec' τ) Δ) Δ).car v v'.
  rw [hopenL]
  iapply (refines_pure_r
    (e' := Exp.open' (.bvar 0) v'.1)
    (Hex := pureExec_app_lam) ⟨v'.2.toIsValue, by is_lc⟩)
  rw [hopenR]
  iapply refines_ret (e1 := Ectx.fill [] v.1) (e2 := Ectx.fill [] v'.1)
    (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  -- Goal: (interp (τ.single (.rec' τ)) Δ).car v v'.
  -- Bridge to (interp τ (cons (rec' τ) Δ) Δ).car v v' via interp_subst, then close with Hv.
  have hsub_eq : (interp (Ty.single τ (.rec' τ)) Δ).car v v' =
      (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v' :=
    congrArg (fun A => A.car v v') (interp_subst (.rec' τ) τ Δ)
  rw [hsub_eq]
  iexact HvL

theorem bin_log_related_pack (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (τ.single τ')) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.exists' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  -- IH' : refines ⊤ ... (interp (τ.single τ' = τ[τ'/0]) Δ).
  -- Via interp_subst: = refines ⊤ ... (interp τ (cons (interp τ' Δ) Δ)).
  have hsub : interp (Ty.single τ τ') Δ = interp τ (TyEnv.cons (interp τ' Δ) Δ) :=
    interp_subst τ' τ Δ
  ihave IH'' := refines_proper_entails ⊤ (Exp.substMap vs.fst e)
    (Exp.substMap vs.snd e') hsub $$ IH'
  -- Goal: refines ⊤ ... (interp (.exists' τ) Δ) = lrel_exists (fun X => interp τ (cons X Δ)).
  -- Pack at witness `interp τ' Δ` via refines_wand. Closedness extracted via interp_closed.
  iapply refines_wand $$ IH''
  iintro %v %v' Hv !>
  -- Extract closedness from Hv as a persistent pure fact (doesn't consume Hv).
  ihave %Hclosed : iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ : IProp GF) $$ [Hv]
  · iapply (interp_closed τ v v')
    iexact Hv
  -- Goal: (interp (.exists' τ) Δ).car v v' =
  --       ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗ ∃ A, (interp τ (cons A Δ)).car v v'.
  rw [interp_exists_car Δ τ v v']
  isplitr
  · ipureintro; exact Hclosed
  iexists (interp τ' Δ)
  iexact Hv

/-- **Statement:** unpack of an existentially-typed `e1` into a binder `x` in `e2`,
yielding type `τ2`. **Proof obligation:** bind e1, e1' at `Ty.exists' τ` to get
related values v, v' with `(lrel_exists ...).car v v'`. Destructure to extract
the witness type A and the v, v' relation `(interp τ (cons A Δ)).car v v'`.
Pick fresh atom x. Use `HIH2 A x` (specialized at A and fresh x) to get
the body's bin_log_related under `(cons A Δ)` and `((x, A) :: Γ)`. Combine
with closedness of v, v' (via interp_closed), do env_ltyped2_insert with the
extracted A.car, and bridge via substMap_open_fresh. Mirrors lam template
but with both Δ-extension AND Γ-extension. -/
theorem bin_log_related_unpack (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) (L : Finset Var)
    {e1 e1' e2 e2' : Exp rT} {τ τ2 : Ty}
    (HIH1 : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (Ty.exists' τ))
    (he2_lc : ∀ x ∉ L, (Exp.open' e2 (.fvar x)).IsLocallyClosed)
    (he2'_lc : ∀ x ∉ L, (Exp.open' e2' (.fvar x)).IsLocallyClosed)
    (HIH2 : ∀ A : lrel rT GF, ∀ x ∉ L,
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ)
        ((x, interp τ (TyEnv.cons A Δ)) :: Γ)
        (Exp.open' e2 (.fvar x)) (Exp.open' e2' (.fvar x)) τ2.shift) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ
      (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  -- Specialize HIH1 (Lean-level) at vs.
  have HIH1_sp := HIH1
  unfold bin_log_related_ty bin_log_related at HIH1_sp
  ihave HIH1' := HIH1_sp $$ %vs Hvs
  -- HIH1' : refines ⊤ (substMap vs.fst e1) (substMap vs.snd e1') (interp (.exists' τ) Δ)
  -- Bind to get values v, v' with (interp (.exists' τ) Δ).car v v'.
  rw [Exp.substMap_app, Exp.substMap_app, Exp.substMap_lam, Exp.substMap_lam]
  -- Closedness machinery (analogous to lam).
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  -- Bind under [appR (.lam (substMap vs.fst e2))] for e1, similarly for spec.
  have hlam2_lc : (Exp.lam (Exp.substMap vs.fst e2)).IsLocallyClosed :=
    Exp.lam_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he2_lc
  have hlam2'_lc : (Exp.lam (Exp.substMap vs.snd e2')).IsLocallyClosed :=
    Exp.lam_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he2'_lc
  rw [← Ectx.fill_appR (Exp.lam (Exp.substMap vs.fst e2)),
      ← Ectx.fill_appR (Exp.lam (Exp.substMap vs.snd e2'))]
  iapply (refines_bind [EctxItem.appR (Exp.lam (Exp.substMap vs.fst e2))]
    [EctxItem.appR (Exp.lam (Exp.substMap vs.snd e2'))]
    (A := interp (Ty.exists' τ) Δ)) $$ [HIH1']
  · iexact HIH1'
  iintro %v %v' #Hv
  -- Hv : (interp (.exists' τ) Δ).car v v' = ⌜closed⌝ ∗ ∃ A, (interp τ (cons A Δ)).car v v'.
  -- Destructure.
  isimp only [interp_exists_car Δ τ v v'] at Hv
  icases Hv with ⟨%hvc, %A, #HvA⟩
  -- Now Hv (we destructured): %hvc : closed; %A : witness lrel; HvA : (interp τ (cons A Δ)).car v
  -- v'.
  -- Pick fresh atom x.
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e2.fv ∪ e2'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨hxL, hxFvE2⟩, hxFvE2'⟩, hxNotDom⟩ := hx
  -- Beta-step the application: (.lam e2).app v reduces to open' e2 v.
  rw [Ectx.fill_appR,
      Ectx.eq_fill_nil (Exp.app (Exp.lam (Exp.substMap vs.fst e2)) v.1),
      Ectx.fill_appR,
      Ectx.eq_fill_nil (Exp.app (Exp.lam (Exp.substMap vs.snd e2')) v'.1)]
  iapply (refines_pure_l
    (e' := Exp.open' (Exp.substMap vs.fst e2) v.1)
    (Hex := pureExec_app_lam)
    ⟨v.2.toIsValue, by is_lc⟩)
  inext
  iapply (refines_pure_r
    (e' := Exp.open' (Exp.substMap vs.snd e2') v'.1)
    (Hex := pureExec_app_lam) ⟨v'.2.toIsValue, by is_lc⟩)
  -- Goal: refines ⊤ ([].fill (open' (substMap vs.fst e2) v.1)) ([].fill (open' (substMap vs.snd
  -- e2') v'.1)) (interp τ2 Δ).
  -- Use HIH2 at A and x. vs' := (x, (v, v')) :: vs.
  let vs' : ValSubstMap rT := (x, (v, v')) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((x, interp τ (TyEnv.cons A Δ)) :: Γ) vs') $$ [HvA]
  · iapply (env_ltyped2_insert Γ vs x (interp τ (TyEnv.cons A Δ)) v v'
      hvc.1.toFvSubsetEmpty hvc.2.toFvSubsetEmpty)
    iframe HvA
    iexact Hvs
  -- Apply HIH2 at A and x.
  have HIH2AtAX := HIH2 A x hxL
  unfold bin_log_related_ty bin_log_related at HIH2AtAX
  ihave HBody_shift := HIH2AtAX $$ Hvs'
  -- Bridge interp τ2.shift (cons A Δ) = interp τ2 Δ via interp_ren.
  have hshift : interp τ2.shift (TyEnv.cons A Δ) = interp τ2 Δ := interp_ren τ2 A Δ
  ihave HBody := refines_proper_entails ⊤
    (Exp.substMap vs'.fst (Exp.open' e2 (.fvar x)))
    (Exp.substMap vs'.snd (Exp.open' e2' (.fvar x))) hshift $$ HBody_shift
  -- Bridge via substMap_open_fresh.
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hxFvE2 hxFvE2' hxNotDom hvc.1 hvc.2
  isimp only [hbridge_fst, hbridge_snd] at HBody
  -- Bridge ectx fill to bare expr.
  simp only [Ectx.fill_nil]
  iexact HBody

/-! ### Operator / scrut compatibility

`lrel_int`, `lrel_bool` and `lrel_real` all relate a value to itself exactly when
both sides are the *same* literal, so all six operator lemmas share one envelope:
bind the operands, read off the common literal, then take a pure step. The envelope
is `refines_{un,bin}op_bind`, parameterised by the literal family `V`; the step is
`refines_{un,bin}op_val`. -/

/-- One pure step of a `binop` on two values whose result is the literal `l`. -/
private theorem refines_binop_val (op : BinOp) (w1 w2 : Val rT) {l : BaseLit rT}
    {A : lrel rT GF} (heval : op.eval w1.1 w2.1 = some (.lit l))
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines ⊤ (.binop op w1.1 w2.1) (.binop op w1.1 w2.1) A :=
  refines_binop_pure op _ _ _ w1.2 w2.2 IsVal.lit heval HA

/-- One pure step of a `unop` on a value whose result is the literal `l`. -/
private theorem refines_unop_val (op : UnOp) (w : Val rT) {l : BaseLit rT}
    {A : lrel rT GF} (heval : op.eval w.1 = some (.lit l))
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines ⊤ (.unop op w.1) (.unop op w.1) A :=
  refines_unop_pure op _ _ w.2 IsVal.lit heval HA

/-- Bind both operands of a `binop` at a relation `A` that forces the two sides to
be the *same* value `V i`; the continuation then works on literals only. -/
private theorem refines_binop_bind (op : BinOp) {ι : Type _} (V : ι → Val rT)
    {A B : lrel rT GF} {e1 e2 e1' e2' : Exp rT}
    (hA : ∀ v v' : Val rT, A.car v v' ⊢@{IProp GF} ∃ i : ι, ⌜v = V i ∧ v' = V i⌝) :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      refines ⊤ e2 e2' A -∗
        (∀ (i1 i2 : ι), refines ⊤ (.binop op (V i1).1 (V i2).1)
          (.binop op (V i1).1 (V i2).1) B) -∗
          refines ⊤ (.binop op e1 e2) (.binop op e1' e2') B := by
  iintro IH1 IH2 Hcont
  -- Bind e2/e2' first, then e1/e1'.
  rw [show Exp.binop op e1 e2 = Ectx.fill [EctxItem.binopR op e1] e2 from rfl,
      show Exp.binop op e1' e2' = Ectx.fill [EctxItem.binopR op e1'] e2' from rfl]
  iapply (refines_bind [EctxItem.binopR op e1] [EctxItem.binopR op e1'] (A := A)) $$ [IH2]
  · iexact IH2
  iintro %v2 %v2' Hv2
  icases hA v2 v2' $$ Hv2 with ⟨%i2, %hv2, %hv2'⟩
  rw [show Ectx.fill [EctxItem.binopR op e1] v2.1 = Exp.binop op e1 v2.1 from rfl,
      show Ectx.fill [EctxItem.binopR op e1'] v2'.1 = Exp.binop op e1' v2'.1 from rfl,
      hv2, hv2',
      show Exp.binop op e1 (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1 from rfl,
      show Exp.binop op e1' (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1' from rfl]
  iapply (refines_bind [EctxItem.binopL op (V i2)] [EctxItem.binopL op (V i2)]
    (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v1 %v1' Hv1
  icases hA v1 v1' $$ Hv1 with ⟨%i1, %hv1, %hv1'⟩
  rw [show Ectx.fill [EctxItem.binopL op (V i2)] v1.1 = Exp.binop op v1.1 (V i2).1 from rfl,
      show Ectx.fill [EctxItem.binopL op (V i2)] v1'.1 = Exp.binop op v1'.1 (V i2).1 from rfl,
      hv1, hv1']
  ihave Hgoal := Hcont $$ %i1 %i2
  iexact Hgoal

/-- Unary counterpart of `refines_binop_bind`. -/
private theorem refines_unop_bind (op : UnOp) {ι : Type _} (V : ι → Val rT)
    {A B : lrel rT GF} {e e' : Exp rT}
    (hA : ∀ v v' : Val rT, A.car v v' ⊢@{IProp GF} ∃ i : ι, ⌜v = V i ∧ v' = V i⌝) :
    iprop(refines ⊤ e e' A) ⊢@{IProp GF}
      (∀ i : ι, refines ⊤ (.unop op (V i).1) (.unop op (V i).1) B) -∗
        refines ⊤ (.unop op e) (.unop op e') B := by
  iintro IH Hcont
  rw [show Exp.unop op e = Ectx.fill [EctxItem.unop op] e from rfl,
      show Exp.unop op e' = Ectx.fill [EctxItem.unop op] e' from rfl]
  iapply (refines_bind [EctxItem.unop op] [EctxItem.unop op] (A := A)) $$ [IH]
  · iexact IH
  iintro %v %v' Hv
  icases hA v v' $$ Hv with ⟨%i, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.unop op] v.1 = Exp.unop op v.1 from rfl,
      show Ectx.fill [EctxItem.unop op] v'.1 = Exp.unop op v'.1 from rfl,
      hv, hv']
  ihave Hgoal := Hcont $$ %i
  iexact Hgoal

/-- Int-typed binops: `plus`…`mod`, `shl`, `shr` land in `lrel_int`; `eq`, `lt`, `le`
land in `lrel_bool`; `and`/`or`/`xor` are not int ops, so `Hres` is contradictory. -/
theorem bin_log_related_int_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp rT} {τ : Ty}
    (Hres : op.intResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .int -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => Exp.substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_int]
    iintro IH1 IH2
    iapply (refines_binop_bind op Val.int lrel_int_unfold) $$ IH1 IH2
    iintro %n1 %n2
    cases op <;> simp [BinOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply (refines_binop_val _ _ _ rfl (lrel_int_lit _)))
      | (rw [interp_bool]; iapply (refines_binop_val _ _ _ rfl (lrel_bool_lit _)))

/-- Bool-typed binops: `and`, `or`, `xor`, `eq` land in `lrel_bool`; the rest are not
bool ops, so `Hres` is contradictory. -/
theorem bin_log_related_bool_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp rT} {τ : Ty}
    (Hres : op.boolResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .bool) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .bool -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => Exp.substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_bool]
    iintro IH1 IH2
    iapply (refines_binop_bind op Val.bool lrel_bool_unfold) $$ IH1 IH2
    iintro %b1 %b2
    cases op <;> simp [BinOp.boolResTy] at Hres <;> subst Hres
    all_goals (rw [interp_bool]; iapply (refines_binop_val _ _ _ rfl (lrel_bool_lit _)))

/-- Int-typed unops: `minus` lands in `lrel_int`, `toReal` in `lrel_real`. -/
theorem bin_log_related_int_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : UnOp) {e e' : Exp rT} {τ : Ty}
    (Hres : op.intResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => Exp.substMap_unop σ op) fun _ _ => by
    rw [interp_int]
    iintro IH
    iapply (refines_unop_bind op Val.int lrel_int_unfold) $$ IH
    iintro %n
    cases op <;> simp [UnOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply (refines_unop_val _ _ rfl (lrel_int_lit _)))
      | (rw [interp_real]; iapply (refines_unop_val _ _ rfl (lrel_real_lit _)))

/-! ### The real fragment

`lrel_real` relates two values exactly when both are the *same* real literal, so
the two sides of a real operation always step to a common result and
`refines_{unop,binop}_pure` applies directly. -/

/-- Real-typed unops: `minus`, `toReal` and `frac` all land in `lrel_real`. -/
theorem bin_log_related_real_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : UnOp) {e e' : Exp rT} {τ : Ty}
    (Hres : op.realResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .real) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => Exp.substMap_unop σ op) fun _ _ => by
    rw [interp_real]
    iintro IH
    iapply (refines_unop_bind op Val.real lrel_real_unfold) $$ IH
    iintro %r
    cases op <;> simp [UnOp.realResTy] at Hres <;> subst Hres
    all_goals (rw [interp_real]; iapply (refines_unop_val _ _ rfl (lrel_real_lit _)))

/-- Real-typed binops: `plus` lands in `lrel_real`, the comparisons in `lrel_bool`. -/
theorem bin_log_related_real_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp rT} {τ : Ty}
    (Hres : op.realResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .real) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .real -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => Exp.substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_real]
    iintro IH1 IH2
    iapply (refines_binop_bind op Val.real lrel_real_unfold) $$ IH1 IH2
    iintro %r1 %r2
    cases op <;> simp [BinOp.realResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_real]; iapply (refines_binop_val _ _ _ rfl (lrel_real_lit _)))
      | (rw [interp_bool]; iapply (refines_binop_val _ _ _ rfl (lrel_bool_lit _)))

/-- **The continuous sampler is self-related at `real`.** Couple the two `urand`
draws along the identity — which is trivially measure-preserving — and return the
common sample. -/
theorem bin_log_related_urand (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ .urand .urand .real := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs _
  rw [Exp.substMap_urand, Exp.substMap_urand, interp_real,
      show (Exp.urand : Exp rT) = Ectx.fill [] Exp.urand from rfl]
  iapply (refines_couple_urands_lr (K' := []) id
    (MeasureTheory.MeasurePreserving.id _))
  iintro %r _
  simp only [id_eq]
  iapply (refines_ret (e1 := Ectx.fill [] pl(#(.real r))) (e2 := Ectx.fill [] pl(#(.real r)))
    (v1 := Val.real r) (v2 := Val.real r) (hv1 := rfl) (hv2 := rfl))
  imodintro
  iapply (lrel_real_lit r)

/-- Bool-typed unops: only `neg` is a bool op, and it lands in `lrel_bool`. -/
theorem bin_log_related_bool_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : UnOp) {e e' : Exp rT} {τ : Ty}
    (Hres : op.boolResTy = some τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .bool) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => Exp.substMap_unop σ op) fun _ _ => by
    rw [interp_bool]
    iintro IH
    iapply (refines_unop_bind op Val.bool lrel_bool_unfold) $$ IH
    iintro %b
    cases op <;> simp [UnOp.boolResTy] at Hres
    subst Hres
    rw [interp_bool]
    iapply (refines_unop_val _ _ rfl (lrel_bool_lit _))

/-- **Statement:** `eq` of two `UnboxedType`-related arguments is related at `bool`.
Mirrors Rocq's `bin_log_related_unboxed_eq` (fundamental.v ~167). -/
theorem bin_log_related_unboxed_eq (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty}
    (HUnboxed : UnboxedType τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_binop, Exp.substMap_binop]
  -- Bind e2, e2' first.
  rw [← Ectx.fill_binopR .eq (Exp.substMap vs.fst e1),
      ← Ectx.fill_binopR .eq (Exp.substMap vs.snd e1')]
  iapply (refines_bind [EctxItem.binopR .eq (Exp.substMap vs.fst e1)]
    [EctxItem.binopR .eq (Exp.substMap vs.snd e1')] (A := interp τ Δ)) $$ [IH2']
  · iexact IH2'
  iintro %v2 %v2' #Hv2
  -- Bind e1, e1' next.
  have hbL : Ectx.fill [EctxItem.binopR .eq (Exp.substMap vs.fst e1)] v2.1 =
      Ectx.fill [EctxItem.binopL .eq v2] (Exp.substMap vs.fst e1) := rfl
  have hbL' : Ectx.fill [EctxItem.binopR .eq (Exp.substMap vs.snd e1')] v2'.1 =
      Ectx.fill [EctxItem.binopL .eq v2'] (Exp.substMap vs.snd e1') := rfl
  rw [hbL, hbL']
  iapply (refines_bind [EctxItem.binopL .eq v2] [EctxItem.binopL .eq v2']) $$ IH1'
  iintro %v1 %v1' #Hv1
  -- Now we have v1, v2 (LHS), v1', v2' (RHS), all related at τ.
  -- Use unboxed_type_eq to get pure: v1 = v2 ↔ v1' = v2'.
  ihave Heq : iprop(|={⊤}=> ⌜v1 = v2 ↔ v1' = v2'⌝) $$ [Hv1 Hv2]
  · ihave Heq' := unboxed_type_eq HUnboxed (w2 := v2') $$ Hv1
    iapply Heq' $$ Hv2
  -- Extract literal shapes via the helper.
  ihave Hsh1 := unboxed_type_lit_shape HUnboxed (v' := v1') $$ Hv1
  ihave Hsh2 := unboxed_type_lit_shape HUnboxed (v' := v2') $$ Hv2
  icases Hsh1 with ⟨%l1, %l1', %hv1eq, %hv1'eq⟩
  icases Hsh2 with ⟨%l2, %l2', %hv2eq, %hv2'eq⟩
  -- Reshape goal: ectx fills become bare binops, then substitute lit forms.
  have hL : Ectx.fill [EctxItem.binopL .eq v2] v1.1 = .binop .eq v1.1 v2.1 := rfl
  have hR : Ectx.fill [EctxItem.binopL .eq v2'] v1'.1 = .binop .eq v1'.1 v2'.1 := rfl
  rw [hL, hR, hv1eq, hv2eq, hv1'eq, hv2'eq]
  -- Now extract pure Heq via imod (refines absorbs fupd via ElimModal).
  imod Heq with %heqIff
  -- Compute hdec at Lean level before re-entering iris-heavy section.
  -- Two values holding literals are equal exactly when the literals are.
  have hval : ∀ {w w' : Val rT} {m m' : BaseLit rT}, w.1 = .lit m → w'.1 = .lit m' →
      (w = w' ↔ m = m') := by
    refine fun hw hw' => ⟨fun h => ?_, fun h => Val.ext (by rw [hw, hw', h])⟩
    have hp := congrArg Val.fst h
    rw [hw, hw'] at hp
    exact Exp.lit.inj hp
  have hdec : decide (l1 = l2) = decide (l1' = l2') :=
    decide_eq_decide.mpr ((hval hv1eq hv2eq).symm.trans (heqIff.trans (hval hv1'eq hv2'eq)))
  -- Goal: refines ⊤ (.binop .eq #l1 #l2) (.binop .eq #l1' #l2') lrel_bool.
  -- β-step both sides via pureExec_binop_discrete.
  have hφ_l : (Exp.lit l1).isValue ∧ (Exp.lit l2).isValue ∧
      BinOp.eval .eq (.lit l1) (.lit l2) = some pl(#(.bool (decide (l1 = l2)))) :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  have hφ_r : (Exp.lit l1').isValue ∧ (Exp.lit l2').isValue ∧
      BinOp.eval .eq (.lit l1') (.lit l2') = some pl(#(.bool (decide (l1' = l2')))) :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  rw [Ectx.eq_fill_nil (Exp.binop .eq (.lit l1) (.lit l2)),
      Ectx.eq_fill_nil (Exp.binop .eq (.lit l1') (.lit l2'))]
  iapply (refines_pure_l hφ_l)
  inext
  iapply (refines_pure_r hφ_r)
  iapply refines_ret
    (e1 := Ectx.fill [] (pl(#(.bool (decide (l1 = l2))))))
    (e2 := Ectx.fill [] (pl(#(.bool (decide (l1' = l2'))))))
    (v1 := .bool (decide (l1 = l2)))
    (v2 := .bool (decide (l1' = l2')))
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  rw [interp_bool, hdec]
  iapply (lrel_bool_lit _)

/-- The three literal-pattern cases of `pat_match_related`: both sides carry the same
literal `l'`, so `Pat.lit l` takes the same branch on both, and the bindings are `()`. -/
private theorem pat_match_lit {Δ : TyEnv rT GF} {l l' : BaseLit rT} {v v' : Val rT}
    (hv : v = .ofBaseLit l') (hv' : v' = .ofBaseLit l')
    (hll : l = l' ∨ ¬ (l == l') = true) :
    ⊢@{IProp GF} (∃ (b b' : Val rT), ⌜Pat.tryMatch (.lit l) v.1 = some b.1 ∧
        Pat.tryMatch (.lit l) v'.1 = some b'.1⌝ ∗ (interp Ty.unit Δ).car b b') ∨
      ⌜Pat.tryMatch (.lit l) v.1 = none ∧ Pat.tryMatch (.lit l) v'.1 = none⌝ := by
  subst hv hv'
  rcases hll with rfl | hne
  · ileft
    iexists (.unit : Val _), (.unit : Val _)
    isplitr
    · ipureintro; exact ⟨Pat.tryMatch_lit_eq l, Pat.tryMatch_lit_eq l⟩
    rw [interp_unit]
    iapply lrel_unit_lit
  · iright
    ipureintro
    exact ⟨Pat.tryMatch_lit_ne hne, Pat.tryMatch_lit_ne hne⟩

/-- **Pattern-match agreement**: if `v ~ v'` at `interp τs Δ` and `PatTyped τs p τb`,
then `tryMatch p v.1` and `tryMatch p v'.1` produce related outcomes — either
both succeed with related bindings, or both fail. The shape used here exposes
the bindings as `Val`s (with their `IsVal` witnesses) since the operational
step requires values. -/
theorem pat_match_related {Δ : TyEnv rT GF} {τs τb : Ty} {p : Pat rT}
    (Hpat : PatTyped τs p τb) (v v' : Val rT) :
    (interp τs Δ).car v v' ⊢@{IProp GF}
      (∃ (b b' : Val rT), ⌜Pat.tryMatch p v.1 = some b.1 ∧
                                Pat.tryMatch p v'.1 = some b'.1⌝ ∗
            (interp τb Δ).car b b') ∨
        ⌜Pat.tryMatch p v.1 = none ∧ Pat.tryMatch p v'.1 = none⌝ := by
  induction Hpat generalizing v v' with
  | @wildcard τ =>
    -- tryMatch wildcard v = some v.1; bindings = v.1 (which is a Val).
    iintro Hvv
    ileft
    iexists v, v'
    isplitr
    · ipureintro
      simp [Pat.tryMatch]
    iexact Hvv
  | @lit_int z =>
    -- v ~ v' at lrel_int means v = v' = .int n for the same n.
    rw [interp_int]
    iintro Hv
    ihave ⟨%n, %h⟩ := lrel_int_unfold v v' $$ Hv
    have hll : (BaseLit.int z : BaseLit rT) = .int n ∨
        ¬ ((BaseLit.int z : BaseLit rT) == .int n) = true :=
      if hzn : z = n then .inl (by rw [hzn]) else
        .inr (show ¬ (Int.decEq z n).decide = true from fun hd => hzn (of_decide_eq_true hd))
    iapply (pat_match_lit h.1 h.2 hll)
  | @lit_bool b =>
    rw [interp_bool]
    iintro Hv
    ihave ⟨%b', %h⟩ := lrel_bool_unfold v v' $$ Hv
    have hll : (BaseLit.bool b : BaseLit rT) = .bool b' ∨
        ¬ ((BaseLit.bool b : BaseLit rT) == .bool b') = true :=
      if hbb : b = b' then .inl (by rw [hbb]) else
        .inr (show ¬ (Bool.decEq b b').decide = true from fun hd => hbb (of_decide_eq_true hd))
    iapply (pat_match_lit h.1 h.2 hll)
  | lit_unit =>
    show iprop(⌜v = .unit ∧ v' = .unit⌝) ⊢ _
    iintro %h
    iapply (pat_match_lit (l := .unit) h.1 h.2 (.inl rfl))
  | @pair τ1 τ2 p1 p2 b1 b2 Hpat1 Hpat2 ih1 ih2 =>
    rw [interp_prod]
    iintro Hv
    ihave ⟨%a1, %a2, %c1, %c2, %hv1, %hv2, HA, HC⟩ :=
      lrel_prod_unfold (interp τ1 Δ) (interp τ2 Δ) v v' $$ Hv
    -- Use IH on a1, a2 at τ1 (with pattern p1).
    ihave Hresa := ih1 a1 a2 $$ HA
    ihave Hresb := ih2 c1 c2 $$ HC
    -- Case-split on the four outcomes (some/some, some/none, none/some, none/none).
    icases Hresa with (⟨%ba, %ba', %hra, HBa⟩ | %hna)
    · icases Hresb with (⟨%bb, %bb', %hrb, HBb⟩ | %hnb)
      · -- Both succeed: bindings are .pair ba bb / .pair ba' bb'.
        ileft
        iexists ⟨.pair ba.1 bb.1, IsVal.pair ba.2 bb.2, (IsVal.pair ba.2 bb.2).lc⟩,
                ⟨.pair ba'.1 bb'.1, IsVal.pair ba'.2 bb'.2, (IsVal.pair ba'.2 bb'.2).lc⟩
        isplitr
        · ipureintro
          simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hrb.1, hrb.2]
        -- Need (interp (.prod b1 b2) Δ).car ⟨.pair ba bb, _⟩ ⟨.pair ba' bb', _⟩.
        rw [interp_prod]
        unfold lrel_prod
        iexists ba, ba', bb, bb'
        isplitr; · ipureintro; rfl
        isplitr; · ipureintro; rfl
        iframe HBa
        iexact HBb
      · -- p1 succeeds but p2 fails. Combined match fails.
        iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hnb.1, hnb.2]
    · -- p1 fails. Combined match fails (regardless of p2).
      iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2, hna.1, hna.2]
  | @inl τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    ihave ⟨%w1, %w2, Hcase⟩ := lrel_sum_unfold (interp τ1 Δ) (interp τ2 Δ) v v' $$ Hv
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · -- v1 = inl w1, v2 = inl w2: tryMatch (.inl p) (.inl wi) = tryMatch p wi.
      icases ih w1 w2 $$ HA with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro
          simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]
    · -- v1 = inr w1, v2 = inr w2: tryMatch (.inl p) (.inr w) = none.
      iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
  | @inr τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    ihave ⟨%w1, %w2, Hcase⟩ := lrel_sum_unfold (interp τ1 Δ) (interp τ2 Δ) v v' $$ Hv
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
    · ihave Hres := ih w1 w2 $$ HB
      icases Hres with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro
          simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]

theorem bin_log_related_scrut (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT}
    {p : Pat rT} {τs τb : Ty} (Hpat : PatTyped τs p τb) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τs) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.scrut e p) (.scrut e' p) (.sum τb .unit) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_scrut, Exp.substMap_scrut]
  -- Bind e, e' to get values v, v' at interp τs Δ.
  rw [← Ectx.fill_scrut p, ← Ectx.fill_scrut p]
  iapply (refines_bind [EctxItem.scrut p] [EctxItem.scrut p]
    (A := interp τs Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' #Hv
  -- Goal: refines ⊤ (.scrut v.1 p) (.scrut v'.1 p) (interp (.sum τb .unit) Δ).
  -- Case-split on pat_match_related.
  ihave Hmatch := pat_match_related Hpat v v' $$ Hv
  rw [show Ectx.fill [EctxItem.scrut p] v.1 = Ectx.fill ([] : Ectx rT) (.scrut v.1 p) from rfl,
      show Ectx.fill [EctxItem.scrut p] v'.1 = Ectx.fill ([] : Ectx rT) (.scrut v'.1 p) from rfl]
  icases Hmatch with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
  · -- Both match: step to .inl bb / .inl bb'.
    iapply (refines_pure_l (Hex := pureExec_scrut_some) ⟨v.2.toIsValue, hr.1⟩)
    inext
    iapply (refines_pure_r (Hex := pureExec_scrut_some) ⟨v'.2.toIsValue, hr.2⟩)
    iapply refines_ret
      (e1 := Ectx.fill [] (Exp.inl bb.1))
      (e2 := Ectx.fill [] (Exp.inl bb'.1))
      (v1 := ⟨.inl bb.1, IsVal.inl bb.2, (IsVal.inl bb.2).lc⟩)
      (v2 := ⟨.inl bb'.1, IsVal.inl bb'.2, (IsVal.inl bb'.2).lc⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists bb, bb'
    ileft
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iexact Hbnd
  · -- Both fail: step to .inr ()
    iapply (refines_pure_l (Hex := pureExec_scrut_none) ⟨v.2.toIsValue, hn.1⟩)
    inext
    iapply (refines_pure_r (Hex := pureExec_scrut_none) ⟨v'.2.toIsValue, hn.2⟩)
    iapply refines_ret
      (e1 := Ectx.fill [] (Exp.inr pl(#(.unit))))
      (e2 := Ectx.fill [] (Exp.inr pl(#(.unit))))
      (v1 := ⟨.inr pl(#(.unit)), IsVal.inr IsVal.lit, (IsVal.inr IsVal.lit).lc⟩)
      (v2 := ⟨.inr pl(#(.unit)), IsVal.inr IsVal.lit, (IsVal.inr IsVal.lit).lc⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists (.unit : Val _), (.unit : Val _)
    iright
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iapply lrel_unit_lit

/-! ## The fundamental theorem

Every well-typed expression is logically related to itself. -/

/-- If `Γtc x = some τ` then there's a corresponding entry in `Γrc`. -/
theorem TctxRelated.lookup_isSome {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) {x : Var} (hx : (Γtc x).isSome) :
    (Γrc.lookup x).isSome := by
  have heq := HCtx x
  rcases hΓ : Γtc x with _ | τ
  · rw [hΓ] at hx; exact (Bool.false_ne_true hx).elim
  · rw [hΓ] at heq; rw [← heq]; rfl

/-- The relational context entry at `x` is `interp τ Δ` when `Γtc x = some τ`. -/
theorem TctxRelated.lookup_some {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) {x : Var} {τ : Ty} (hx : Γtc x = some τ) :
    Γrc.lookup x = some (interp τ Δ) := by
  have heq := HCtx x
  rw [hx] at heq
  exact heq.symm

/-- The TctxRelated relation is preserved by type-environment shifting:
shifting all types by 1 and consing a fresh `A` gives the same relational
context (after Leibniz from `interp_ren`). -/
theorem TctxRelated.shift {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) (A : lrel rT GF) :
    TctxRelated (TyEnv.cons A Δ) Γtc.shift Γrc := by
  intro x
  have heq := HCtx x
  unfold Tctx.shift
  cases hΓ : Γtc x with
  | none => rw [hΓ] at heq; rw [← heq]; rfl
  | some τ =>
    rw [hΓ] at heq
    have hint : interp τ.shift (TyEnv.cons A Δ) = interp τ Δ :=
      interp_ren τ A Δ
    simp [hint]; exact heq

/-- The TctxRelated relation extends to context insertion at a fresh atom. -/
theorem TctxRelated.insert {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) (x : Var) (τ : Ty)
    (hfresh : Γrc.lookup x = none) :
    TctxRelated Δ (Γtc.insert x τ) ((x, interp τ Δ) :: Γrc) := by
  intro y
  unfold Tctx.insert RelCtx.lookup
  have heq := HCtx y
  by_cases hxy : y = x
  · subst hxy
    have hΓy_none : Γtc y = none := by
      rw [hfresh] at heq
      cases h : Γtc y with
      | none => rfl
      | some τ' => rw [h] at heq; simp at heq
    simp [hfresh]
  · rw [if_neg hxy]
    cases hRc : Γrc.lookup y with
    | none =>
      rw [hRc] at heq
      cases hΓy : Γtc y with
      | none =>
        simp [if_neg hxy]
      | some τ' => rw [hΓy] at heq; simp at heq
    | some A =>
      rw [hRc] at heq
      cases hΓy : Γtc y with
      | none => rw [hΓy] at heq; simp at heq
      | some τ' =>
        rw [hΓy] at heq; simp at heq
        show some (interp τ' Δ) = some A
        rw [heq]

omit [ProbLangℝ rT] in
/-- Helper: an `isSome` lookup in a `RelCtx` gives a list-membership witness. -/
theorem RelCtx.exists_mem_of_lookup_isSome {Γ : RelCtx rT GF} {x : Var}
    (h : (Γ.lookup x).isSome) : ∃ p ∈ Γ, p.1 = x := by
  induction Γ with
  | nil => simp [RelCtx.lookup] at h
  | cons q rest ih =>
    simp only [RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest x with
    | some _ =>
      have hsome : (RelCtx.lookup rest x).isSome := by rw [hr]; rfl
      obtain ⟨p, hpmem, hpeq⟩ := ih hsome
      exact ⟨p, List.mem_cons_of_mem _ hpmem, hpeq⟩
    | none =>
      rw [hr] at h
      by_cases hxq : x = q.1
      · exact ⟨q, List.mem_cons_self, hxq.symm⟩
      · rw [if_neg hxq] at h; simp at h

/-- Helper: `e.fv ⊆ (Γrc.map ·.1).toFinset` follows from `Typed Γtc e τ` + `TctxRelated`. -/
theorem fv_subset_relCtxDom {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset := by
  intro x hx
  have hRcSome : (Γrc.lookup x).isSome := HCtx.lookup_isSome (Hty.fvSubset x hx)
  obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hRcSome
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨p, hpmem, hpeq⟩

omit [ProbLangℝ rT] in
/-- Helper: an atom outside `Γ`'s domain is not bound by `Γ`. -/
private theorem RelCtx.lookup_eq_none {Γ : RelCtx rT GF} {x : Var}
    (h : x ∉ (Γ.map (·.1)).toFinset) : Γ.lookup x = none := by
  cases hRc : Γ.lookup x with
  | none => rfl
  | some _ =>
    obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome (by rw [hRc]; rfl)
    exact absurd (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hpmem, hpeq⟩)) h

/-- Helper: a cofinite typing derivation for a binder's body pins the body's free
variables inside `Γrc`. Probe the derivation at one atom fresh for `L`, `Γrc` and the
variable at hand; that atom is the only one the extended context could have added. -/
private theorem fv_subset_of_cofinite {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Γtc Γrc) {L : Finset Var} {e : Exp rT} {τ1 τ2 : Ty}
    (Hbody : ∀ x ∉ L, Typed (Γtc.insert x τ1) (Exp.open' e (.fvar x)) τ2) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset := by
  intro z hz
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (L ∪ (Γrc.map (·.1)).toFinset ∪ {z})
  have hyL : y ∉ L := fun h =>
    hy (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hyRc : y ∉ (Γrc.map (·.1)).toFinset := fun h =>
    hy (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hzy : z ≠ y := fun h =>
    hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm))
  have hzdom := fv_subset_relCtxDom (HCtx.insert y τ1 (RelCtx.lookup_eq_none hyRc))
    (Hbody y hyL) (Exp.fv_subset_open e y hz)
  simp only [List.mem_toFinset, List.mem_map] at hzdom ⊢
  obtain ⟨p, hpmem, hpeq⟩ := hzdom
  rcases List.mem_cons.mp hpmem with rfl | hmem
  · -- p = (y, _), so hpeq : y = z contradicts hzy.
    exact (hzy hpeq.symm).elim
  · exact ⟨p, hmem, hpeq⟩

/-- **Fundamental theorem of the logical relation.** Induction on `Typed`,
dispatching each case to its `bin_log_related_*` lemma. The binder cases
(`lam`, `fix`, `tunpack`) recurse on the body's typing under an extended
context; the polymorphic cases (`tlam`, `tapp`) relate the shifted typing
context to a re-interpreted relational one via `TctxRelated.shift` and
`interp_ren`. -/
theorem fundamental {Γtc : Tctx} {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ)
    (Δ : TyEnv rT GF)
    (Γrc : RelCtx rT GF)
    (HCtx : TctxRelated Δ Γtc Γrc) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e e τ := by
  induction Hty generalizing Δ Γrc with
  | @fvar _ x τ hx => exact bin_log_related_var Δ Γrc x τ (HCtx.lookup_some hx)
  | @lit_int _ n => exact bin_log_related_lit Γrc _ (lrel_int_lit n)
  | @lit_real _ r => exact bin_log_related_lit Γrc _ (lrel_real_lit r)
  | @lit_bool _ b => exact bin_log_related_lit Γrc _ (lrel_bool_lit b)
  | lit_unit => exact bin_log_related_lit Γrc _ lrel_unit_lit
  | «urand» => exact bin_log_related_urand Δ Γrc
  | unop_real _ Hres ih =>
    iintro; iapply (bin_log_related_real_unop Δ Γrc _ Hres) $$ %(ih Δ Γrc HCtx)
  | unop_int _ Hres ih =>
    iintro; iapply (bin_log_related_int_unop Δ Γrc _ Hres) $$ %(ih Δ Γrc HCtx)
  | unop_bool _ Hres ih =>
    iintro; iapply (bin_log_related_bool_unop Δ Γrc _ Hres) $$ %(ih Δ Γrc HCtx)
  | binop_real _ _ Hres ih1 ih2 =>
    iintro
    iapply (bin_log_related_real_binop Δ Γrc _ Hres) $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_int _ _ Hres ih1 ih2 =>
    iintro
    iapply (bin_log_related_int_binop Δ Γrc _ Hres) $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_bool _ _ Hres ih1 ih2 =>
    iintro
    iapply (bin_log_related_bool_binop Δ Γrc _ Hres) $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | unboxed_eq HUnboxed _ _ ih1 ih2 =>
    iintro
    iapply (bin_log_related_unboxed_eq Δ Γrc HUnboxed) $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | pair _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_pair $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | fst _ ih => iintro; iapply (bin_log_related_fst Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | snd _ ih => iintro; iapply (bin_log_related_snd Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | inl _ ih => iintro; iapply (bin_log_related_injl Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | inr _ ih => iintro; iapply (bin_log_related_injr Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | «case» _ _ _ ih0 ih1 ih2 =>
    iintro
    iapply bin_log_related_case $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | cond _ _ _ ih0 ih1 ih2 =>
    iintro
    iapply bin_log_related_if $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | app _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_app $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc _ ih => iintro; iapply (bin_log_related_alloc Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | load _ ih => iintro; iapply (bin_log_related_load Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | store _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_store $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc_tape _ ih => iintro; iapply bin_log_related_alloctape $$ %(ih Δ Γrc HCtx)
  | rand _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_rand_tape $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | rand_unit _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_rand_unit $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | «scrut» _ Hpat ih =>
    iintro; iapply (bin_log_related_scrut Δ Γrc Hpat) $$ %(ih Δ Γrc HCtx)
  | tfold _ ih => iintro; iapply (bin_log_related_fold Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | tunfold _ ih => iintro; iapply (bin_log_related_unfold Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | tapp _ ih => iintro; iapply (bin_log_related_tapp Δ Γrc) $$ %(ih Δ Γrc HCtx)
  | tpack _ ih => iintro; iapply (bin_log_related_pack Δ Γrc) $$ %(ih Δ Γrc HCtx)
  -- Recursive binder cases (lam, fix): instantiate the cofinite quantifier at atoms
  -- fresh for `L`, `dom Γrc` and `e.fv`, so both freshness side conditions hold at once.
  | @lam L Γtc' e τ1 τ2 Hbody ih =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset ∪ e.fv
    have hxL : ∀ x ∉ L', x ∉ L := fun _ hx h =>
      hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxRc : ∀ x ∉ L', Γrc.lookup x = none := fun _ hx =>
      RelCtx.lookup_eq_none fun h => hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ L', (Exp.open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (hxL x hx)).isLocallyClosed
    apply bin_log_related_lam Δ Γrc L' he_lc he_lc he_fv he_fv
    exact fun x hx => ih x (hxL x hx) Δ _ (HCtx.insert x τ1 (hxRc x hx))
  | @«fix» L Γtc' e τ1 τ2 Hbody ih =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset ∪ e.fv
    have hxL : ∀ x ∉ L', x ∉ L := fun _ hx h =>
      hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxRc : ∀ x ∉ L', Γrc.lookup x = none := fun _ hx =>
      RelCtx.lookup_eq_none fun h => hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ L', (Exp.open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (hxL x hx)).isLocallyClosed
    apply bin_log_related_fix Δ Γrc L' he_lc he_lc he_fv he_fv
    exact fun x hx => ih x (hxL x hx) Δ _ (HCtx.insert x (.arrow τ1 τ2) (hxRc x hx))
  -- Polymorphic binder cases (tlam, tunpack). Closedness is now built into
  -- `lrel`'s structure (option D), so the IH works for any `A`.
  | @tlam Γtc' e τ Hbody ih =>
    have hLC : e.IsLocallyClosed := Hbody.isLocallyClosed
    have he_fv : e.fv ⊆ (Γrc.map (·.1)).toFinset :=
      fv_subset_relCtxDom (HCtx.shift default) Hbody
    apply bin_log_related_tlam Δ Γrc hLC hLC he_fv he_fv
    intro A
    iintro
    imodintro
    iapply (ih (TyEnv.cons A Δ) Γrc (HCtx.shift A))
  | @tunpack L Γtc' e1 e2 τ τ2 Hty1 Hbody2 ih1 ih2 =>
    -- Augment L with Γrc.dom for freshness in the inner Γrc.
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset
    have hxL : ∀ x ∉ L', x ∉ L := fun _ hx h => hx (Finset.mem_union_left _ h)
    have hxRc : ∀ x ∉ L', Γrc.lookup x = none := fun _ hx =>
      RelCtx.lookup_eq_none fun h => hx (Finset.mem_union_right _ h)
    have HIH2 : ∀ A : lrel rT GF, ∀ x ∉ L',
        ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ)
          ((x, interp τ (TyEnv.cons A Δ)) :: Γrc)
          (Exp.open' e2 (.fvar x)) (Exp.open' e2 (.fvar x)) τ2.shift := fun A x hx =>
      ih2 x (hxL x hx) (TyEnv.cons A Δ) _ ((HCtx.shift A).insert x τ (hxRc x hx))
    -- Body closedness from its cofinite typing derivation, as in the `lam` case.
    have he2_lc : ∀ x ∉ L', (Exp.open' e2 (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody2 x (hxL x hx)).isLocallyClosed
    exact bin_log_related_unpack Δ Γrc L' (ih1 Δ Γrc HCtx) he2_lc he2_lc HIH2

/-- Closed specialization: `∅ ⊢ₜ e : τ → ⊢ REL e << e : interp τ Δ`. -/
theorem refines_typed (Δ : TyEnv rT GF) {e : Exp rT} {τ : Ty}
    (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines (⊤ : CoPset) e e (interp τ Δ) := by
  have HRel : TctxRelated Δ Tctx.empty ([] : RelCtx rT GF) := by
    intro x; simp [Tctx.empty, RelCtx.lookup]
  have Hfund := fundamental Hty Δ [] HRel
  unfold bin_log_related_ty bin_log_related at Hfund
  -- `substMap [] e = e`, so the goal is def-eq to `Hfund` specialized at `vs := []`.
  show ⊢@{IProp GF} refines (⊤ : CoPset)
    (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e)
    (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e) (interp τ Δ)
  ihave Hf := Hfund
  iapply Hf $$ %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

end Fundamental

end ProbLang
