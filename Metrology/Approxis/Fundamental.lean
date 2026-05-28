module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.Model
public import Metrology.Approxis.Compatibility
public import Metrology.Approxis.AppRelRules
public import Metrology.Approxis.RelTactics
public import Metrology.Approxis.Interp

@[expose] public section

/-! # Fundamental Theorem

Fundamental theorem of the logical relation: well-typed terms are related to themselves, plus per-constructor `bin_log_related_*` compatibility lemmas. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

open Cslib Exp

section Fundamental
set_option linter.unusedSectionVars false
variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-! ## Tctx → RelCtx lifting -/

/-- `TctxRelated Δ Γtc Γrc` asserts that the relational context `Γrc` is the
pointwise lift of the syntactic context `Γtc` through `interp · Δ`. -/
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp τ Δ) = Γrc.lookup x

/-! ## Compatibility lemmas -/

theorem bin_log_related_var (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp τ Δ)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
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

theorem bin_log_related_pair (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ1) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ2 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.pair e1 e2) (.pair e1' e2')
          (.prod τ1 τ2)) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_pair, Exp.substMap_pair, interp_prod]
  iapply (refines_pair (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH1']
  · iexact IH1'
  iexact IH2'

theorem bin_log_related_fst (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.fst e) (.fst e') τ1 := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_fst, Exp.substMap_fst]
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_prod (interp τ1 Δ) (interp τ2 Δ))) $$ [IH']
  · rw [← interp_prod]; iexact IH'
  iapply (refines_fst (A := interp τ1 Δ) (B := interp τ2 Δ))
  iexact IH''

theorem bin_log_related_snd (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.prod τ1 τ2)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.snd e) (.snd e') τ2 := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_snd, Exp.substMap_snd]
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_prod (interp τ1 Δ) (interp τ2 Δ))) $$ [IH']
  · rw [← interp_prod]; iexact IH'
  iapply (refines_snd (A := interp τ1 Δ) (B := interp τ2 Δ))
  iexact IH''

theorem bin_log_related_injl (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ1) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_inl, Exp.substMap_inl, interp_sum]
  iapply (refines_injl (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_injr (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ2) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.inr e) (.inr e') (.sum τ1 τ2) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_inr, Exp.substMap_inr, interp_sum]
  iapply (refines_injr (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_case (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ1 τ2 τ3 : Ty} :
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
  ihave IH0'' : iprop(refines ⊤ (Exp.substMap vs.fst e0) (Exp.substMap vs.snd e0')
      (lrel_sum (interp τ1 Δ) (interp τ2 Δ))) $$ [IH0']
  · rw [← interp_sum]; iexact IH0'
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_arr (interp τ1 Δ) (interp τ3 Δ))) $$ [IH1']
  · rw [← interp_arrow]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      (lrel_arr (interp τ2 Δ) (interp τ3 Δ))) $$ [IH2']
  · rw [← interp_arrow]; iexact IH2'
  ihave HRcaseApp := refines_case (A := interp τ1 Δ) (B := interp τ2 Δ) (C := interp τ3 Δ)
    (e0 := Exp.substMap vs.fst e0) (e0' := Exp.substMap vs.snd e0')
    (e1 := Exp.substMap vs.fst e1) (e1' := Exp.substMap vs.snd e1')
    (e2 := Exp.substMap vs.fst e2) (e2' := Exp.substMap vs.snd e2') $$ [IH0'']
  · iexact IH0''
  ihave HRcaseApp1 := HRcaseApp $$ [IH1'']
  · iexact IH1''
  iapply HRcaseApp1
  iexact IH2''

theorem bin_log_related_if (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ : Ty} :
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
  ihave IH0'' : iprop(refines ⊤ (Exp.substMap vs.fst e0) (Exp.substMap vs.snd e0')
      lrel_bool) $$ [IH0']
  · rw [← interp_bool]; iexact IH0'
  ihave HRifApplied := refines_if (A := interp τ Δ) (e0 := Exp.substMap vs.fst e0)
    (e0' := Exp.substMap vs.snd e0') (e1 := Exp.substMap vs.fst e1)
    (e1' := Exp.substMap vs.snd e1') (e2 := Exp.substMap vs.fst e2)
    (e2' := Exp.substMap vs.snd e2') $$ [IH0'']
  · iexact IH0''
  ihave HRif1 := HRifApplied $$ [IH1']
  · iexact IH1'
  iapply HRif1
  iexact IH2'

theorem bin_log_related_app (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ1 τ2 : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.arrow τ1 τ2)) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ1 -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.app e1 e2) (.app e1' e2') τ2) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_app, Exp.substMap_app]
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_arr (interp τ1 Δ) (interp τ2 Δ))) $$ [IH1']
  · rw [← interp_arrow]; iexact IH1'
  iapply (refines_app (A := interp τ1 Δ) (B := interp τ2 Δ)) $$ [IH1'']
  · iexact IH1''
  iexact IH2'

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
  ihave %Hvs_closed := env_ltyped2_allClosed Γ vs $$ Hvs
  have hvsfst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).1
  have hvssnd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).2
  have hlam_lc : (Exp.lam (Exp.substMap vs.fst e)).IsLocallyClosed := by
    refine Exp.IsLocallyClosed.lam (L ∪ (vs.map (·.1)).toFinset) _ ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
    have hyNotDom : y ∉ (vs.map (·.1)).toFinset :=
      fun h => hy (Finset.mem_union_right _ h)
    have hyVsFst : SubstMap.lookup vs.fst y = none := by
      rw [ValSubstMap.fst_lookup]
      have : ValSubstMap.lookup vs y = none := by
        have aux : ∀ (ys : ValSubstMap rT), y ∉ (ys.map (·.1)).toFinset →
            ValSubstMap.lookup ys y = none := by
          intro ys
          induction ys with
          | nil => intro _; rfl
          | cons p rest ih =>
            obtain ⟨z, _⟩ := p
            intro hyNot
            simp only [List.map_cons, List.toFinset_cons,
              Finset.mem_insert, not_or] at hyNot
            simp only [ValSubstMap.lookup, ih hyNot.2]
            simp [hyNot.1]
        exact aux vs hyNotDom
      rw [this]; rfl
    have hbridge : Exp.substMap vs.fst (Exp.open' e (.fvar y)) =
        Exp.open' (Exp.substMap vs.fst e) (.fvar y) := by
      rw [Exp.substMap_open _ _ _ hvsfst_closed]
      rw [Exp.substMap_fvar_lookup_none hyVsFst]
    rw [← hbridge]
    exact Exp.substMap_lc hvsfst_closed (he_lc y hyL)
  have hlam'_lc : (Exp.lam (Exp.substMap vs.snd e')).IsLocallyClosed := by
    refine Exp.IsLocallyClosed.lam (L ∪ (vs.map (·.1)).toFinset) _ ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
    have hyNotDom : y ∉ (vs.map (·.1)).toFinset :=
      fun h => hy (Finset.mem_union_right _ h)
    have hyVsSnd : SubstMap.lookup vs.snd y = none := by
      rw [ValSubstMap.snd_lookup]
      have : ValSubstMap.lookup vs y = none := by
        have aux : ∀ (ys : ValSubstMap rT), y ∉ (ys.map (·.1)).toFinset →
            ValSubstMap.lookup ys y = none := by
          intro ys
          induction ys with
          | nil => intro _; rfl
          | cons p rest ih =>
            obtain ⟨z, _⟩ := p
            intro hyNot
            simp only [List.map_cons, List.toFinset_cons,
              Finset.mem_insert, not_or] at hyNot
            simp only [ValSubstMap.lookup, ih hyNot.2]
            simp [hyNot.1]
        exact aux vs hyNotDom
      rw [this]; rfl
    have hbridge : Exp.substMap vs.snd (Exp.open' e' (.fvar y)) =
        Exp.open' (Exp.substMap vs.snd e') (.fvar y) := by
      rw [Exp.substMap_open _ _ _ hvssnd_closed]
      rw [Exp.substMap_fvar_lookup_none hyVsSnd]
    rw [← hbridge]
    exact Exp.substMap_lc hvssnd_closed (he'_lc y hyL)
  have hdom_eq_fst : (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.1.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have hdom_eq_snd : (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.2.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  have hΓdomVs : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨p, hpmem, hpeq⟩ := hy
    subst hpeq
    have hyΓlookup : (Γ.lookup p.1).isSome := RelCtx.lookup_isSome_of_mem hpmem
    have hyVsLookup : (vs.lookup p.1).isSome := (hDom p.1).mp hyΓlookup
    obtain ⟨q, hqmem, hqeq⟩ := ValSubstMap.mem_of_lookup_isSome hyVsLookup
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hqmem, hqeq⟩
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [hdom_eq_fst]
    exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [hdom_eq_snd]
    exact he'_fv.trans hΓdomVs
  have hlam_closed : (Exp.lam (Exp.substMap vs.fst e)).isClosedEmpty ∧
      (Exp.lam (Exp.substMap vs.snd e')).isClosedEmpty := by
    refine ⟨⟨hlam_lc, ?_⟩, ⟨hlam'_lc, ?_⟩⟩
    · simp only [Exp.fv]
      exact Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst
    · simp only [Exp.fv]
      exact Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd
  iapply (refines_arrow_val
    (v := ⟨Exp.lam (Exp.substMap vs.fst e), IsVal.lam⟩)
    (v' := ⟨Exp.lam (Exp.substMap vs.snd e'), IsVal.lam⟩)
    (hv := hlam_closed))
  iintro !> %v1 %v2 #HA
  ihave %hv1v2_closed : iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ : IProp GF) $$ [HA]
  · iapply (interp_closed (Δ := Δ) τ1 v1 v2)
    iexact HA
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists
    (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  have hxL : x ∉ L :=
    fun h => hx (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hxFvE : x ∉ e.fv :=
    fun h => hx (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hxFvE' : x ∉ e'.fv :=
    fun h => hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hxNotDom : x ∉ (vs.map (·.1)).toFinset :=
    fun h => hx (Finset.mem_union_right _ h)
  have HbodyAtX := Hbody x hxL
  let vs' : ValSubstMap rT := (x, (v1, v2)) :: vs
  have hv1c : v1.1.isClosed .empty :=
    ⟨hv1v2_closed.1.1, by rw [hv1v2_closed.1.2]; exact Finset.empty_subset _⟩
  have hv2c : v2.1.isClosed .empty :=
    ⟨hv1v2_closed.2.1, by rw [hv1v2_closed.2.2]; exact Finset.empty_subset _⟩
  ihave Hvs' : iprop(env_ltyped2 ((x, interp τ1 Δ) :: Γ) vs') $$ [HA]
  · iapply (env_ltyped2_insert Γ vs x (interp τ1 Δ) v1 v2 hv1c hv2c)
    isplitr [HA]
    · iexact HA
    iexact Hvs
  unfold bin_log_related_ty bin_log_related at HbodyAtX
  ihave HbodyAtX_iris := HbodyAtX
  ihave HbodyApplied : iprop(refines (⊤ : CoPset)
      (Exp.substMap vs'.fst (Exp.open' e (.fvar x)))
      (Exp.substMap vs'.snd (Exp.open' e' (.fvar x)))
      (interp τ2 Δ)) $$ [HbodyAtX_iris Hvs']
  · iapply HbodyAtX_iris
    iexact Hvs'
  have hxDomVs : ValSubstMap.lookup vs x = none := by
    have aux : ∀ (ys : ValSubstMap rT), x ∉ (ys.map (·.1)).toFinset →
        ValSubstMap.lookup ys x = none := by
      intro ys
      induction ys with
      | nil => intro _; rfl
      | cons p rest ih =>
        obtain ⟨y, _⟩ := p
        intro hxNot
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hxNot
        have hxNeY : x ≠ y := hxNot.1
        have hxNotRest : x ∉ (rest.map (·.1)).toFinset := hxNot.2
        simp only [ValSubstMap.lookup]
        rw [ih hxNotRest]
        simp [hxNeY]
    exact aux vs hxNotDom
  have hxDomFst : SubstMap.lookup vs.fst x = none := by
    rw [ValSubstMap.fst_lookup, hxDomVs]; rfl
  have hxDomSnd : SubstMap.lookup vs.snd x = none := by
    rw [ValSubstMap.snd_lookup, hxDomVs]; rfl
  have hv1_lc : v1.1.IsLocallyClosed := hv1v2_closed.1.1
  have hv2_lc : v2.1.IsLocallyClosed := hv1v2_closed.2.1
  have hbridge_fst : Exp.substMap vs'.fst (Exp.open' e (.fvar x)) =
      Exp.open' (Exp.substMap vs.fst e) v1.1 := by
    show Exp.substMap ((x, v1.1) :: vs.fst) (Exp.open' e (.fvar x)) =
        Exp.open' (Exp.substMap vs.fst e) v1.1
    exact Exp.substMap_open_fresh hvsfst_closed hxFvE hxDomFst hv1_lc
  have hbridge_snd : Exp.substMap vs'.snd (Exp.open' e' (.fvar x)) =
      Exp.open' (Exp.substMap vs.snd e') v2.1 := by
    show Exp.substMap ((x, v2.1) :: vs.snd) (Exp.open' e' (.fvar x)) =
        Exp.open' (Exp.substMap vs.snd e') v2.1
    exact Exp.substMap_open_fresh hvssnd_closed hxFvE' hxDomSnd hv2_lc
  ihave HbodyApplied' : iprop(refines (⊤ : CoPset)
      (Exp.open' (Exp.substMap vs.fst e) v1.1)
      (Exp.open' (Exp.substMap vs.snd e') v2.1)
      (interp τ2 Δ)) $$ [HbodyApplied]
  · rw [← hbridge_fst, ← hbridge_snd]; iexact HbodyApplied
  have hL1 : Exp.app (Exp.lam (Exp.substMap vs.fst e)) v1.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.lam (Exp.substMap vs.fst e)) v1.1) := rfl
  have hR1 : Exp.app (Exp.lam (Exp.substMap vs.snd e')) v2.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.lam (Exp.substMap vs.snd e')) v2.1) := rfl
  rw [hL1, hR1]
  iapply (refines_pure_l (K := []) (e := Exp.app (Exp.lam (Exp.substMap vs.fst e)) v1.1)
    (e' := Exp.open' (Exp.substMap vs.fst e) v1.1)
    (Hex := pureExec_app_lam) v1.2.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (e := Exp.app (Exp.lam (Exp.substMap vs.snd e')) v2.1)
    (e' := Exp.open' (Exp.substMap vs.snd e') v2.1)
    (Hex := pureExec_app_lam) v2.2.toIsValue)
  have hf1 : (Ectx.fill ([] : Ectx rT) (Exp.open' (Exp.substMap vs.fst e) v1.1)) =
      Exp.open' (Exp.substMap vs.fst e) v1.1 := rfl
  have hf2 : (Ectx.fill ([] : Ectx rT) (Exp.open' (Exp.substMap vs.snd e') v2.1)) =
      Exp.open' (Exp.substMap vs.snd e') v2.1 := rfl
  rw [hf1, hf2]
  iexact HbodyApplied'

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
  ihave %Hvs_closed := env_ltyped2_allClosed Γ vs $$ Hvs
  have hvsfst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).1
  have hvssnd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).2
  have hfix_lc : (Exp.fix (Exp.substMap vs.fst e)).IsLocallyClosed := by
    refine Exp.IsLocallyClosed.fix (L ∪ (vs.map (·.1)).toFinset) _ ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
    have hyNotDom : y ∉ (vs.map (·.1)).toFinset :=
      fun h => hy (Finset.mem_union_right _ h)
    have hyVsFst : SubstMap.lookup vs.fst y = none := by
      rw [ValSubstMap.fst_lookup]
      have : ValSubstMap.lookup vs y = none := by
        have aux : ∀ (ys : ValSubstMap rT), y ∉ (ys.map (·.1)).toFinset →
            ValSubstMap.lookup ys y = none := by
          intro ys
          induction ys with
          | nil => intro _; rfl
          | cons p rest ih =>
            obtain ⟨z, _⟩ := p
            intro hyNot
            simp only [List.map_cons, List.toFinset_cons,
              Finset.mem_insert, not_or] at hyNot
            simp only [ValSubstMap.lookup, ih hyNot.2]
            simp [hyNot.1]
        exact aux vs hyNotDom
      rw [this]; rfl
    have hbridge : Exp.substMap vs.fst (Exp.open' e (.fvar y)) =
        Exp.open' (Exp.substMap vs.fst e) (.fvar y) := by
      rw [Exp.substMap_open _ _ _ hvsfst_closed]
      rw [Exp.substMap_fvar_lookup_none hyVsFst]
    rw [← hbridge]
    exact Exp.substMap_lc hvsfst_closed (he_lc y hyL)
  have hfix'_lc : (Exp.fix (Exp.substMap vs.snd e')).IsLocallyClosed := by
    refine Exp.IsLocallyClosed.fix (L ∪ (vs.map (·.1)).toFinset) _ ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
    have hyNotDom : y ∉ (vs.map (·.1)).toFinset :=
      fun h => hy (Finset.mem_union_right _ h)
    have hyVsSnd : SubstMap.lookup vs.snd y = none := by
      rw [ValSubstMap.snd_lookup]
      have : ValSubstMap.lookup vs y = none := by
        have aux : ∀ (ys : ValSubstMap rT), y ∉ (ys.map (·.1)).toFinset →
            ValSubstMap.lookup ys y = none := by
          intro ys
          induction ys with
          | nil => intro _; rfl
          | cons p rest ih =>
            obtain ⟨z, _⟩ := p
            intro hyNot
            simp only [List.map_cons, List.toFinset_cons,
              Finset.mem_insert, not_or] at hyNot
            simp only [ValSubstMap.lookup, ih hyNot.2]
            simp [hyNot.1]
        exact aux vs hyNotDom
      rw [this]; rfl
    have hbridge : Exp.substMap vs.snd (Exp.open' e' (.fvar y)) =
        Exp.open' (Exp.substMap vs.snd e') (.fvar y) := by
      rw [Exp.substMap_open _ _ _ hvssnd_closed]
      rw [Exp.substMap_fvar_lookup_none hyVsSnd]
    rw [← hbridge]
    exact Exp.substMap_lc hvssnd_closed (he'_lc y hyL)
  -- Domain agreement.
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  have hΓdomVs : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨p, hpmem, hpeq⟩ := hy
    subst hpeq
    have hyΓlookup : (Γ.lookup p.1).isSome := RelCtx.lookup_isSome_of_mem hpmem
    have hyVsLookup : (vs.lookup p.1).isSome := (hDom p.1).mp hyΓlookup
    obtain ⟨q, hqmem, hqeq⟩ := ValSubstMap.mem_of_lookup_isSome hyVsLookup
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hqmem, hqeq⟩
  have hdom_eq_fst : (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.1.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have hdom_eq_snd : (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.2.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [hdom_eq_fst]; exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [hdom_eq_snd]; exact he'_fv.trans hΓdomVs
  have hfix_closed : (Exp.fix (Exp.substMap vs.fst e)).isClosedEmpty ∧
      (Exp.fix (Exp.substMap vs.snd e')).isClosedEmpty := by
    refine ⟨⟨hfix_lc, ?_⟩, ⟨hfix'_lc, ?_⟩⟩
    · simp only [Exp.fv]
      exact Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst
    · simp only [Exp.fv]
      exact Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd
  obtain ⟨f, hf⟩ := HasFresh.fresh_exists
    (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  have hfL : f ∉ L :=
    fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hfFvE : f ∉ e.fv :=
    fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hfFvE' : f ∉ e'.fv :=
    fun h => hf (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hfNotDom : f ∉ (vs.map (·.1)).toFinset :=
    fun h => hf (Finset.mem_union_right _ h)
  iapply refines_ret
    (e1 := Exp.fix (Exp.substMap vs.fst e)) (e2 := Exp.fix (Exp.substMap vs.snd e'))
    (v1 := ⟨_, IsVal.fix⟩) (v2 := ⟨_, IsVal.fix⟩) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply (loeb_wand (P := (lrel_arr (interp τ1 Δ) (interp τ2 Δ)).car
    ⟨Exp.fix (Exp.substMap vs.fst e), IsVal.fix⟩
    ⟨Exp.fix (Exp.substMap vs.snd e'), IsVal.fix⟩))
  iintro !>
  iintro #IH
  unfold lrel_arr
  isplitr
  · ipure_intro; exact hfix_closed
  iintro !> %v1 %v2 #HA
  have hL1 : Exp.app (Exp.fix (Exp.substMap vs.fst e)) v1.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.fix (Exp.substMap vs.fst e)) v1.1) := rfl
  have hR1 : Exp.app (Exp.fix (Exp.substMap vs.snd e')) v2.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.fix (Exp.substMap vs.snd e')) v2.1) := rfl
  rw [hL1, hR1]
  iapply (refines_pure_l (K := []) (e := Exp.app (Exp.fix (Exp.substMap vs.fst e)) v1.1)
    (e' := Exp.app (Exp.open' (Exp.substMap vs.fst e) (Exp.fix (Exp.substMap vs.fst e))) v1.1)
    (Hex := pureExec_app_fix) v1.2.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (e := Exp.app (Exp.fix (Exp.substMap vs.snd e')) v2.1)
    (e' := Exp.app (Exp.open' (Exp.substMap vs.snd e') (Exp.fix (Exp.substMap vs.snd e'))) v2.1)
    (Hex := pureExec_app_fix) v2.2.toIsValue)
  let fixv : Val rT := ⟨Exp.fix (Exp.substMap vs.fst e), IsVal.fix⟩
  let fixv' : Val rT := ⟨Exp.fix (Exp.substMap vs.snd e'), IsVal.fix⟩
  let vs' : ValSubstMap rT := (f, (fixv, fixv')) :: vs
  have hfixv_c : fixv.1.isClosed .empty :=
    ⟨hfix_closed.1.1, by rw [hfix_closed.1.2]; exact Finset.empty_subset _⟩
  have hfixv'_c : fixv'.1.isClosed .empty :=
    ⟨hfix_closed.2.1, by rw [hfix_closed.2.2]; exact Finset.empty_subset _⟩
  ihave Hvs' : iprop(env_ltyped2 ((f, interp (Ty.arrow τ1 τ2) Δ) :: Γ) vs') $$ [IH]
  · rw [interp_arrow]
    iapply (env_ltyped2_insert Γ vs f (lrel_arr (interp τ1 Δ) (interp τ2 Δ))
      fixv fixv' hfixv_c hfixv'_c)
    isplitr [IH]
    · iapply (lrel_arr_fold (interp τ1 Δ) (interp τ2 Δ) fixv fixv')
      iexact IH
    iexact Hvs
  have HbodyAtF := Hbody f hfL
  unfold bin_log_related_ty bin_log_related at HbodyAtF
  ihave HbodyAtF_iris := HbodyAtF
  ihave HbodyApplied : iprop(refines (⊤ : CoPset)
      (Exp.substMap vs'.fst (Exp.open' e (.fvar f)))
      (Exp.substMap vs'.snd (Exp.open' e' (.fvar f)))
      (interp (.arrow τ1 τ2) Δ)) $$ [HbodyAtF_iris Hvs']
  · iapply HbodyAtF_iris
    iexact Hvs'
  have hxDomVs : ValSubstMap.lookup vs f = none := by
    have aux : ∀ (ys : ValSubstMap rT), f ∉ (ys.map (·.1)).toFinset →
        ValSubstMap.lookup ys f = none := by
      intro ys
      induction ys with
      | nil => intro _; rfl
      | cons p rest ih =>
        obtain ⟨z, _⟩ := p
        intro hxNot
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hxNot
        simp only [ValSubstMap.lookup, ih hxNot.2]
        simp [hxNot.1]
    exact aux vs hfNotDom
  have hxDomFst : SubstMap.lookup vs.fst f = none := by
    rw [ValSubstMap.fst_lookup, hxDomVs]; rfl
  have hxDomSnd : SubstMap.lookup vs.snd f = none := by
    rw [ValSubstMap.snd_lookup, hxDomVs]; rfl
  have hbridge_fst : Exp.substMap vs'.fst (Exp.open' e (.fvar f)) =
      Exp.open' (Exp.substMap vs.fst e) fixv.1 := by
    show Exp.substMap ((f, fixv.1) :: vs.fst) (Exp.open' e (.fvar f)) = _
    exact Exp.substMap_open_fresh hvsfst_closed hfFvE hxDomFst hfix_closed.1.1
  have hbridge_snd : Exp.substMap vs'.snd (Exp.open' e' (.fvar f)) =
      Exp.open' (Exp.substMap vs.snd e') fixv'.1 := by
    show Exp.substMap ((f, fixv'.1) :: vs.snd) (Exp.open' e' (.fvar f)) = _
    exact Exp.substMap_open_fresh hvssnd_closed hfFvE' hxDomSnd hfix_closed.2.1
  ihave HbodyApplied' : iprop(refines (⊤ : CoPset)
      (Exp.open' (Exp.substMap vs.fst e) fixv.1)
      (Exp.open' (Exp.substMap vs.snd e') fixv'.1)
      (interp (.arrow τ1 τ2) Δ)) $$ [HbodyApplied]
  · rw [← hbridge_fst, ← hbridge_snd]; iexact HbodyApplied
  ihave HArgs : iprop(refines ⊤ v1.1 v2.1 (interp τ1 Δ)) $$ [HA]
  · iapply refines_ret (v1 := v1) (v2 := v2) (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HA
  ihave HbodyApplied'' : iprop(refines (⊤ : CoPset)
      (Exp.open' (Exp.substMap vs.fst e) fixv.1)
      (Exp.open' (Exp.substMap vs.snd e') fixv'.1)
      (lrel_arr (interp τ1 Δ) (interp τ2 Δ))) $$ [HbodyApplied']
  · rw [← interp_arrow]; iexact HbodyApplied'
  ihave Hgoal := refines_app $$ [HbodyApplied''] HArgs
  · iexact HbodyApplied''
  have hWrap_L : Ectx.fill ([] : Ectx rT) (Exp.app (Exp.open' (Exp.substMap vs.fst e) fixv.1) v1.1) =
      Exp.app (Exp.open' (Exp.substMap vs.fst e) fixv.1) v1.1 := rfl
  have hWrap_R : Ectx.fill ([] : Ectx rT) (Exp.app (Exp.open' (Exp.substMap vs.snd e') fixv'.1) v2.1) =
      Exp.app (Exp.open' (Exp.substMap vs.snd e') fixv'.1) v2.1 := rfl
  rw [hWrap_L, hWrap_R]
  iexact Hgoal

theorem bin_log_related_alloc (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.alloc e) (.alloc e') (.ref τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_alloc, Exp.substMap_alloc, interp_ref]
  iapply (refines_alloc (A := interp τ Δ)) $$ [IH']
  iexact IH'

theorem bin_log_related_load (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.ref τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.load e) (.load e') τ := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_load, Exp.substMap_load]
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      (lrel_ref (interp τ Δ))) $$ [IH']
  · rw [← interp_ref]; iexact IH'
  iapply (refines_load (A := interp τ Δ)) $$ [IH'']
  iexact IH''

theorem bin_log_related_store (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' (.ref τ)) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.store e1 e2) (.store e1' e2') .unit) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_store, Exp.substMap_store, interp_unit]
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      (lrel_ref (interp τ Δ))) $$ [IH1']
  · rw [← interp_ref]; iexact IH1'
  iapply (refines_store (A := interp τ Δ)) $$ [IH1'']
  · iexact IH1''
  iexact IH2'

theorem bin_log_related_alloctape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' .int) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ (.tape e) (.tape e') .tape := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_tape, Exp.substMap_tape, interp_tape]
  ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
      lrel_int) $$ [IH']
  · rw [← interp_int]; iexact IH'
  iapply refines_alloctape
  iexact IH''

/-- `bin_log_related_rand_tape`: ports the labeled-rand compatibility from
`fundamental.v:289`, but at `lrel_int` (not `lrel_nat` as in Rocq), to match
Lean's `Typed.rand` signature. Discharges via `refines_rand_tape_int` from
`Compatibility.lean`. -/
theorem bin_log_related_rand_tape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .tape -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_rand, Exp.substMap_rand, interp_int]
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_tape) $$ [IH2']
  · rw [← interp_tape]; iexact IH2'
  iapply refines_rand_tape_int $$ [IH1']
  · iexact IH1'
  iexact IH2''

/-- `bin_log_related_rand_unit`: ports unlabeled-rand compatibility, at
`lrel_int`. Discharges via `refines_rand_unit_int`. -/
theorem bin_log_related_rand_unit (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' .int) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' .unit -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.rand e1 e2) (.rand e1' e2') .int) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_rand, Exp.substMap_rand]
  have hb1 : Exp.rand (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
      Ectx.fill [EctxItem.randR (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) := rfl
  have hb2 : Exp.rand (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
      Ectx.fill [EctxItem.randR (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') := rfl
  rw [hb1, hb2]
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_unit) $$ [IH2']
  · rw [← interp_unit]; iexact IH2'
  iapply (refines_bind [EctxItem.randR (Exp.substMap vs.fst e1)]
    [EctxItem.randR (Exp.substMap vs.snd e1')] (A := lrel_unit)) $$ [IH2'']
  · iexact IH2''
  iintro %v2 %v2' Hu
  have hunit_unfold : (lrel_unit (GF := GF)).car v2 v2' =
      iprop(⌜v2.1 = .lit .unit ∧ v2'.1 = .lit .unit⌝) := rfl
  ihave %Hu' : (⌜v2.1 = .lit .unit ∧ v2'.1 = .lit .unit⌝ : IProp GF) $$ [Hu]
  · rw [← hunit_unfold]; iexact Hu
  obtain ⟨hv2, hv2'⟩ := Hu'
  rw [hv2, hv2', interp_int]
  have hbk1 : Ectx.fill [EctxItem.randR (Exp.substMap vs.fst e1)] (Exp.lit .unit) =
      Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.fst e1) := rfl
  have hbk2 : Ectx.fill [EctxItem.randR (Exp.substMap vs.snd e1')] (Exp.lit .unit) =
      Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.snd e1') := rfl
  rw [hbk1, hbk2]
  iapply refines_rand_unit_int
  iexact IH1'

/-! ### Polymorphic / recursive type compatibility -/

/-! #### OFE-rewrite helper for `bin_log_related`

Several polymorphic cases (`tapp`, `fold`, `unfold`, `pack`) need to
transport a `bin_log_related` hypothesis along an OFE-equivalence
`A ≡ B` between the underlying lrels. This is `refines_proper` lifted
through `bin_log_related`'s `∀ vs, env_ltyped2 Γ vs -∗ refines _ _ _ A`
shape. We expose it both as an `≡` (`bin_log_related_proper`) and
as an entailment (`bin_log_related_proper_entails`) for direct use
inside iris-tactics. -/

theorem bin_log_related_proper (E : CoPset) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {A B : lrel rT GF} (h : A ≡ B) :
    bin_log_related E Γ e e' A ≡ bin_log_related E Γ e e' B := by
  unfold bin_log_related
  refine OFE.equiv_dist.mpr fun n => ?_
  refine forall_ne fun vs => ?_
  refine wand_ne.ne .rfl ?_
  exact refines_ne (OFE.equiv_dist.mp h n)

theorem bin_log_related_proper_entails (E : CoPset) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {A B : lrel rT GF} (h : A ≡ B) :
    bin_log_related E Γ e e' A ⊢@{IProp GF} bin_log_related E Γ e e' B :=
  (Iris.BI.equiv_iff.mp (bin_log_related_proper E Γ e e' h)).1

/-- Type-flavored Q2: rewrite at the level of `bin_log_related_ty` when
two interpreted types are OFE-equivalent. -/
theorem bin_log_related_ty_proper_entails (E : CoPset) (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (e e' : Exp rT) {τ1 τ2 : Ty} (h : interp τ1 Δ ≡ (interp τ2 Δ : lrel rT GF)) :
    bin_log_related_ty E Δ Γ e e' τ1 ⊢@{IProp GF}
      bin_log_related_ty E Δ Γ e e' τ2 :=
  bin_log_related_proper_entails E Γ e e' h

/-- Refines OFE-rewrite: bridge `refines E e e' A` and `refines E e e' B`
along an OFE-equivalence `A ≡ B`. Useful in proof bodies where we have
a `refines` hypothesis at one relation and need it at an equivalent one. -/
theorem refines_proper_entails (E : CoPset) (e e' : Exp rT) {A B : lrel rT GF}
    (h : A ≡ B) :
    refines E e e' A ⊢@{IProp GF} refines E e e' B :=
  (Iris.BI.equiv_iff.mp (refines_proper h)).1

/-- Wand form of `refines_proper_entails`, suitable for `iapply` inside
the iris proofmode. -/
theorem refines_proper_wand (E : CoPset) (e e' : Exp rT) {A B : lrel rT GF}
    (h : A ≡ B) :
    refines E e e' A ⊢@{IProp GF} refines E e e' B :=
  refines_proper_entails E e e' h

/-- lrel-level OFE-rewrite at a value pair: bridge `A v v'` and `B v v'`
when `A ≡ B`. Used for value-relation level rewrites under e.g.
`lrel_exists` instantiation. -/
theorem lrel_car_proper_entails {A B : lrel rT GF} (h : A ≡ B) (v v' : Val rT) :
    A.car v v' ⊢@{IProp GF} B.car v v' :=
  (Iris.BI.equiv_iff.mp (h v v')).1

/-- Unfold helper: bridge `(lrel_forall C).car v v'` to its underlying
`∀ A, (lrel_arr lrel_unit (C A)).car v v'` form. The two are defeq but
iris-tactic unification doesn't reduce through `.car`/`lrel.mk`. -/
theorem lrel_forall_unfold (C : lrel rT GF → lrel rT GF) (v v' : Val rT) :
    (lrel_forall C).car v v' ⊢@{IProp GF}
      iprop(∀ (A : lrel rT GF), (lrel_arr lrel_unit (C A)).car v v') :=
  BIBase.Entails.rfl

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
  ihave %Hvs_closed := env_ltyped2_allClosed Γ vs $$ Hvs
  have hvsfst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).1
  have hvssnd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).2
  have hbody_lc : (Exp.substMap vs.fst e).IsLocallyClosed :=
    Exp.substMap_lc hvsfst_closed he_lc
  have hbody'_lc : (Exp.substMap vs.snd e').IsLocallyClosed :=
    Exp.substMap_lc hvssnd_closed he'_lc
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  have hΓdomVs : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨p, hpmem, hpeq⟩ := hy
    subst hpeq
    have hyΓlookup : (Γ.lookup p.1).isSome := RelCtx.lookup_isSome_of_mem hpmem
    have hyVsLookup : (vs.lookup p.1).isSome := (hDom p.1).mp hyΓlookup
    obtain ⟨q, hqmem, hqeq⟩ := ValSubstMap.mem_of_lookup_isSome hyVsLookup
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨q, hqmem, hqeq⟩
  have hdom_eq_fst : (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.1.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have hdom_eq_snd : (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.2.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have he_dom_fst : e.fv ⊆ (vs.fst.map (·.1)).toFinset := by
    rw [hdom_eq_fst]; exact he_fv.trans hΓdomVs
  have he_dom_snd : e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
    rw [hdom_eq_snd]; exact he'_fv.trans hΓdomVs
  have hbody_fv : (Exp.substMap vs.fst e).fv = ∅ :=
    Exp.substMap_fv_eq_empty hvsfst_closed he_dom_fst
  have hbody'_fv : (Exp.substMap vs.snd e').fv = ∅ :=
    Exp.substMap_fv_eq_empty hvssnd_closed he_dom_snd
  have harr : (interp (Ty.forall' τ) Δ : lrel rT GF) =
      lrel_forall (fun A => interp τ (TyEnv.cons A Δ)) := rfl
  rw [harr]
  iapply (refines_forall (e := Exp.substMap vs.fst e) (e' := Exp.substMap vs.snd e')
    (C := fun A => interp τ (TyEnv.cons A Δ))
    hbody_lc hbody'_lc hbody_fv hbody'_fv)
  iintro !> %A
  have HbodyAtA := Hbody A
  unfold bin_log_related_ty bin_log_related at HbodyAtA
  ihave HbodyAtA_iris := HbodyAtA
  iapply HbodyAtA_iris
  iexact Hvs

theorem bin_log_related_tapp (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.forall' τ)) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ
        (.app e (.lit .unit)) (.app e' (.lit .unit)) (τ.single τ') := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [Exp.substMap_app, Exp.substMap_app, Exp.substMap_lit, Exp.substMap_lit]
  have hb1 : Exp.app (Exp.substMap vs.fst e) (.lit .unit) =
      Ectx.fill [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.fst e) := rfl
  have hb2 : Exp.app (Exp.substMap vs.snd e') (.lit .unit) =
      Ectx.fill [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩] (Exp.substMap vs.snd e') := rfl
  rw [hb1, hb2]
  iapply (refines_bind [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩]
    [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩]
    (A := interp (Ty.forall' τ) Δ)
    (A' := interp (Ty.single τ τ') Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' Hv
  have hbridge_forall : (interp (Ty.forall' τ) Δ).car v v' =
      (lrel_forall (fun A => interp τ (TyEnv.cons A Δ))).car v v' := rfl
  ihave Hv' : iprop((lrel_forall (fun A => interp τ (TyEnv.cons A Δ))).car v v') $$ [Hv]
  · rw [← hbridge_forall]; iexact Hv
  ihave HvF := lrel_forall_unfold (fun A => interp τ (TyEnv.cons A Δ)) v v' $$ Hv'
  ihave HvSpec := HvF $$ %(interp τ' Δ)
  ihave HvArr := lrel_arr_unfold_wand lrel_unit
    (interp τ (TyEnv.cons (interp τ' Δ) Δ)) v v' $$ HvSpec
  ihave HvArr2 := HvArr $$ %⟨.lit .unit, IsVal.lit⟩ %⟨.lit .unit, IsVal.lit⟩
  have hUnit : ⊢@{IProp GF} (lrel_unit (rT := rT) (GF := GF)).car
      ⟨.lit .unit, IsVal.lit⟩ ⟨.lit .unit, IsVal.lit⟩ := by
    show ⊢@{IProp GF} iprop(⌜(.lit .unit : Exp rT) = .lit .unit ∧ (.lit .unit : Exp rT) = .lit .unit⌝)
    ipure_intro; exact ⟨rfl, rfl⟩
  ihave HvApp : iprop(refines ⊤ (Exp.app v.1 (.lit .unit)) (Exp.app v'.1 (.lit .unit))
      (interp τ (TyEnv.cons (interp τ' Δ) Δ))) $$ [HvArr2]
  · ihave HUnit := hUnit
    iapply HvArr2
    iexact HUnit
  have hsub : interp τ (TyEnv.cons (interp τ' Δ) Δ) ≡ interp (Ty.single τ τ') Δ :=
    (interp_subst τ' τ Δ).symm
  ihave HvAppFinal := refines_proper_entails ⊤ (Exp.app v.1 (.lit .unit))
    (Exp.app v'.1 (.lit .unit)) hsub $$ HvApp
  have hbridge1 : Ectx.fill [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩] v.1 =
      Exp.app v.1 (.lit .unit) := rfl
  have hbridge2 : Ectx.fill [EctxItem.appL ⟨.lit .unit, IsVal.lit⟩] v'.1 =
      Exp.app v'.1 (.lit .unit) := rfl
  rw [hbridge1, hbridge2]
  iexact HvAppFinal

theorem bin_log_related_fold (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (τ.single (.rec' τ))) ⊢@{IProp GF}
      bin_log_related_ty (⊤ : CoPset) Δ Γ e e' (.rec' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  have hsub : interp (Ty.single τ (.rec' τ)) Δ ≡
      interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ) :=
    interp_subst (.rec' τ) τ Δ
  ihave IH'' := refines_proper_entails ⊤ (Exp.substMap vs.fst e)
    (Exp.substMap vs.snd e') hsub $$ IH'
  iapply refines_wand $$ IH''
  iintro %v %v' #Hv
  imodintro
  let CRec : lrel rT GF -n> lrel rT GF :=
    { f := fun X => interp τ (TyEnv.cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE τ).ne (TyEnv.cons_ne_head hXY)⟩ }
  have hunfold_eq : (interp (Ty.rec' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        ▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') :=
    OFE.Leibniz.eq_of_eqv (α := IProp GF)
      (lrel_rec_unfold (GF := GF) CRec v v')
  rw [hunfold_eq]
  isplitr
  · iapply (interp_closed (Δ := TyEnv.cons (interp (Ty.rec' τ) Δ) Δ) τ v v')
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
  have hb1 : Exp.app recUnfold (Exp.substMap vs.fst e) =
      Ectx.fill [EctxItem.appR recUnfold] (Exp.substMap vs.fst e) := rfl
  have hb2 : Exp.app recUnfold (Exp.substMap vs.snd e') =
      Ectx.fill [EctxItem.appR recUnfold] (Exp.substMap vs.snd e') := rfl
  rw [hb1, hb2]
  iapply (refines_bind [EctxItem.appR recUnfold] [EctxItem.appR recUnfold]
    (A := interp (Ty.rec' τ) Δ)
    (A' := interp (Ty.single τ (.rec' τ)) Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' Hv
  -- Hv : (interp (.rec' τ) Δ).car v v'.
  -- Unfold via lrel_rec_unfold: Hv = ⌜...⌝ ∗ ▷ (interp τ (cons (rec' τ) Δ) Δ).car v v'.
  let CRec : lrel rT GF -n> lrel rT GF :=
    { f := fun X => interp τ (TyEnv.cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE τ).ne (TyEnv.cons_ne_head hXY)⟩ }
  have hunfold_eq : (interp (Ty.rec' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        ▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') :=
    OFE.Leibniz.eq_of_eqv (α := IProp GF)
      (lrel_rec_unfold (GF := GF) CRec v v')
  ihave HvUnfold : iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      ▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') $$ [Hv]
  · rw [← hunfold_eq]; iexact Hv
  ihave HvL : iprop(▷ (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v') $$ [HvUnfold]
  · icases HvUnfold with ⟨_, HvLater⟩
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
  iapply (refines_pure_l (K := []) (e := Exp.app (.lam (.bvar 0)) v.1)
    (e' := Exp.open' (.bvar 0) v.1)
    (Hex := pureExec_app_lam) v.2.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  -- Now HvL's ▷ has been stripped: HvL : (interp τ (cons (rec' τ) Δ) Δ).car v v'.
  rw [hopenL]
  iapply (refines_pure_r (K := []) (e := Exp.app (.lam (.bvar 0)) v'.1)
    (e' := Exp.open' (.bvar 0) v'.1)
    (Hex := pureExec_app_lam) v'.2.toIsValue)
  rw [hopenR]
  iapply refines_ret (e1 := Ectx.fill [] v.1) (e2 := Ectx.fill [] v'.1)
    (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  -- Goal: (interp (τ.single (.rec' τ)) Δ).car v v'.
  -- Bridge to (interp τ (cons (rec' τ) Δ) Δ).car v v' via interp_subst, then close with Hv.
  have hsub_eq : (interp (Ty.single τ (.rec' τ)) Δ).car v v' =
      (interp τ (TyEnv.cons (interp (Ty.rec' τ) Δ) Δ)).car v v' :=
    OFE.eq_of_eqv (interp_subst (.rec' τ) τ Δ v v')
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
  -- Via interp_subst: ≡ refines ⊤ ... (interp τ (cons (interp τ' Δ) Δ)).
  have hsub : interp (Ty.single τ τ') Δ ≡ interp τ (TyEnv.cons (interp τ' Δ) Δ) :=
    interp_subst τ' τ Δ
  ihave IH'' := refines_proper_entails ⊤ (Exp.substMap vs.fst e)
    (Exp.substMap vs.snd e') hsub $$ IH'
  -- Goal: refines ⊤ ... (interp (.exists' τ) Δ) = lrel_exists (fun X => interp τ (cons X Δ)).
  -- Pack at witness `interp τ' Δ` via refines_wand. Closedness extracted via interp_closed.
  iapply refines_wand $$ IH''
  iintro %v %v' Hv
  imodintro
  -- Extract closedness from Hv as a persistent pure fact (doesn't consume Hv).
  ihave %Hclosed : iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ : IProp GF) $$ [Hv]
  · iapply (interp_closed (Δ := TyEnv.cons (interp τ' Δ) Δ) τ v v')
    iexact Hv
  -- Goal: (interp (.exists' τ) Δ).car v v' =
  --       ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗ ∃ A, (interp τ (cons A Δ)).car v v'.
  have hex : (interp (Ty.exists' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        (∃ A : lrel rT GF, (interp τ (TyEnv.cons A Δ)).car v v')) := rfl
  rw [hex]
  isplitr
  · ipure_intro; exact Hclosed
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
  ihave HIH1_iris := HIH1_sp
  ihave HIH1' := HIH1_iris $$ %vs Hvs
  -- HIH1' : refines ⊤ (substMap vs.fst e1) (substMap vs.snd e1') (interp (.exists' τ) Δ)
  -- Bind to get values v, v' with (interp (.exists' τ) Δ).car v v'.
  rw [Exp.substMap_app, Exp.substMap_app, Exp.substMap_lam, Exp.substMap_lam]
  -- Closedness machinery (analogous to lam).
  ihave %Hvs_closed := env_ltyped2_allClosed Γ vs $$ Hvs
  have hvsfst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).1
  have hvssnd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨w1, w2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]; exact (Hvs_closed (z, w1, w2) hmem).2
  -- Bind under [appR (.lam (substMap vs.fst e2))] for e1, similarly for spec.
  have hbL : Exp.app (Exp.lam (Exp.substMap vs.fst e2)) (Exp.substMap vs.fst e1) =
      Ectx.fill [EctxItem.appR (Exp.lam (Exp.substMap vs.fst e2))] (Exp.substMap vs.fst e1) := rfl
  have hbR : Exp.app (Exp.lam (Exp.substMap vs.snd e2')) (Exp.substMap vs.snd e1') =
      Ectx.fill [EctxItem.appR (Exp.lam (Exp.substMap vs.snd e2'))] (Exp.substMap vs.snd e1') := rfl
  rw [hbL, hbR]
  iapply (refines_bind [EctxItem.appR (Exp.lam (Exp.substMap vs.fst e2))]
    [EctxItem.appR (Exp.lam (Exp.substMap vs.snd e2'))]
    (A := interp (Ty.exists' τ) Δ)) $$ [HIH1']
  · iexact HIH1'
  iintro %v %v' #Hv
  -- Hv : (interp (.exists' τ) Δ).car v v' = ⌜closed⌝ ∗ ∃ A, (interp τ (cons A Δ)).car v v'.
  -- Destructure.
  have hex_unfold : (interp (Ty.exists' τ) Δ).car v v' =
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        (∃ A : lrel rT GF, (interp τ (TyEnv.cons A Δ)).car v v')) := rfl
  ihave Hv_unfold : iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      (∃ A : lrel rT GF, (interp τ (TyEnv.cons A Δ)).car v v')) $$ [Hv]
  · rw [← hex_unfold]; iexact Hv
  icases Hv_unfold with ⟨%hvc, %A, #HvA⟩
  -- Now Hv (we destructured): %hvc : closed; %A : witness lrel; HvA : (interp τ (cons A Δ)).car v v'.
  -- Pick fresh atom x.
  obtain ⟨x, hxFresh⟩ := HasFresh.fresh_exists
    (L ∪ e2.fv ∪ e2'.fv ∪ (vs.map (·.1)).toFinset)
  have hxL : x ∉ L :=
    fun h => hxFresh (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hxFvE2 : x ∉ e2.fv :=
    fun h => hxFresh (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hxFvE2' : x ∉ e2'.fv :=
    fun h => hxFresh (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hxNotDom : x ∉ (vs.map (·.1)).toFinset :=
    fun h => hxFresh (Finset.mem_union_right _ h)
  -- Beta-step the application: (.lam e2).app v reduces to open' e2 v.
  have hL2 : Ectx.fill [EctxItem.appR (Exp.lam (Exp.substMap vs.fst e2))] v.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.lam (Exp.substMap vs.fst e2)) v.1) := rfl
  have hR2 : Ectx.fill [EctxItem.appR (Exp.lam (Exp.substMap vs.snd e2'))] v'.1 =
    Ectx.fill ([] : Ectx rT) (Exp.app (Exp.lam (Exp.substMap vs.snd e2')) v'.1) := rfl
  rw [hL2, hR2]
  iapply (refines_pure_l (K := []) (e := Exp.app (Exp.lam (Exp.substMap vs.fst e2)) v.1)
    (e' := Exp.open' (Exp.substMap vs.fst e2) v.1)
    (Hex := pureExec_app_lam) v.2.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (e := Exp.app (Exp.lam (Exp.substMap vs.snd e2')) v'.1)
    (e' := Exp.open' (Exp.substMap vs.snd e2') v'.1)
    (Hex := pureExec_app_lam) v'.2.toIsValue)
  -- Goal: refines ⊤ ([].fill (open' (substMap vs.fst e2) v.1)) ([].fill (open' (substMap vs.snd e2') v'.1)) (interp τ2 Δ).
  -- Use HIH2 at A and x. vs' := (x, (v, v')) :: vs.
  let vs' : ValSubstMap rT := (x, (v, v')) :: vs
  have hv_c : v.1.isClosed .empty :=
    ⟨hvc.1.1, by rw [hvc.1.2]; exact Finset.empty_subset _⟩
  have hv'_c : v'.1.isClosed .empty :=
    ⟨hvc.2.1, by rw [hvc.2.2]; exact Finset.empty_subset _⟩
  ihave Hvs' : iprop(env_ltyped2 ((x, interp τ (TyEnv.cons A Δ)) :: Γ) vs') $$ [HvA]
  · iapply (env_ltyped2_insert Γ vs x (interp τ (TyEnv.cons A Δ)) v v' hv_c hv'_c)
    isplitr [HvA]
    · iexact HvA
    iexact Hvs
  -- Apply HIH2 at A and x.
  have HIH2AtAX := HIH2 A x hxL
  unfold bin_log_related_ty bin_log_related at HIH2AtAX
  ihave HIH2_iris := HIH2AtAX
  ihave HBody_shift : iprop(refines (⊤ : CoPset)
      (Exp.substMap vs'.fst (Exp.open' e2 (.fvar x)))
      (Exp.substMap vs'.snd (Exp.open' e2' (.fvar x)))
      (interp τ2.shift (TyEnv.cons A Δ))) $$ [HIH2_iris Hvs']
  · iapply HIH2_iris
    iexact Hvs'
  -- Bridge interp τ2.shift (cons A Δ) ≡ interp τ2 Δ via interp_ren.
  have hshift : interp τ2.shift (TyEnv.cons A Δ) ≡ interp τ2 Δ := interp_ren τ2 A Δ
  ihave HBody := refines_proper_entails ⊤
    (Exp.substMap vs'.fst (Exp.open' e2 (.fvar x)))
    (Exp.substMap vs'.snd (Exp.open' e2' (.fvar x))) hshift $$ HBody_shift
  -- Bridge via substMap_open_fresh.
  have hxDomVs : ValSubstMap.lookup vs x = none := by
    have aux : ∀ (ys : ValSubstMap rT), x ∉ (ys.map (·.1)).toFinset →
        ValSubstMap.lookup ys x = none := by
      intro ys
      induction ys with
      | nil => intro _; rfl
      | cons p rest ih =>
        obtain ⟨z, _⟩ := p
        intro hxNot
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hxNot
        simp only [ValSubstMap.lookup, ih hxNot.2]
        simp [hxNot.1]
    exact aux vs hxNotDom
  have hxDomFst : SubstMap.lookup vs.fst x = none := by
    rw [ValSubstMap.fst_lookup, hxDomVs]; rfl
  have hxDomSnd : SubstMap.lookup vs.snd x = none := by
    rw [ValSubstMap.snd_lookup, hxDomVs]; rfl
  have hbridge_fst : Exp.substMap vs'.fst (Exp.open' e2 (.fvar x)) =
      Exp.open' (Exp.substMap vs.fst e2) v.1 := by
    show Exp.substMap ((x, v.1) :: vs.fst) (Exp.open' e2 (.fvar x)) = _
    exact Exp.substMap_open_fresh hvsfst_closed hxFvE2 hxDomFst hvc.1.1
  have hbridge_snd : Exp.substMap vs'.snd (Exp.open' e2' (.fvar x)) =
      Exp.open' (Exp.substMap vs.snd e2') v'.1 := by
    show Exp.substMap ((x, v'.1) :: vs.snd) (Exp.open' e2' (.fvar x)) = _
    exact Exp.substMap_open_fresh hvssnd_closed hxFvE2' hxDomSnd hvc.2.1
  ihave HBody' : iprop(refines (⊤ : CoPset)
      (Exp.open' (Exp.substMap vs.fst e2) v.1)
      (Exp.open' (Exp.substMap vs.snd e2') v'.1)
      (interp τ2 Δ)) $$ [HBody]
  · rw [← hbridge_fst, ← hbridge_snd]; iexact HBody
  -- Bridge ectx fill to bare expr.
  have hf1 : (Ectx.fill ([] : Ectx rT) (Exp.open' (Exp.substMap vs.fst e2) v.1)) =
      Exp.open' (Exp.substMap vs.fst e2) v.1 := rfl
  have hf2 : (Ectx.fill ([] : Ectx rT) (Exp.open' (Exp.substMap vs.snd e2') v'.1)) =
      Exp.open' (Exp.substMap vs.snd e2') v'.1 := rfl
  rw [hf1, hf2]
  iexact HBody'

/-! ### Operator / scrut compatibility -/

theorem bin_log_related_int_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp rT} {τ : Ty}
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
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      lrel_int) $$ [IH1']
  · rw [← interp_int]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_int) $$ [IH2']
  · rw [← interp_int]; iexact IH2'
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
  cases op
  case plus =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .plus _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 + n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case minus =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .minus _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 - n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case mult =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .mult _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 * n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case div =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .div _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 / n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case mod =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .mod _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 % n2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case and => simp [BinOp.intResTy] at Hres
  case or  => simp [BinOp.intResTy] at Hres
  case xor => simp [BinOp.intResTy] at Hres
  case eq =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .eq _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide ((BaseLit.int n1) = .int n2))
    ipure_intro
    exact ⟨rfl, rfl⟩
  case lt =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .lt _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide (n1 < n2))
    ipure_intro
    exact ⟨rfl, rfl⟩
  case le =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .le _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide (n1 ≤ n2))
    ipure_intro
    exact ⟨rfl, rfl⟩
  case shl =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .shl _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 * 2 ^ n2.toNat)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case shr =>
    simp [BinOp.intResTy] at Hres; subst Hres; rw [interp_int]
    iapply (refines_binop_pure .shr _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_int))
    unfold lrel_int
    iexists (n1 / 2 ^ n2.toNat)
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_bool_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : BinOp) {e1 e2 e1' e2' : Exp rT} {τ : Ty}
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
  ihave IH1'' : iprop(refines ⊤ (Exp.substMap vs.fst e1) (Exp.substMap vs.snd e1')
      lrel_bool) $$ [IH1']
  · rw [← interp_bool]; iexact IH1'
  ihave IH2'' : iprop(refines ⊤ (Exp.substMap vs.fst e2) (Exp.substMap vs.snd e2')
      lrel_bool) $$ [IH2']
  · rw [← interp_bool]; iexact IH2'
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
  case lt => simp [BinOp.boolResTy] at Hres
  case le => simp [BinOp.boolResTy] at Hres
  case shl => simp [BinOp.boolResTy] at Hres
  case shr => simp [BinOp.boolResTy] at Hres
  case and =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .and _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 && b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case or =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .or _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 || b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case xor =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .xor _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (b1 ^^ b2)
    ipure_intro
    exact ⟨rfl, rfl⟩
  case eq =>
    simp [BinOp.boolResTy] at Hres; subst Hres; rw [interp_bool]
    iapply (refines_binop_pure .eq _ _ _ IsVal.lit IsVal.lit IsVal.lit
      (heval := rfl) (A := lrel_bool))
    unfold lrel_bool
    iexists (decide ((BaseLit.bool b1) = .bool b2))
    ipure_intro
    exact ⟨rfl, rfl⟩

theorem bin_log_related_int_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : UnOp) {e e' : Exp rT} {τ : Ty}
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
    rw [Exp.substMap_unop, Exp.substMap_unop, interp_int]
    ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
        lrel_int) $$ [IH']
    · rw [← interp_int (GF := GF) Δ]; iexact IH'
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
    have heval : UnOp.eval .minus (Exp.lit (.int n) : Exp rT) = some (Exp.lit (.int n.neg)) := rfl
    have hφ : (Exp.lit (.int n) : Exp rT).isValue ∧ UnOp.eval .minus (Exp.lit (.int n) : Exp rT) = some _ :=
      ⟨IsVal.lit.toIsValue, heval⟩
    have hf1 : (Exp.unop .minus (.lit (.int n)) : Exp rT) =
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

theorem bin_log_related_bool_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    (op : UnOp) {e e' : Exp rT} {τ : Ty}
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
    rw [Exp.substMap_unop, Exp.substMap_unop, interp_bool]
    ihave IH'' : iprop(refines ⊤ (Exp.substMap vs.fst e) (Exp.substMap vs.snd e')
        lrel_bool) $$ [IH']
    · rw [← interp_bool (GF := GF) Δ]; iexact IH'
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
    have heval : UnOp.eval .neg (Exp.lit (.bool b) : Exp rT) = some (Exp.lit (.bool (¬b))) := rfl
    have hφ : (Exp.lit (.bool b) : Exp rT).isValue ∧ UnOp.eval .neg (Exp.lit (.bool b) : Exp rT) = some _ :=
      ⟨IsVal.lit.toIsValue, heval⟩
    have hf1 : (Exp.unop .neg (.lit (.bool b)) : Exp rT) =
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

/-- **Statement:** `eq` of two `UnboxedType`-related arguments is related at `bool`.
Mirrors Rocq's `bin_log_related_unboxed_eq` (fundamental.v ~167). -/
theorem bin_log_related_unboxed_eq (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty}
    (HUnboxed : UnboxedType τ) :
    iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e1 e1' τ) ⊢@{IProp GF}
      iprop(bin_log_related_ty (⊤ : CoPset) Δ Γ e2 e2' τ -∗
        bin_log_related_ty (⊤ : CoPset) Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool) := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [Exp.substMap_binop, Exp.substMap_binop]
  -- Bind e2, e2' first.
  have hbR : Exp.binop .eq (Exp.substMap vs.fst e1) (Exp.substMap vs.fst e2) =
      Ectx.fill [EctxItem.binopR .eq (Exp.substMap vs.fst e1)] (Exp.substMap vs.fst e2) := rfl
  have hbR' : Exp.binop .eq (Exp.substMap vs.snd e1') (Exp.substMap vs.snd e2') =
      Ectx.fill [EctxItem.binopR .eq (Exp.substMap vs.snd e1')] (Exp.substMap vs.snd e2') := rfl
  rw [hbR, hbR']
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
  iapply (refines_bind [EctxItem.binopL .eq v2] [EctxItem.binopL .eq v2'] (A := interp τ Δ)) $$ [IH1']
  · iexact IH1'
  iintro %v1 %v1' #Hv1
  -- Now we have v1, v2 (LHS), v1', v2' (RHS), all related at τ.
  -- Use unboxed_type_eq to get pure: v1 = v2 ↔ v1' = v2'.
  ihave Heq : iprop(|={⊤}=> ⌜v1 = v2 ↔ v1' = v2'⌝) $$ [Hv1 Hv2]
  · ihave Heq' := unboxed_type_eq HUnboxed (v1 := v1) (v2 := v1') (w1 := v2) (w2 := v2') $$ Hv1
    iapply Heq'
    iexact Hv2
  -- Extract literal shapes via the helper.
  ihave Hsh1 := unboxed_type_lit_shape HUnboxed (v := v1) (v' := v1') $$ Hv1
  ihave Hsh2 := unboxed_type_lit_shape HUnboxed (v := v2) (v' := v2') $$ Hv2
  icases Hsh1 with ⟨%l1, %l1', %hv1eq, %hv1'eq⟩
  icases Hsh2 with ⟨%l2, %l2', %hv2eq, %hv2'eq⟩
  -- Reshape goal: ectx fills become bare binops, then substitute lit forms.
  have hL : Ectx.fill [EctxItem.binopL .eq v2] v1.1 = .binop .eq v1.1 v2.1 := rfl
  have hR : Ectx.fill [EctxItem.binopL .eq v2'] v1'.1 = .binop .eq v1'.1 v2'.1 := rfl
  rw [hL, hR, hv1eq, hv2eq, hv1'eq, hv2'eq]
  -- Now extract pure Heq via imod (refines absorbs fupd via ElimModal).
  imod Heq with %heqIff
  -- Compute hdec at Lean level before re-entering iris-heavy section.
  have hdec : decide (l1 = l2) = decide (l1' = l2') :=
    have h1 : v1 = v2 ↔ (l1 : BaseLit rT) = l2 := by
      refine ⟨fun h => ?_, fun h => Val.ext (by rw [hv1eq, hv2eq, h])⟩
      have hp : v1.1 = v2.1 := congrArg Sigma.fst h
      rw [hv1eq, hv2eq] at hp
      exact Exp.lit.inj hp
    have h2 : v1' = v2' ↔ (l1' : BaseLit rT) = l2' := by
      refine ⟨fun h => ?_, fun h => Val.ext (by rw [hv1'eq, hv2'eq, h])⟩
      have hp : v1'.1 = v2'.1 := congrArg Sigma.fst h
      rw [hv1'eq, hv2'eq] at hp
      exact Exp.lit.inj hp
    have hdecIff : (l1 = l2) ↔ (l1' = l2') := h1.symm.trans (heqIff.trans h2)
    by
      by_cases hLR : l1 = l2
      · rw [decide_eq_true hLR, decide_eq_true (hdecIff.mp hLR)]
      · rw [decide_eq_false hLR, decide_eq_false (fun h => hLR (hdecIff.mpr h))]
  -- Goal: refines ⊤ (.binop .eq #l1 #l2) (.binop .eq #l1' #l2') lrel_bool.
  -- β-step both sides via pureExec_binop with heval = .lit (.bool (decide (l1 = l2))) etc.
  have heval_l : BinOp.eval .eq (.lit l1) (.lit l2) =
      some (.lit (.bool (decide (l1 = l2)))) := rfl
  have heval_r : BinOp.eval .eq (.lit l1') (.lit l2') =
      some (.lit (.bool (decide (l1' = l2')))) := rfl
  have hφ_l : (Exp.lit l1).isValue ∧ (Exp.lit l2).isValue ∧
      BinOp.eval .eq (.lit l1) (.lit l2) = some _ :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, heval_l⟩
  have hφ_r : (Exp.lit l1').isValue ∧ (Exp.lit l2').isValue ∧
      BinOp.eval .eq (.lit l1') (.lit l2') = some _ :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, heval_r⟩
  have hfL : Exp.binop .eq (.lit l1) (.lit l2) =
      Ectx.fill ([] : Ectx rT) (Exp.binop .eq (.lit l1) (.lit l2)) := rfl
  have hfR : Exp.binop .eq (.lit l1') (.lit l2') =
      Ectx.fill ([] : Ectx rT) (Exp.binop .eq (.lit l1') (.lit l2')) := rfl
  rw [hfL, hfR]
  iapply (refines_pure_l (K := []) (Hex := pureExec_binop) hφ_l)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (Hex := pureExec_binop) hφ_r)
  iapply refines_ret
    (e1 := Ectx.fill [] (Exp.lit (.bool (decide (l1 = l2)))))
    (e2 := Ectx.fill [] (Exp.lit (.bool (decide (l1' = l2')))))
    (v1 := ⟨.lit (.bool (decide (l1 = l2))), IsVal.lit⟩)
    (v2 := ⟨.lit (.bool (decide (l1' = l2'))), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  rw [interp_bool]
  unfold lrel_bool
  iexists (decide (l1 = l2))
  rw [hdec]
  ipure_intro
  exact ⟨rfl, rfl⟩

/-- **Pattern-match agreement**: if `v ~ v'` at `interp τs Δ` and `PatTyped τs p τb`,
then `tryMatch p v.1` and `tryMatch p v'.1` produce related outcomes — either
both succeed with related bindings, or both fail. The shape used here exposes
the bindings as `Val`s (with their `IsVal` witnesses) since the operational
step requires values. -/
theorem pat_match_related {Δ : TyEnv rT GF} {τs τb : Ty} {p : Pat rT}
    (Hpat : PatTyped τs p τb) (v v' : Val rT) :
    (interp τs Δ).car v v' ⊢@{IProp GF}
      iprop((∃ (b b' : Val rT), ⌜Pat.tryMatch p v.1 = some b.1 ∧
                                Pat.tryMatch p v'.1 = some b'.1⌝ ∗
            (interp τb Δ).car b b') ∨
        ⌜Pat.tryMatch p v.1 = none ∧ Pat.tryMatch p v'.1 = none⌝) := by
  induction Hpat generalizing v v' with
  | @wildcard τ =>
    -- tryMatch wildcard v = some v.1; bindings = v.1 (which is a Val).
    iintro Hvv
    iapply BI.or_intro_l
    iexists v, v'
    isplitr
    · ipure_intro
      simp [Pat.tryMatch]
    iexact Hvv
  | @lit_int z =>
    -- v ~ v' at lrel_int means v.1 = v'.1 = .lit (.int n) for same n.
    rw [interp_int]
    iintro Hv
    ihave ⟨%n, %h⟩ := lrel_int_unfold v v' $$ Hv
    by_cases hzn : z = n
    · -- Match succeeds: tryMatch (.lit (.int z)) (.lit (.int n)) = some (.lit .unit) when z = n.
      iapply BI.or_intro_l
      iexists ⟨.lit .unit, IsVal.lit⟩, ⟨.lit .unit, IsVal.lit⟩
      isplitr
      · ipure_intro
        subst hzn
        refine ⟨?_, ?_⟩
        · rw [h.1]; exact Pat.tryMatch_lit_eq (.int z)
        · rw [h.2]; exact Pat.tryMatch_lit_eq (.int z)
      -- (interp .unit Δ).car ⟨.lit .unit, _⟩ ⟨.lit .unit, _⟩ via lrel_unit.
      rw [interp_unit]
      unfold lrel_unit
      ipure_intro
      exact ⟨rfl, rfl⟩
    · -- Match fails: z ≠ n so the BaseLit beq is false.
      iapply BI.or_intro_r
      ipure_intro
      have hbeq : ¬ ((BaseLit.int z : BaseLit rT) == BaseLit.int n) = true := by
        show ¬ (Int.decEq z n).decide = true
        intro hd
        exact hzn (of_decide_eq_true hd)
      refine ⟨?_, ?_⟩
      · rw [h.1]; exact Pat.tryMatch_lit_ne hbeq
      · rw [h.2]; exact Pat.tryMatch_lit_ne hbeq
  | @lit_bool b =>
    rw [interp_bool]
    iintro Hv
    ihave ⟨%b', %h⟩ := lrel_bool_unfold v v' $$ Hv
    by_cases hbb : b = b'
    · iapply BI.or_intro_l
      iexists ⟨.lit .unit, IsVal.lit⟩, ⟨.lit .unit, IsVal.lit⟩
      isplitr
      · ipure_intro
        subst hbb
        refine ⟨?_, ?_⟩
        · rw [h.1]; exact Pat.tryMatch_lit_eq (.bool b)
        · rw [h.2]; exact Pat.tryMatch_lit_eq (.bool b)
      rw [interp_unit]
      unfold lrel_unit
      ipure_intro
      exact ⟨rfl, rfl⟩
    · iapply BI.or_intro_r
      ipure_intro
      have hbeq : ¬ ((BaseLit.bool b : BaseLit rT) == BaseLit.bool b') = true := by
        show ¬ (Bool.decEq b b').decide = true
        intro hd; exact hbb (of_decide_eq_true hd)
      refine ⟨?_, ?_⟩
      · rw [h.1]; exact Pat.tryMatch_lit_ne hbeq
      · rw [h.2]; exact Pat.tryMatch_lit_ne hbeq
  | lit_unit =>
    rw [interp_unit]
    show iprop(⌜v.1 = .lit .unit ∧ v'.1 = .lit .unit⌝) ⊢ _
    iintro %h
    iapply BI.or_intro_l
    iexists ⟨.lit .unit, IsVal.lit⟩, ⟨.lit .unit, IsVal.lit⟩
    isplitr
    · ipure_intro
      refine ⟨?_, ?_⟩
      · rw [h.1]; exact Pat.tryMatch_lit_eq .unit
      · rw [h.2]; exact Pat.tryMatch_lit_eq .unit
    -- Goal: _ ⊢ lrel_unit.car ⟨lit unit, _⟩ ⟨lit unit, _⟩.
    -- def-eq to iprop(⌜...⌝).
    have hrfl : (lrel_unit (GF := GF)).car ⟨.lit .unit, IsVal.lit⟩ ⟨.lit .unit, IsVal.lit⟩
        = iprop(⌜(⟨.lit .unit, IsVal.lit⟩ : Val rT).1 = .lit .unit ∧
                 (⟨.lit .unit, IsVal.lit⟩ : Val rT).1 = .lit .unit⌝) := rfl
    rw [hrfl]
    iintro
    ipure_intro
    exact ⟨rfl, rfl⟩
  | @pair τ1 τ2 p1 p2 b1 b2 Hpat1 Hpat2 ih1 ih2 =>
    have hprod : (interp (Ty.prod τ1 τ2) Δ : lrel rT GF) =
        lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl
    rw [hprod]
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
        iapply BI.or_intro_l
        iexists ⟨.pair ba.1 bb.1, IsVal.pair ba.2 bb.2⟩,
                ⟨.pair ba'.1 bb'.1, IsVal.pair ba'.2 bb'.2⟩
        isplitr
        · ipure_intro
          simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hrb.1, hrb.2]
        -- Need (interp (.prod b1 b2) Δ).car ⟨.pair ba bb, _⟩ ⟨.pair ba' bb', _⟩.
        have hprodb : (interp (Ty.prod b1 b2) Δ : lrel rT GF) =
            lrel_prod (interp b1 Δ) (interp b2 Δ) := rfl
        rw [hprodb]
        unfold lrel_prod
        iexists ba, ba', bb, bb'
        isplitr; · ipure_intro; rfl
        isplitr; · ipure_intro; rfl
        isplitl [HBa]; · iexact HBa
        iexact HBb
      · -- p1 succeeds but p2 fails. Combined match fails.
        iapply BI.or_intro_r
        ipure_intro
        simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hnb.1, hnb.2]
    · -- p1 fails. Combined match fails (regardless of p2).
      iapply BI.or_intro_r
      ipure_intro
      simp [Pat.tryMatch, hv1, hv2, hna.1, hna.2]
  | @inl τ1 τ2 p b Hpat' ih =>
    have hsum : (interp (Ty.sum τ1 τ2) Δ : lrel rT GF) =
        lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
    rw [hsum]
    iintro Hv
    ihave ⟨%w1, %w2, Hcase⟩ := lrel_sum_unfold (interp τ1 Δ) (interp τ2 Δ) v v' $$ Hv
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · -- v1 = inl w1, v2 = inl w2: tryMatch (.inl p) (.inl wi) = tryMatch p wi.
      ihave Hres := ih w1 w2 $$ HA
      icases Hres with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · iapply BI.or_intro_l
        iexists bb, bb'
        isplitr
        · ipure_intro
          simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iapply BI.or_intro_r
        ipure_intro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]
    · -- v1 = inr w1, v2 = inr w2: tryMatch (.inl p) (.inr w) = none.
      iapply BI.or_intro_r
      ipure_intro
      simp [Pat.tryMatch, hv1, hv2]
  | @inr τ1 τ2 p b Hpat' ih =>
    have hsum : (interp (Ty.sum τ1 τ2) Δ : lrel rT GF) =
        lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
    rw [hsum]
    iintro Hv
    ihave ⟨%w1, %w2, Hcase⟩ := lrel_sum_unfold (interp τ1 Δ) (interp τ2 Δ) v v' $$ Hv
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · iapply BI.or_intro_r
      ipure_intro
      simp [Pat.tryMatch, hv1, hv2]
    · ihave Hres := ih w1 w2 $$ HB
      icases Hres with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · iapply BI.or_intro_l
        iexists bb, bb'
        isplitr
        · ipure_intro
          simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iapply BI.or_intro_r
        ipure_intro
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
  have hb1 : Exp.scrut (Exp.substMap vs.fst e) p =
      Ectx.fill [EctxItem.scrut p] (Exp.substMap vs.fst e) := rfl
  have hb2 : Exp.scrut (Exp.substMap vs.snd e') p =
      Ectx.fill [EctxItem.scrut p] (Exp.substMap vs.snd e') := rfl
  rw [hb1, hb2]
  iapply (refines_bind [EctxItem.scrut p] [EctxItem.scrut p]
    (A := interp τs Δ)) $$ [IH']
  · iexact IH'
  iintro %v %v' #Hv
  -- Goal: refines ⊤ (.scrut v.1 p) (.scrut v'.1 p) (interp (.sum τb .unit) Δ).
  -- Case-split on pat_match_related.
  ihave Hmatch := pat_match_related Hpat v v' $$ Hv
  rw [show Ectx.fill [EctxItem.scrut p] v.1 = .scrut v.1 p from rfl,
      show Ectx.fill [EctxItem.scrut p] v'.1 = .scrut v'.1 p from rfl]
  icases Hmatch with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
  · -- Both match: step to .inl bb / .inl bb'.
    have hf1 : Exp.scrut v.1 p = Ectx.fill ([] : Ectx rT) (Exp.scrut v.1 p) := rfl
    have hf2 : Exp.scrut v'.1 p = Ectx.fill ([] : Ectx rT) (Exp.scrut v'.1 p) := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_scrut_some) ⟨v.2.toIsValue, hr.1⟩)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_scrut_some) ⟨v'.2.toIsValue, hr.2⟩)
    iapply refines_ret
      (e1 := Ectx.fill [] (Exp.inl bb.1))
      (e2 := Ectx.fill [] (Exp.inl bb'.1))
      (v1 := ⟨.inl bb.1, IsVal.inl bb.2⟩)
      (v2 := ⟨.inl bb'.1, IsVal.inl bb'.2⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    have hsum : (interp (Ty.sum τb .unit) Δ : lrel rT GF) =
        lrel_sum (interp τb Δ) lrel_unit := rfl
    rw [hsum]
    unfold lrel_sum
    iexists bb, bb'
    iapply BI.or_intro_l
    isplitr; · ipure_intro; rfl
    isplitr; · ipure_intro; rfl
    iexact Hbnd
  · -- Both fail: step to .inr ()
    have hf1 : Exp.scrut v.1 p = Ectx.fill ([] : Ectx rT) (Exp.scrut v.1 p) := rfl
    have hf2 : Exp.scrut v'.1 p = Ectx.fill ([] : Ectx rT) (Exp.scrut v'.1 p) := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_scrut_none) ⟨v.2.toIsValue, hn.1⟩)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_scrut_none) ⟨v'.2.toIsValue, hn.2⟩)
    iapply refines_ret
      (e1 := Ectx.fill [] (Exp.inr (.lit .unit)))
      (e2 := Ectx.fill [] (Exp.inr (.lit .unit)))
      (v1 := ⟨.inr (.lit .unit), IsVal.inr IsVal.lit⟩)
      (v2 := ⟨.inr (.lit .unit), IsVal.inr IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    have hsum : (interp (Ty.sum τb .unit) Δ : lrel rT GF) =
        lrel_sum (interp τb Δ) lrel_unit := rfl
    rw [hsum]
    unfold lrel_sum
    iexists ⟨.lit .unit, IsVal.lit⟩, ⟨.lit .unit, IsVal.lit⟩
    iapply BI.or_intro_r
    isplitr; · ipure_intro; rfl
    isplitr; · ipure_intro; rfl
    unfold lrel_unit
    ipure_intro
    exact ⟨rfl, rfl⟩

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
      OFE.Leibniz.eq_of_eqv (interp_ren τ A Δ)
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
  have hsome := Hty.fvSubset x hx
  have hRcSome : (Γrc.lookup x).isSome := HCtx.lookup_isSome hsome
  obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hRcSome
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨p, hpmem, hpeq⟩

/-- **Fundamental theorem of the logical relation.** Induction on `Typed`
dispatching each case to its `bin_log_related_*` lemma. The recursive
binder cases (`lam`, `fix`) recurse on the body's typing under an extended
context. The polymorphic binder cases (`tlam`, `tunpack`) require relating
the shifted typing context to a re-interpreted relational context — sorried
pending an additional `TctxRelated.shift` lemma threading through `interp_ren`. -/
theorem fundamental {Γtc : Tctx} {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ)
    (Δ : TyEnv rT GF)
    (Γrc : RelCtx rT GF)
    (HCtx : TctxRelated Δ Γtc Γrc) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e e τ := by
  induction Hty generalizing Δ Γrc with
  | @fvar _ x τ hx =>
    exact bin_log_related_var Δ Γrc x τ (HCtx.lookup_some hx)
  | @lit_int _ n =>
    unfold bin_log_related_ty bin_log_related
    iintro %vs _
    rw [Exp.substMap_lit, Exp.substMap_lit]
    set v : Val rT := ⟨.lit (.int n), IsVal.lit⟩
    have hv : (Exp.lit (.int n) : Exp rT) = v.1 := rfl
    rw [hv]
    iapply (refines_ret (v1 := v) (v2 := v) (hv1 := rfl) (hv2 := rfl))
    imodintro
    rw [interp_int]
    unfold lrel_int
    iexists n
    ipure_intro
    exact ⟨rfl, rfl⟩
  | @lit_bool _ b =>
    unfold bin_log_related_ty bin_log_related
    iintro %vs _
    rw [Exp.substMap_lit, Exp.substMap_lit]
    set v : Val rT := ⟨.lit (.bool b), IsVal.lit⟩
    have hv : (Exp.lit (.bool b) : Exp rT) = v.1 := rfl
    rw [hv]
    iapply (refines_ret (v1 := v) (v2 := v) (hv1 := rfl) (hv2 := rfl))
    imodintro
    rw [interp_bool]
    unfold lrel_bool
    iexists b
    ipure_intro
    exact ⟨rfl, rfl⟩
  | lit_unit =>
    unfold bin_log_related_ty bin_log_related
    iintro %vs _
    rw [Exp.substMap_lit, Exp.substMap_lit]
    set v : Val rT := ⟨.lit .unit, IsVal.lit⟩
    have hv : (Exp.lit .unit : Exp rT) = v.1 := rfl
    rw [hv]
    iapply (refines_ret (v1 := v) (v2 := v) (hv1 := rfl) (hv2 := rfl))
    imodintro
    rw [interp_unit]
    unfold lrel_unit
    ipure_intro
    exact ⟨rfl, rfl⟩
  | binop_int Hty1 Hty2 Hres ih1 ih2 =>
    rename_i op _ _ τ
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply (bin_log_related_int_binop Δ Γrc op Hres) $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | binop_bool Hty1 Hty2 Hres ih1 ih2 =>
    rename_i op _ _ τ
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply (bin_log_related_bool_binop Δ Γrc op Hres) $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | unop_int Hty Hres ih =>
    rename_i op _ τ
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_int_unop Δ Γrc op Hres) $$ [IH']
    iexact IH'
  | unop_bool Hty Hres ih =>
    rename_i op _ τ
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_bool_unop Δ Γrc op Hres) $$ [IH']
    iexact IH'
  | unboxed_eq HUnboxed _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply (bin_log_related_unboxed_eq Δ Γrc HUnboxed) $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | pair _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_pair $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | fst _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_fst Δ Γrc) $$ [IH']
    iexact IH'
  | snd _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_snd Δ Γrc) $$ [IH']
    iexact IH'
  | inl _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_injl Δ Γrc) $$ [IH']
    iexact IH'
  | inr _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_injr Δ Γrc) $$ [IH']
    iexact IH'
  | «case» _ _ _ ih0 ih1 ih2 =>
    have IH0 := ih0 Δ Γrc HCtx
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH0' := IH0
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_case $$ [IH0' IH1' IH2']
    · iexact IH0'
    · iexact IH1'
    iexact IH2'
  | cond _ _ _ ih0 ih1 ih2 =>
    have IH0 := ih0 Δ Γrc HCtx
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH0' := IH0
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_if $$ [IH0' IH1' IH2']
    · iexact IH0'
    · iexact IH1'
    iexact IH2'
  | app _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_app $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | alloc _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_alloc Δ Γrc) $$ [IH']
    iexact IH'
  | load _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_load Δ Γrc) $$ [IH']
    iexact IH'
  | store _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_store $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | alloc_tape _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply bin_log_related_alloctape $$ [IH']
    iexact IH'
  | rand _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_rand_tape $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | rand_unit _ _ ih1 ih2 =>
    have IH1 := ih1 Δ Γrc HCtx
    have IH2 := ih2 Δ Γrc HCtx
    iintro
    ihave IH1' := IH1
    ihave IH2' := IH2
    iapply bin_log_related_rand_unit $$ [IH1' IH2']
    · iexact IH1'
    iexact IH2'
  | «scrut» _ Hpat ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_scrut Δ Γrc Hpat) $$ [IH']
    iexact IH'
  | tfold _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_fold Δ Γrc) $$ [IH']
    iexact IH'
  | tunfold _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_unfold Δ Γrc) $$ [IH']
    iexact IH'
  | tapp _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_tapp Δ Γrc) $$ [IH']
    iexact IH'
  | tpack _ ih =>
    have IH := ih Δ Γrc HCtx
    iintro
    ihave IH' := IH
    iapply (bin_log_related_pack Δ Γrc) $$ [IH']
    iexact IH'
  -- Recursive binder cases (lam, fix).
  | @lam L Γtc' e τ1 τ2 Hbody ih =>
    -- Pick fresh atoms not in L ∪ dom(Γrc) ∪ e.fv to satisfy bin_log_related_lam.
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset ∪ e.fv
    have hHbodyTyped : ∀ x ∉ L',
        Typed (Γtc'.insert x τ1) (Exp.open' e (.fvar x)) τ2 := by
      intro x hx
      have hxL : x ∉ L := fun h =>
        hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      exact Hbody x hxL
    -- Derive e.fv ⊆ Γrc.dom by picking a fresh atom y.
    have he_fv : e.fv ⊆ (Γrc.map (·.1)).toFinset := by
      intro z hz
      obtain ⟨y, hy⟩ := Cslib.HasFresh.fresh_exists (L ∪ (Γrc.map (·.1)).toFinset ∪ {z})
      have hyL : y ∉ L := fun h =>
        hy (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hyRc : y ∉ (Γrc.map (·.1)).toFinset := fun h =>
        hy (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hzy : z ≠ y := fun h =>
        hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm))
      have hyRcLookup : Γrc.lookup y = none := by
        cases hRc : Γrc.lookup y with
        | none => rfl
        | some A =>
          exfalso
          have hsome : (Γrc.lookup y).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hyRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      have HCtxY := HCtx.insert y τ1 hyRcLookup
      have hzopen : z ∈ (Exp.open' e (.fvar y)).fv := Exp.fv_subset_open e y hz
      have hzdom := fv_subset_relCtxDom HCtxY (Hbody y hyL) hzopen
      simp only [List.mem_toFinset, List.mem_map] at hzdom
      simp only [List.mem_toFinset, List.mem_map]
      obtain ⟨p, hpmem, hpeq⟩ := hzdom
      rcases List.mem_cons.mp hpmem with rfl | hmem
      · -- p = (y, _), so p.1 = y, but hpeq : p.1 = z, so y = z, contradicts hzy
        exact (hzy hpeq.symm).elim
      · exact ⟨p, hmem, hpeq⟩
    -- Each Hbody x is locally closed.
    have he_lc : ∀ x ∉ L', (Exp.open' e (.fvar x)).IsLocallyClosed := by
      intro x hx
      exact (hHbodyTyped x hx).isLocallyClosed
    apply bin_log_related_lam Δ Γrc L'
      he_lc he_lc he_fv he_fv
    intro x hx
    have hxL : x ∉ L := fun h =>
      hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxRc : Γrc.lookup x = none := by
      -- x ∉ Γrc.map (·.1).toFinset implies x not a key in Γrc.
      have hxNotDom : x ∉ (Γrc.map (·.1)).toFinset := fun h =>
        hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      cases hRc : Γrc.lookup x with
      | none => rfl
      | some A =>
        exfalso
        have hsome : (Γrc.lookup x).isSome := by rw [hRc]; rfl
        obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
        apply hxNotDom
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨p, hpmem, hpeq⟩
    have HCtx' : TctxRelated Δ (Γtc'.insert x τ1) ((x, interp τ1 Δ) :: Γrc) :=
      HCtx.insert x τ1 hxRc
    exact ih x hxL Δ ((x, interp τ1 Δ) :: Γrc) HCtx'
  | @«fix» L Γtc' e τ1 τ2 Hbody ih =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset ∪ e.fv
    have hHbodyTyped : ∀ x ∉ L',
        Typed (Γtc'.insert x (.arrow τ1 τ2)) (Exp.open' e (.fvar x)) (.arrow τ1 τ2) := by
      intro x hx
      have hxL : x ∉ L := fun h =>
        hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      exact Hbody x hxL
    -- Derive e.fv ⊆ Γrc.dom by picking a fresh atom y.
    have he_fv : e.fv ⊆ (Γrc.map (·.1)).toFinset := by
      intro z hz
      obtain ⟨y, hy⟩ := Cslib.HasFresh.fresh_exists (L ∪ (Γrc.map (·.1)).toFinset ∪ {z})
      have hyL : y ∉ L := fun h =>
        hy (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hyRc : y ∉ (Γrc.map (·.1)).toFinset := fun h =>
        hy (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hzy : z ≠ y := fun h =>
        hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm))
      have hyRcLookup : Γrc.lookup y = none := by
        cases hRc : Γrc.lookup y with
        | none => rfl
        | some A =>
          exfalso
          have hsome : (Γrc.lookup y).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hyRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      have HCtxY := HCtx.insert y (.arrow τ1 τ2) hyRcLookup
      have hzopen : z ∈ (Exp.open' e (.fvar y)).fv := Exp.fv_subset_open e y hz
      have hzdom := fv_subset_relCtxDom HCtxY (Hbody y hyL) hzopen
      simp only [List.mem_toFinset, List.mem_map] at hzdom
      simp only [List.mem_toFinset, List.mem_map]
      obtain ⟨p, hpmem, hpeq⟩ := hzdom
      rcases List.mem_cons.mp hpmem with rfl | hmem
      · -- p = (y, _), so p.1 = y, but hpeq : p.1 = z, so y = z, contradicts hzy
        exact (hzy hpeq.symm).elim
      · exact ⟨p, hmem, hpeq⟩
    have he_lc : ∀ x ∉ L', (Exp.open' e (.fvar x)).IsLocallyClosed := by
      intro x hx
      exact (hHbodyTyped x hx).isLocallyClosed
    apply bin_log_related_fix Δ Γrc L'
      he_lc he_lc he_fv he_fv
    intro x hx
    have hxL : x ∉ L := fun h =>
      hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxRc : Γrc.lookup x = none := by
      have hxNotDom : x ∉ (Γrc.map (·.1)).toFinset := fun h =>
        hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      cases hRc : Γrc.lookup x with
      | none => rfl
      | some A =>
        exfalso
        have hsome : (Γrc.lookup x).isSome := by rw [hRc]; rfl
        obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
        apply hxNotDom
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨p, hpmem, hpeq⟩
    have HCtx' : TctxRelated Δ (Γtc'.insert x (.arrow τ1 τ2))
        ((x, interp (.arrow τ1 τ2) Δ) :: Γrc) :=
      HCtx.insert x (.arrow τ1 τ2) hxRc
    exact ih x hxL Δ ((x, interp (.arrow τ1 τ2) Δ) :: Γrc) HCtx'
  -- Polymorphic binder cases (tlam, tunpack). Closedness is now built into
  -- `lrel`'s structure (option D), so the IH works for any `A`.
  | @tlam Γtc' e τ Hbody ih =>
    have hLC : e.IsLocallyClosed := Hbody.isLocallyClosed
    have he_fv : e.fv ⊆ (Γrc.map (·.1)).toFinset :=
      fv_subset_relCtxDom (HCtx.shift default) Hbody
    apply bin_log_related_tlam Δ Γrc hLC hLC he_fv he_fv
    intro A
    -- Goal: ⊢ □ bin_log_related_ty ⊤ (cons A Δ) Γrc e e τ
    -- IH at (cons A Δ, Γrc) using TctxRelated.shift.
    have HCtxShift := HCtx.shift A
    have HFund := ih (TyEnv.cons A Δ) Γrc HCtxShift
    iintro
    imodintro
    ihave Hf := HFund
    iexact Hf
  | @tunpack L Γtc' e1 e2 τ τ2 Hty1 Hbody2 ih1 ih2 =>
    have HIH1 : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e1 e1 (Ty.exists' τ) :=
      ih1 Δ Γrc HCtx
    -- Augment L with Γrc.dom for freshness in the inner Γrc.
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset
    have HIH2 : ∀ A : lrel rT GF, ∀ x ∉ L',
        ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) (TyEnv.cons A Δ)
          ((x, interp τ (TyEnv.cons A Δ)) :: Γrc)
          (Exp.open' e2 (.fvar x)) (Exp.open' e2 (.fvar x)) τ2.shift := by
      intro A x hxL'
      have hxL : x ∉ L := fun h => hxL' (Finset.mem_union_left _ h)
      have hxNotDom : x ∉ (Γrc.map (·.1)).toFinset :=
        fun h => hxL' (Finset.mem_union_right _ h)
      have hxRc : Γrc.lookup x = none := by
        cases hRc : Γrc.lookup x with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc.lookup x).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hxNotDom
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      have HCtxShift := HCtx.shift A
      have HCtxIns : TctxRelated (TyEnv.cons A Δ) ((Γtc'.shift).insert x τ)
          ((x, interp τ (TyEnv.cons A Δ)) :: Γrc) :=
        HCtxShift.insert x τ hxRc
      exact ih2 x hxL (TyEnv.cons A Δ) ((x, interp τ (TyEnv.cons A Δ)) :: Γrc) HCtxIns
    exact bin_log_related_unpack Δ Γrc L' HIH1 HIH2

/-- Closed specialization: `∅ ⊢ₜ e : τ → ⊢ REL e << e : interp τ Δ`. -/
theorem refines_typed (Δ : TyEnv rT GF) {e : Exp rT} {τ : Ty}
    (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines (⊤ : CoPset) e e (interp τ Δ) := by
  have HRel : TctxRelated Δ Tctx.empty ([] : RelCtx rT GF) := by
    intro x; simp [Tctx.empty, RelCtx.lookup]
  have Hfund := fundamental Hty Δ [] HRel
  -- Hfund : ⊢ bin_log_related_ty ⊤ Δ [] e e τ
  --       = ⊢ ∀ vs, env_ltyped2 [] vs -∗ refines ⊤ (substMap vs.fst e) (substMap vs.snd e) ...
  -- Specialize at vs := [].
  unfold bin_log_related_ty bin_log_related at Hfund
  -- substMap [] e = e by `Exp.substMap_empty` (applied via ValSubstMap.{fst,snd} of []).
  have h1 : Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e = e := rfl
  have h2 : Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e = e := rfl
  ihave Hf := Hfund
  -- Goal `refines ⊤ e e (interp τ Δ)` is def-eq to
  -- `refines ⊤ (substMap [].fst e) (substMap [].snd e) (interp τ Δ)`.
  have hgoal_eq : (refines (⊤ : CoPset) e e (interp τ Δ) : IProp GF) =
      refines (⊤ : CoPset)
        (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e)
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e)
        (interp τ Δ) := rfl
  rw [hgoal_eq]
  iapply Hf $$ %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

end Fundamental

end ProbLang
