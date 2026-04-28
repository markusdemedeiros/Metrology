import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.AdequacyRel
import Metrology.Approxis.Interp
import Metrology.Approxis.Fundamental
import Metrology.ProbLang.ContextualRefinement

/-! # Soundness

Soundness of the logical relation w.r.t. contextual refinement (precongruence + closed/open soundness theorems). -/

namespace ProbLang

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

section Soundness
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

set_option maxHeartbeats 4000000 in

/-- Recursive predicate: K's binder atoms are pairwise distinct AND each is
fresh in Γrc.dom (and accumulated dom from outer binders). Used to close the
binder cases of `bin_log_related_under_typed_ctx`. -/
def Ctx.BindersFresh : Ctx → Finset Var → Prop
  | [], _ => True
  | k :: K', S =>
    (∀ x ∈ k.binderAtoms, x ∉ S) ∧
    Ctx.BindersFresh K' (S ∪ k.binderAtoms)

/-- Helper for the lam binder case of the precongruence. Given that the inner
context `K'` already produces related expressions at the extended `(x, A) :: Γrc'`,
plus typing of `K'.fill e`/`K'.fill e'` at `Γtc.insert x τ`, this lemma produces
the lam'd related expressions at `Γrc'`.

This is the key step that combines (a) `bin_log_related_lam` (cofinite-binder
introduction) with (b) `bin_log_related_ty_rename` (α-renaming the binder atom
from a fixed `x` to a cofinite `y`). -/
theorem bin_log_related_lam_step
    {Δ : TyEnv GF} {Γrc' : RelCtx GF} {x : Var} {τ_arg τ_body : Ty}
    {Ke Ke' : Exp}
    (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed)
    (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
      ((x, interp τ_arg Δ) :: Γrc') Ke Ke' τ_body) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc'
      (.lam (Ke.close x)) (.lam (Ke'.close x)) (.arrow τ_arg τ_body) := by
  have hInnerDom : (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset =
      (Γrc'.map (·.1)).toFinset ∪ {x} := by
    simp [List.map_cons, List.toFinset_cons, Finset.union_comm]
  -- Cofinite L for bin_log_related_lam: cover Γrc'.dom, x, Ke.fv, Ke'.fv.
  let L : Finset Var :=
    (Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv
  apply bin_log_related_lam Δ Γrc' L
  -- he_lc.
  · intro y _
    rw [Exp.open_close_subst_lc x y _ hKe_lc]
    exact Exp.subst_lc hKe_lc (Exp.IsLocallyClosed.fvar y)
  · intro y _
    rw [Exp.open_close_subst_lc x y _ hKe'_lc]
    exact Exp.subst_lc hKe'_lc (Exp.IsLocallyClosed.fvar y)
  -- he_fv: (close Ke x).fv ⊆ Γrc'.dom.
  · intro z hz
    have hzKe : z ∈ Ke.fv := Exp.close_fv_subset _ x hz
    have hzKeDom := hKe_fv hzKe
    rw [hInnerDom] at hzKeDom
    rcases Finset.mem_union.mp hzKeDom with hz_outer | hz_x
    · exact hz_outer
    · exfalso
      have hzx : z = x := Finset.mem_singleton.mp hz_x
      rw [hzx] at hz
      exact Exp.close_var_not_fvar x Ke hz
  · intro z hz
    have hzKe' : z ∈ Ke'.fv := Exp.close_fv_subset _ x hz
    have hzKe'Dom := hKe'_fv hzKe'
    rw [hInnerDom] at hzKe'Dom
    rcases Finset.mem_union.mp hzKe'Dom with hz_outer | hz_x
    · exact hz_outer
    · exfalso
      have hzx : z = x := Finset.mem_singleton.mp hz_x
      rw [hzx] at hz
      exact Exp.close_var_not_fvar x Ke' hz
  -- Hbody.
  intro y hyNotL
  have hyNotRc : y ∉ (Γrc'.map (·.1)).toFinset := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hyNotX : y ≠ x := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_singleton.mpr h))))
  have hyNotFvKe : y ∉ Ke.fv := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hyNotFvKe' : y ∉ Ke'.fv := fun h => hyNotL
    (Finset.mem_union_right _ h)
  -- Use bin_log_related_ty_rename to swap binder atom x → y.
  have hRename := bin_log_related_ty_rename (E := ⊤) (Δ := Δ) (Γ := Γrc')
    (x := x) (y := y) (A := interp τ_arg Δ)
    (τE := Ke) (τE' := Ke') (τ := τ_body)
    (Ne.symm hyNotX) hxRc hyNotRc hyNotFvKe hyNotFvKe'
  rw [Exp.open_close_subst_lc x y _ hKe_lc,
      Exp.open_close_subst_lc x y _ hKe'_lc]
  exact (BIBase.Entails.trans Hbody hRename)

/-- Helper for the fix binder case (same template as `bin_log_related_lam_step`,
applied to `bin_log_related_fix`). -/
theorem bin_log_related_fix_step
    {Δ : TyEnv GF} {Γrc' : RelCtx GF} {f : Var} {τ1 τ2 : Ty}
    {Ke Ke' : Exp}
    (hfRc : f ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed)
    (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
      ((f, interp (.arrow τ1 τ2) Δ) :: Γrc') Ke Ke' (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc'
      (.fix (Ke.close f)) (.fix (Ke'.close f)) (.arrow τ1 τ2) := by
  have hInnerDom : (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset =
      (Γrc'.map (·.1)).toFinset ∪ {f} := by
    simp [List.map_cons, List.toFinset_cons, Finset.union_comm]
  let L : Finset Var :=
    (Γrc'.map (·.1)).toFinset ∪ {f} ∪ Ke.fv ∪ Ke'.fv
  apply bin_log_related_fix Δ Γrc' L
  · intro y _
    rw [Exp.open_close_subst_lc f y _ hKe_lc]
    exact Exp.subst_lc hKe_lc (Exp.IsLocallyClosed.fvar y)
  · intro y _
    rw [Exp.open_close_subst_lc f y _ hKe'_lc]
    exact Exp.subst_lc hKe'_lc (Exp.IsLocallyClosed.fvar y)
  · intro z hz
    have hzKe : z ∈ Ke.fv := Exp.close_fv_subset _ f hz
    have hzKeDom := hKe_fv hzKe
    rw [hInnerDom] at hzKeDom
    rcases Finset.mem_union.mp hzKeDom with hz_outer | hz_x
    · exact hz_outer
    · exfalso
      have hzx : z = f := Finset.mem_singleton.mp hz_x
      rw [hzx] at hz
      exact Exp.close_var_not_fvar f Ke hz
  · intro z hz
    have hzKe' : z ∈ Ke'.fv := Exp.close_fv_subset _ f hz
    have hzKe'Dom := hKe'_fv hzKe'
    rw [hInnerDom] at hzKe'Dom
    rcases Finset.mem_union.mp hzKe'Dom with hz_outer | hz_x
    · exact hz_outer
    · exfalso
      have hzx : z = f := Finset.mem_singleton.mp hz_x
      rw [hzx] at hz
      exact Exp.close_var_not_fvar f Ke' hz
  intro y hyNotL
  have hyNotRc : y ∉ (Γrc'.map (·.1)).toFinset := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hyNotF : y ≠ f := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_singleton.mpr h))))
  have hyNotFvKe : y ∉ Ke.fv := fun h => hyNotL
    (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hyNotFvKe' : y ∉ Ke'.fv := fun h => hyNotL
    (Finset.mem_union_right _ h)
  have hRename := bin_log_related_ty_rename (E := ⊤) (Δ := Δ) (Γ := Γrc')
    (x := f) (y := y) (A := interp (.arrow τ1 τ2) Δ)
    (τE := Ke) (τE' := Ke') (τ := .arrow τ1 τ2)
    (Ne.symm hyNotF) hfRc hyNotRc hyNotFvKe hyNotFvKe'
  rw [Exp.open_close_subst_lc f y _ hKe_lc,
      Exp.open_close_subst_lc f y _ hKe'_lc]
  exact (BIBase.Entails.trans Hbody hRename)

/-- **Precongruence**: if `e ~ e'` at `(Γ, τ)` and `K` takes `(Γ, τ)` to
`(Γ', τ')`, then `K[e] ~ K[e']` at `(Γ', τ')`. The hypothesis is universal
in both `Δ` and the relational context (the latter via `TctxRelated`).
The `Hfresh` premise (`Ctx.BindersFresh`) asserts that K's binder atoms are
pairwise distinct and disjoint from the outer `Γrc'`. `Hty_e`/`Hty_e'` give
typing of the holes (used in binder cases to derive LC + fv-bounds on
`K'.fill e`/`K'.fill e'` via `TypedCtx.fill_typed`); `Hbinders` ensures the
context's binder atoms don't clash with `e.fv ∪ e'.fv ∪ payloadFv K`, also
needed for `TypedCtx.fill_typed`. -/
theorem bin_log_related_under_typed_ctx
    {Γtc : Tctx} {e e' : Exp} {τ : Ty} {Γtc' : Tctx} {τ' : Ty} {K : Ctx}
    (HK : TypedCtx K Γtc τ Γtc' τ')
    (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hbinders : ∀ x ∈ Ctx.binderAtoms K,
      x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K)
    (Hrel : ∀ (Δ : TyEnv GF) (Γrc : RelCtx GF),
      TctxRelated Δ Γtc Γrc →
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv GF) (Γrc' : RelCtx GF),
      TctxRelated Δ Γtc' Γrc' →
      Ctx.BindersFresh K (Γrc'.map (·.1)).toFinset →
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc' (K.fill e) (K.fill e') τ' := by
  induction K generalizing Γtc' τ' with
  | nil =>
    intro Δ Γrc HCtx _
    cases HK
    exact Hrel Δ Γrc HCtx
  | cons k K' ih =>
    intro Δ Γrc' HCtx Hfresh
    cases HK with
    | @cons _ _ _ _ Γ2 τ2 _ _ HKitem HKtail =>
    obtain ⟨HfreshHead, HfreshTail⟩ := Hfresh
    -- Restrict the global binder-freshness premise to K'.
    have HbindersK' : ∀ x ∈ Ctx.binderAtoms K',
        x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K' := by
      intro x hxK'
      have hxK : x ∈ Ctx.binderAtoms (k :: K') := by
        simp [Ctx.binderAtoms, Finset.mem_union]; exact Or.inr hxK'
      obtain ⟨h1, h2, h3⟩ := Hbinders x hxK
      refine ⟨h1, h2, ?_⟩
      intro hPay
      apply h3
      simp [Ctx.payloadFv, Finset.mem_union]; exact Or.inr hPay
    have IHinner := fun Γrc_inner => ih HKtail HbindersK' Δ Γrc_inner
    simp only [Ctx.fill_cons]
    cases HKitem with
    | @appL Γ e2 τα τβ Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_app $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @appR Γ e1 τα τβ Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_app $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @pairL Γ e2 τα τβ Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_pair $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @pairR Γ e1 τα τβ Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_pair $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @fst Γ τα τβ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply bin_log_related_fst $$ [IHk']
      iexact IHk'
    | @snd Γ τα τβ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply bin_log_related_snd $$ [IHk']
      iexact IHk'
    | @inl Γ τα τβ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply bin_log_related_injl $$ [IHk']
      iexact IHk'
    | @inr Γ τα τβ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply bin_log_related_injr $$ [IHk']
      iexact IHk'
    | @caseL Γ e1 e2 τ1' τ2' τr Hty1 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH1' := IH1
      ihave IH2' := IH2
      iapply bin_log_related_case $$ [IHk' IH1' IH2']
      · iexact IHk'
      · iexact IH1'
      iexact IH2'
    | @caseM Γ e0 e2 τ1' τ2' τr Hty0 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH0 := fundamental Hty0 Δ Γrc' HCtx
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IH0' := IH0
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_case $$ [IH0' IHk' IH2']
      · iexact IH0'
      · iexact IHk'
      iexact IH2'
    | @caseR Γ e0 e1 τ1' τ2' τr Hty0 Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH0 := fundamental Hty0 Δ Γrc' HCtx
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH0' := IH0
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_case $$ [IH0' IH1' IHk']
      · iexact IH0'
      · iexact IH1'
      iexact IHk'
    | @ifL Γ e1 e2 τr Hty1 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH1' := IH1
      ihave IH2' := IH2
      iapply bin_log_related_if $$ [IHk' IH1' IH2']
      · iexact IHk'
      · iexact IH1'
      iexact IH2'
    | @ifM Γ e0 e2 τr Hty0 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH0 := fundamental Hty0 Δ Γrc' HCtx
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IH0' := IH0
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_if $$ [IH0' IHk' IH2']
      · iexact IH0'
      · iexact IHk'
      iexact IH2'
    | @ifR Γ e0 e1 τr Hty0 Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH0 := fundamental Hty0 Δ Γrc' HCtx
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH0' := IH0
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_if $$ [IH0' IH1' IHk']
      · iexact IH0'
      · iexact IH1'
      iexact IHk'
    | @alloc Γ τα =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_alloc Δ Γrc') $$ [IHk']
      iexact IHk'
    | @load Γ τα =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_load Δ Γrc') $$ [IHk']
      iexact IHk'
    | @storeL Γ e2 τα Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_store $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @storeR Γ e1 τα Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_store $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @allocTape Γ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply bin_log_related_alloctape $$ [IHk']
      iexact IHk'
    | @randL_unit Γ e2 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_rand_unit $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @randL_tape Γ e2 Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply bin_log_related_rand_tape $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @randR_unit Γ e1 Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_rand_unit $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @randR_tape Γ e1 Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply bin_log_related_rand_tape $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @unop_int Γ op τα Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_int_unop Δ Γrc' op Hres) $$ [IHk']
      iexact IHk'
    | @unop_bool Γ op τα Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_bool_unop Δ Γrc' op Hres) $$ [IHk']
      iexact IHk'
    | @binopL_int Γ op e2 τα Hty2 Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply (bin_log_related_int_binop Δ Γrc' op Hres) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @binopR_int Γ op e1 τα Hty1 Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply (bin_log_related_int_binop Δ Γrc' op Hres) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @binopL_bool Γ op e2 τα Hty2 Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply (bin_log_related_bool_binop Δ Γrc' op Hres) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @binopR_bool Γ op e1 τα Hty1 Hres =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply (bin_log_related_bool_binop Δ Γrc' op Hres) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @binopL_unboxedEq Γ e2 τα Hub Hty2 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH2 := fundamental Hty2 Δ Γrc' HCtx
      iintro
      ihave IHk' := IHk
      ihave IH2' := IH2
      iapply (bin_log_related_unboxed_eq Δ Γrc' Hub) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @binopR_unboxedEq Γ e1 τα Hub Hty1 =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      have IH1 := fundamental Hty1 Δ Γrc' HCtx
      iintro
      ihave IH1' := IH1
      ihave IHk' := IHk
      iapply (bin_log_related_unboxed_eq Δ Γrc' Hub) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @fold Γ τα =>
      -- CtxItem.fold is subsumption: k.fill e = e.
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_fold Δ Γrc') $$ [IHk']
      iexact IHk'
    | @unfold Γ τα =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_unfold Δ Γrc') $$ [IHk']
      iexact IHk'
    | @tapp Γ τα τβ =>
      simp only [CtxItem.fill]
      have IHk := IHinner Γrc' HCtx (by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail)
      iintro
      ihave IHk' := IHk
      iapply (bin_log_related_tapp Δ Γrc') $$ [IHk']
      iexact IHk'
    -- Binder cases. The architecture for `lam` is documented in soundness_port_status.md:
    -- - rename_i to bind atom and types from cases
    -- - extract HfreshHead / HfreshTail from BindersFresh.cons
    -- - apply IH at extended Γrc to get bin_log_related at the binder atom
    -- - apply `bin_log_related_lam` with cofinite L, transporting each fresh-atom
    --   instance via `bin_log_related_rename` (proven in Interp.lean).
    -- The full proof additionally needs LC and fv-bounds on K'.fill e / e' as
    -- preconditions to the precongruence (typically derived from typing).
    | @lam Γ x τ τ' =>
      simp only [CtxItem.fill]
      -- After cases: x : Var (binder atom), τ : Ty (binder type),
      -- τ2 : Ty (body type), Γtc' : Tctx (outer typing ctx).
      have hHeadAtom : x ∈ (CtxItem.lam x).binderAtoms := by
        simp [CtxItem.binderAtoms]
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset := HfreshHead x hHeadAtom
      -- Inner Γrc := (x, interp τ Δ) :: Γrc'; well-formed since x ∉ Γrc'.dom.
      have hxRcLookup : Γrc'.lookup x = none := by
        cases hRc : Γrc'.lookup x with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc'.lookup x).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hxRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      have HCtxInner : TctxRelated Δ (Γtc'.insert x τ) ((x, interp τ Δ) :: Γrc') :=
        HCtx.insert x τ hxRcLookup
      -- HfreshTail in extended dom: dom of (x,_)::Γrc' = Γrc'.dom ∪ {x}.
      have hInnerDom : (((x, interp τ Δ) :: Γrc').map (·.1)).toFinset =
          (Γrc'.map (·.1)).toFinset ∪ {x} := by
        simp [List.map_cons, List.toFinset_cons, Finset.union_comm]
      have HfreshK'Inner : Ctx.BindersFresh K'
          (((x, interp τ Δ) :: Γrc').map (·.1)).toFinset := by
        rw [hInnerDom]
        simp only [CtxItem.binderAtoms] at HfreshTail
        exact HfreshTail
      have IHk_at_x := IHinner ((x, interp τ Δ) :: Γrc') HCtxInner HfreshK'Inner
      -- Typing of K'.fill e / e' at (Γtc'.insert x τ, τ2).
      have HbindersK'_e : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).1, (HbindersK' y hy).2.2⟩
      have HbindersK'_e' : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e'.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).2.1, (HbindersK' y hy).2.2⟩
      have HtyKfe : Typed (Γtc'.insert x τ) (Ctx.fill K' e) τ2 :=
        TypedCtx.fill_typed Hty_e HKtail HbindersK'_e
      have HtyKfe' : Typed (Γtc'.insert x τ) (Ctx.fill K' e') τ2 :=
        TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e'
      have hKfe_lc : (Ctx.fill K' e).IsLocallyClosed := HtyKfe.isLocallyClosed
      have hKfe'_lc : (Ctx.fill K' e').IsLocallyClosed := HtyKfe'.isLocallyClosed
      have hKfe_fv : (Ctx.fill K' e).fv ⊆ (((x, interp τ Δ) :: Γrc').map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxInner HtyKfe
      have hKfe'_fv : (Ctx.fill K' e').fv ⊆ (((x, interp τ Δ) :: Γrc').map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxInner HtyKfe'
      exact bin_log_related_lam_step (Δ := Δ) (Γrc' := Γrc')
        (x := x) (τ_arg := τ) (τ_body := τ2)
        hxRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv IHk_at_x
    | @fix Γ f τ τ' =>
      simp only [CtxItem.fill]
      -- After cases, names exposed: f : Var (binder atom), τ τ' : Ty (the τ τ' of the
      -- fix binder, which is .arrow τ τ' in the type). Γtc' is unified with Γ.
      -- HfreshHead: f ∉ Γrc'.dom.
      have hHeadAtom : f ∈ (CtxItem.fix f).binderAtoms := by
        simp [CtxItem.binderAtoms]
      have hfRc : f ∉ (Γrc'.map (·.1)).toFinset := HfreshHead f hHeadAtom
      have hfRcLookup : Γrc'.lookup f = none := by
        cases hRc : Γrc'.lookup f with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc'.lookup f).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hfRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      -- Inner Γrc := (f, interp (.arrow τ τ') Δ) :: Γrc'.
      have HCtxInner : TctxRelated Δ (Γtc'.insert f (.arrow τ τ'))
          ((f, interp (.arrow τ τ') Δ) :: Γrc') :=
        HCtx.insert f (.arrow τ τ') hfRcLookup
      have hInnerDom : (((f, interp (.arrow τ τ') Δ) :: Γrc').map (·.1)).toFinset =
          (Γrc'.map (·.1)).toFinset ∪ {f} := by
        simp [List.map_cons, List.toFinset_cons, Finset.union_comm]
      have HfreshK'Inner : Ctx.BindersFresh K'
          (((f, interp (.arrow τ τ') Δ) :: Γrc').map (·.1)).toFinset := by
        rw [hInnerDom]
        simp only [CtxItem.binderAtoms] at HfreshTail
        exact HfreshTail
      have IHk_at_f := IHinner ((f, interp (.arrow τ τ') Δ) :: Γrc')
        HCtxInner HfreshK'Inner
      have HbindersK'_e : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).1, (HbindersK' y hy).2.2⟩
      have HbindersK'_e' : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e'.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).2.1, (HbindersK' y hy).2.2⟩
      have HtyKfe : Typed (Γtc'.insert f (.arrow τ τ')) (Ctx.fill K' e) (.arrow τ τ') :=
        TypedCtx.fill_typed Hty_e HKtail HbindersK'_e
      have HtyKfe' : Typed (Γtc'.insert f (.arrow τ τ')) (Ctx.fill K' e') (.arrow τ τ') :=
        TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e'
      have hKfe_lc : (Ctx.fill K' e).IsLocallyClosed := HtyKfe.isLocallyClosed
      have hKfe'_lc : (Ctx.fill K' e').IsLocallyClosed := HtyKfe'.isLocallyClosed
      have hKfe_fv : (Ctx.fill K' e).fv ⊆
          (((f, interp (.arrow τ τ') Δ) :: Γrc').map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxInner HtyKfe
      have hKfe'_fv : (Ctx.fill K' e').fv ⊆
          (((f, interp (.arrow τ τ') Δ) :: Γrc').map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxInner HtyKfe'
      exact bin_log_related_fix_step (Δ := Δ) (Γrc' := Γrc')
        (f := f) (τ1 := τ) (τ2 := τ')
        hfRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv IHk_at_f
    | tlam =>
      simp only [CtxItem.fill]
      -- After cases: τ2 : Ty (the body type), Γtc' : Tctx (outer = inner outer).
      -- HfreshTail with empty binderAtoms.
      have HfreshK'Outer : Ctx.BindersFresh K' (Γrc'.map (·.1)).toFinset := by
        simp only [CtxItem.binderAtoms, Finset.union_empty] at HfreshTail
        exact HfreshTail
      have HbindersK'_e : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).1, (HbindersK' y hy).2.2⟩
      have HbindersK'_e' : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e'.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).2.1, (HbindersK' y hy).2.2⟩
      have HtyKfe := TypedCtx.fill_typed Hty_e HKtail HbindersK'_e
      have HtyKfe' := TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e'
      have hKfe_lc : (Ctx.fill K' e).IsLocallyClosed := HtyKfe.isLocallyClosed
      have hKfe'_lc : (Ctx.fill K' e').IsLocallyClosed := HtyKfe'.isLocallyClosed
      have HCtxShift := HCtx.shift (default : lrel GF)
      have hKfe_fv : (Ctx.fill K' e).fv ⊆ (Γrc'.map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxShift HtyKfe
      have hKfe'_fv : (Ctx.fill K' e').fv ⊆ (Γrc'.map (·.1)).toFinset :=
        fv_subset_relCtxDom HCtxShift HtyKfe'
      apply bin_log_related_tlam Δ Γrc' hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv
      intro A
      have HCtxShiftA := HCtx.shift A
      have IHk_at_A := ih HKtail HbindersK' (TyEnv.cons A Δ) Γrc'
        HCtxShiftA HfreshK'Outer
      iintro
      imodintro
      ihave Hf := IHk_at_A
      iexact Hf
    | unpackL =>
      simp only [CtxItem.fill]
      next e2 τ_pkg hxFvE2 Hty_e2 =>
      rename_i x  -- the binder atom (inaccessible: from `.unpackL x e2`).
      -- HfreshHead: x ∉ Γrc'.dom (binderAtoms = {x}).
      have hHeadAtom : x ∈ (CtxItem.unpackL x e2).binderAtoms := by
        simp [CtxItem.binderAtoms]
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset := HfreshHead x hHeadAtom
      -- HIH1: related scrutinees at .exists' τ_pkg.
      -- Inner application of IHinner needs BindersFresh K' Γrc'.dom (since
      -- after unpackL, K's binder atoms shift to {x} ∪ inner). Looking at
      -- HfreshTail: BindersFresh K' (Γrc'.dom ∪ {x}). To use the IH at Γrc'
      -- (same outer dom), we need K' freshness against Γrc'.dom — strictly
      -- weaker, so it just follows from HfreshTail by monotonicity.
      have HfreshK'Outer : Ctx.BindersFresh K' (Γrc'.map (·.1)).toFinset := by
        -- Build a generic monotonicity lemma inline.
        have mono : ∀ {K0 : Ctx} {S T : Finset Var},
            S ⊆ T → Ctx.BindersFresh K0 T → Ctx.BindersFresh K0 S := by
          intro K0
          induction K0 with
          | nil => intros; trivial
          | cons k0 K0' ihK =>
            intro S T hST h
            obtain ⟨h1, h2⟩ := h
            refine ⟨fun y hy hyS => h1 y hy (hST hyS), ?_⟩
            exact ihK (Finset.union_subset_union hST Finset.Subset.rfl) h2
        exact mono Finset.subset_union_left HfreshTail
      have HIH1 := IHinner Γrc' HCtx HfreshK'Outer
      -- HIH2: for any A, any fresh y, fundamental applied to rename_unpack typing.
      let L : Finset Var := insert x e2.fv ∪ (Γrc'.map (·.1)).toFinset
      apply bin_log_related_unpack Δ Γrc' L HIH1
      intro A y hyL
      have hyFresh : y ∉ insert x e2.fv := fun h => hyL (Finset.mem_union_left _ h)
      have hyNotInDom : y ∉ (Γrc'.map (·.1)).toFinset :=
        fun h => hyL (Finset.mem_union_right _ h)
      have HtyRen := Typed.rename_unpack hxFvE2 Hty_e2 y hyFresh
      have hyRcLookup : Γrc'.lookup y = none := by
        cases hRc : Γrc'.lookup y with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc'.lookup y).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hyNotInDom
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      have HCtxShiftA := HCtx.shift A
      have HCtxIns : TctxRelated (TyEnv.cons A Δ) ((Γtc'.shift).insert y τ_pkg)
          ((y, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') :=
        HCtxShiftA.insert y τ_pkg hyRcLookup
      exact fundamental HtyRen (TyEnv.cons A Δ) _ HCtxIns
    | unpackR =>
      simp only [CtxItem.fill]
      next e1 τ_pkg Hty_e1 =>
      rename_i x  -- inaccessible binder atom from `.unpackR x e1`.
      have hHeadAtom : x ∈ (CtxItem.unpackR x e1).binderAtoms := by
        simp [CtxItem.binderAtoms]
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset := HfreshHead x hHeadAtom
      have hxRcLookup : Γrc'.lookup x = none := by
        cases hRc : Γrc'.lookup x with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc'.lookup x).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hxRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      -- HIH1: e1 ~ e1 at .exists' τ_pkg (via fundamental on the payload typing).
      have HIH1 := fundamental Hty_e1 Δ Γrc' HCtx
      -- HfreshTail in extended dom: dom of (x,_)::Γrc' = Γrc'.dom ∪ {x}.
      have hInnerDom : ∀ (A' : lrel GF),
          (((x, interp τ_pkg (TyEnv.cons A' Δ)) :: Γrc').map (·.1)).toFinset =
          (Γrc'.map (·.1)).toFinset ∪ {x} := by
        intro A'
        simp [List.map_cons, List.toFinset_cons, Finset.union_comm]
      -- Typing of K'.fill e and K'.fill e' at ((Γtc'.shift).insert x τ_pkg, τ_body).
      -- τ_body unifies with the inner τ2 (body type of cons match). After cases,
      -- the inner ctx is unified with `(Γ.shift).insert x τ` and inner τ2 with τ2.shift.
      have HbindersK'_e : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).1, (HbindersK' y hy).2.2⟩
      have HbindersK'_e' : ∀ y ∈ Ctx.binderAtoms K',
          y ∉ e'.fv ∧ y ∉ Ctx.payloadFv K' :=
        fun y hy => ⟨(HbindersK' y hy).2.1, (HbindersK' y hy).2.2⟩
      have HtyKfe := TypedCtx.fill_typed Hty_e HKtail HbindersK'_e
      have HtyKfe' := TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e'
      have hKfe_lc : (Ctx.fill K' e).IsLocallyClosed := HtyKfe.isLocallyClosed
      have hKfe'_lc : (Ctx.fill K' e').IsLocallyClosed := HtyKfe'.isLocallyClosed
      let L : Finset Var := (Γrc'.map (·.1)).toFinset ∪ {x} ∪
        (Ctx.fill K' e).fv ∪ (Ctx.fill K' e').fv
      apply bin_log_related_unpack Δ Γrc' L HIH1
      intro A y hyL
      have hyNotRc : y ∉ (Γrc'.map (·.1)).toFinset := fun h => hyL
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hyNotX : y ≠ x := fun h => hyL
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_singleton.mpr h))))
      have hyNotFvKfe : y ∉ (Ctx.fill K' e).fv := fun h => hyL
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hyNotFvKfe' : y ∉ (Ctx.fill K' e').fv := fun h => hyL
        (Finset.mem_union_right _ h)
      have hyRcLookup : Γrc'.lookup y = none := by
        cases hRc : Γrc'.lookup y with
        | none => rfl
        | some _ =>
          exfalso
          have hsome : (Γrc'.lookup y).isSome := by rw [hRc]; rfl
          obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
          apply hyNotRc
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hpmem, hpeq⟩
      -- IH at (cons A Δ, ((x, interp τ_pkg (cons A Δ)) :: Γrc')).
      have HCtxShiftA := HCtx.shift A
      have HCtxIns : TctxRelated (TyEnv.cons A Δ) ((Γtc'.shift).insert x τ_pkg)
          ((x, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') :=
        HCtxShiftA.insert x τ_pkg hxRcLookup
      have HfreshK'Inner : Ctx.BindersFresh K'
          (((x, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc').map (·.1)).toFinset := by
        rw [hInnerDom A]
        simp only [CtxItem.binderAtoms] at HfreshTail
        exact HfreshTail
      have IHk_at_x := ih HKtail HbindersK' (TyEnv.cons A Δ)
        ((x, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') HCtxIns HfreshK'Inner
      -- α-rename binder atom from x to y.
      have hRename := bin_log_related_ty_rename
        (E := ⊤) (Δ := TyEnv.cons A Δ) (Γ := Γrc')
        (x := x) (y := y) (A := interp τ_pkg (TyEnv.cons A Δ))
        (τE := Ctx.fill K' e) (τE' := Ctx.fill K' e') (τ := Ty.shift τ')
        (Ne.symm hyNotX) hxRc hyNotRc hyNotFvKfe hyNotFvKfe'
      rw [Exp.open_close_subst_lc x y _ hKfe_lc,
          Exp.open_close_subst_lc x y _ hKfe'_lc]
      exact (BIBase.Entails.trans IHk_at_x hRename)

end Soundness

section RefinesSound
open MeasureTheory
variable {GF : BundledGFunctors}
  [AppPreGS GF] [SpecPreGS GF] [ECPreGS GF] [InvGpreS GF] [NaInvG GF]

/-- The bool-equality value relation extracted from `lrel_bool`. -/
def boolEqVal (v v' : Val) : Prop :=
  ∃ b : Bool, v.1 = .lit (.bool b) ∧ v'.1 = .lit (.bool b)

omit [AppPreGS GF] [SpecPreGS GF] [ECPreGS GF] [InvGpreS GF] [NaInvG GF] in
/-- `lrel_bool` extracts purely to `boolEqVal`. -/
theorem lrel_bool_to_boolEqVal [ApproxisRGS false GF] (v v' : Val) :
    ⊢@{IProp GF} iprop((lrel_bool (GF := GF)).car v v' -∗ ⌜boolEqVal v v'⌝) := by
  iintro Hbool
  ihave ⟨%b, %h⟩ := lrel_bool_unfold v v' $$ Hbool
  ipure_intro
  exact ⟨b, h.1, h.2⟩

/-- Set-level monotonicity from `AddCoupl 0`: if `S(a, b) → a ∈ T → b ∈ T'`, then
`μₗ T ≤ μᵣ T'`. Specialization tactic, not yet a standalone lemma. -/
theorem AddCoupl.set_leq_zero {α β} [MeasurableSpace α] [MeasurableSpace β]
    {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    {T : Set α} {T' : Set β}
    (hT : MeasurableSet T) (hT' : MeasurableSet T')
    (Hcpl : AddCoupl 0 S μₗ μᵣ)
    (Himp : ∀ a b, S (a, b) → a ∈ T → b ∈ T') :
    μₗ T ≤ μᵣ T' := by
  classical
  let fInd : CouplingFunction α :=
    .mk (T.indicator (fun _ => 1))
        ⟨measurable_const.indicator hT,
         fun x => Set.indicator_le_self _ _ x⟩
  let gInd : CouplingFunction β :=
    .mk (T'.indicator (fun _ => 1))
        ⟨measurable_const.indicator hT',
         fun x => Set.indicator_le_self _ _ x⟩
  have hCmp : ∀ a b, S (a, b) → fInd.1 a ≤ gInd.1 b := by
    intro a b hS
    by_cases ha : a ∈ T
    · have hb : b ∈ T' := Himp a b hS ha
      simp [fInd, gInd, Set.indicator_of_mem ha, Set.indicator_of_mem hb]
    · simp [fInd, Set.indicator_of_notMem ha]
  have hMain := Hcpl fInd gInd (fun {a b} hS => hCmp a b hS)
  simp only [add_zero] at hMain
  rw [show (∫⁻ x, fInd.1 x ∂μₗ) = μₗ T by
        simp [fInd, MeasureTheory.lintegral_indicator hT, lintegral_const,
              MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter],
      show (∫⁻ x, gInd.1 x ∂μᵣ) = μᵣ T' by
        simp [gInd, MeasureTheory.lintegral_indicator hT', lintegral_const,
              MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]] at hMain
  exact hMain

/-- **Soundness of the logical relation w.r.t. contextual refinement (open),
restricted to fresh contexts.**

If `e` and `e'` are logically related at every `Δ`-extension of every relational
context lifted from `Γtc` (parametric in the model `IR`), then `e` contextually
refines `e'` at type `τ`, *restricted to closing contexts whose binder atoms
are pairwise distinct*. The freshness restriction is a technical artifact of
the LN encoding (Rocq's BVar-based contexts don't need it); in principle the
unrestricted version follows by alpha-renaming, which is not yet ported.

Also requires typing of `e`, `e'`, and that `K`'s binder atoms are fresh
in `e.fv ∪ e'.fv ∪ payloadFv K`. -/
theorem refines_sound_open_fresh
    (Γtc : Tctx) (e e' : Exp) (τ : Ty)
    (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS false GF) (Δ : TyEnv GF) (Γrc : RelCtx GF),
      TctxRelated Δ Γtc Γrc →
      ⊢@{IProp GF} bin_log_related_ty (hlc := false) (GF := GF)
        (⊤ : CoPset) Δ Γrc e e' τ) :
    ∀ (K : Ctx) (σ₀ : State) (b : Bool),
      TypedCtx K Γtc τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K,
        x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  intro K σ₀ b Htyped HfreshK Hbinders
  -- Bridge limExec on `finalBool b ⊆ Cfg` to its `(·.expr)` projection at `{.lit (.bool b)}`.
  have hRewriteFb : ∀ (e0 : Exp),
      limExec ⟨e0, σ₀⟩ (finalBool b) =
      ((limExec ⟨e0, σ₀⟩).map (·.expr)) {.lit (.bool b)} := by
    intro e0
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
    rfl
  rw [hRewriteFb (K.fill e), hRewriteFb (K.fill e')]
  -- Apply refines_coupling to get an AddCoupl 0 between projected limExec.
  have hCpl :
      AddCoupl 0 (adequacyRel boolEqVal)
        ((limExec ⟨K.fill e,  σ₀⟩).map (·.expr))
        ((limExec ⟨K.fill e', σ₀⟩).map (·.expr)) := by
    apply refines_coupling (GF := GF) (A := fun _ => lrel_bool) (φ := boolEqVal)
    · intro IR v v'
      have := IR  -- bring into scope for instance synthesis
      exact lrel_bool_to_boolEqVal v v'
    · intro IR
      -- bin_log_related_under_typed_ctx (with Γrc' = []) lifts Hlog through K.
      -- Then specialize at vs = [] to land in `refines`.
      have HRel : TctxRelated (default : TyEnv GF) Tctx.empty ([] : RelCtx GF) := by
        intro x; simp [Tctx.empty, RelCtx.lookup]
      have HrelClosed :
          ⊢@{IProp GF}
            bin_log_related_ty (⊤ : CoPset) (default : TyEnv GF) []
              (K.fill e) (K.fill e') .bool := by
        apply bin_log_related_under_typed_ctx Htyped Hty_e Hty_e' Hbinders
        · intro Δ Γrc HCtx; exact Hlog IR Δ Γrc HCtx
        · exact HRel
        · exact HfreshK
      -- Specialize at vs := []; substMap [] e = e (def-eq via fst/snd of []).
      unfold bin_log_related_ty bin_log_related at HrelClosed
      have hgoal_eq : (refines (⊤ : CoPset) (K.fill e) (K.fill e')
            (lrel_bool (GF := GF)) : IProp GF) =
          refines (⊤ : CoPset)
            (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap)) (K.fill e))
            (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap)) (K.fill e'))
            (interp Ty.bool (default : TyEnv GF)) := rfl
      rw [hgoal_eq]
      ihave Hf := HrelClosed
      iapply Hf $$ %([] : ValSubstMap)
      iapply env_ltyped2_empty
  -- Now apply set_leq_zero with T = T' = {.lit (.bool b)}.
  apply AddCoupl.set_leq_zero (MeasurableSet.singleton _) (MeasurableSet.singleton _) hCpl
  rintro a b' ⟨v, v', hv, hv', ⟨b'', hvb1, hvb2⟩⟩ ha
  -- ha : a ∈ {.lit (.bool b)}, so a = .lit (.bool b).
  have haEq : a = .lit (.bool b) := ha
  -- From e.toVal? = some v, derive e = v.1 (via the def of toVal?).
  have toVal?_to_eq : ∀ {e : Exp} {w : Val}, e.toVal? = some w → e = w.1 := by
    intro e w he
    unfold Exp.toVal? at he
    split at he
    · -- IsVal.check? e = some k branch: he : some ⟨e, k⟩ = some w, so w.1 = e.
      rename_i k _
      have := Option.some.inj he
      rw [← this]
    · -- IsVal.check? e = none branch: he : none = some w, contradiction.
      cases he
  have hav : a = v.1 := toVal?_to_eq hv
  have hbv : b' = v'.1 := toVal?_to_eq hv'
  -- v.1 = a = .lit (.bool b), and v.1 = .lit (.bool b''), so b = b''.
  have hvbeq : v.1 = .lit (.bool b) := hav ▸ haEq
  rw [hvbeq] at hvb1
  -- hvb1 : .lit (.bool b) = .lit (.bool b''); subst the bool equality.
  injection hvb1 with hbool
  injection hbool with hbb
  subst hbb
  -- v'.1 = .lit (.bool b), and b' = v'.1.
  show b' ∈ ({.lit (.bool b)} : Set Exp)
  show b' = .lit (.bool b)
  rw [hbv, hvb2]

/-- **Soundness of the logical relation (closed case), restricted to fresh contexts.** -/
theorem refines_sound_fresh (e e' : Exp) (τ : Ty)
    (Hty_e : Typed Tctx.empty e τ) (Hty_e' : Typed Tctx.empty e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS false GF) (Δ : TyEnv GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF)
        (⊤ : CoPset) e e' (interp τ Δ)) :
    ∀ (K : Ctx) (σ₀ : State) (b : Bool),
      TypedCtx K Tctx.empty τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K,
        x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  apply refines_sound_open_fresh (GF := GF) Tctx.empty e e' τ Hty_e Hty_e'
  intro IR Δ Γrc HCtx
  -- HCtx : TctxRelated Δ Tctx.empty Γrc, i.e. ∀ x, (Tctx.empty x).map _ = Γrc.lookup x.
  -- Since Tctx.empty x = none, get Γrc.lookup x = none for all x; force Γrc = [].
  have hΓrcEmpty : Γrc = [] := by
    cases Γrc with
    | nil => rfl
    | cons p rest =>
      exfalso
      have h := HCtx p.1
      simp [Tctx.empty] at h
      -- h : Γrc.lookup p.1 = none, but for cons it's some _.
      simp only [RelCtx.lookup] at h
      cases hr : RelCtx.lookup rest p.1 with
      | some _ => rw [hr] at h; cases h
      | none => rw [hr] at h; simp at h
  subst hΓrcEmpty
  unfold bin_log_related_ty bin_log_related
  iintro %vs Hvs
  ihave Hvs_eq := env_ltyped2_empty_inv vs $$ Hvs
  -- Hvs_eq : ⌜vs = []⌝; rewrite vs to [] then substMap [] e = e.
  icases Hvs_eq with %hvs_nil
  rw [hvs_nil]
  -- Goal: refines ⊤ (substMap [].fst e) (substMap [].snd e') (interp τ Δ).
  -- This is def-eq to refines ⊤ e e' (interp τ Δ).
  have hgoal_eq : (refines (⊤ : CoPset) e e' (interp τ Δ) : IProp GF) =
      refines (⊤ : CoPset)
        (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap)) e)
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap)) e')
        (interp τ Δ) := rfl
  rw [← hgoal_eq]
  ihave Hl := Hlog IR Δ
  iexact Hl

end RefinesSound

end ProbLang
