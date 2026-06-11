module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.Model
public import Metrology.Approxis.AdequacyRel
public import Metrology.Approxis.Interp
public import Metrology.Approxis.Fundamental
public import Metrology.ProbLang.ContextualRefinement

@[expose] public section

set_option linter.discrete false

/-! # Soundness

Soundness of the logical relation w.r.t. contextual refinement (precongruence + closed/open soundness theorems). -/

namespace ProbLang

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS


section Soundness
variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- Recursive predicate: K's binder atoms are pairwise distinct AND each is
fresh in Γrc.dom (and accumulated dom from outer binders). Used to close the
binder cases of `bin_log_related_under_typed_ctx`. -/
def Ctx.BindersFresh : Ctx rT → Finset Var → Prop
  | [], _ => True
  | k :: K', S =>
    (∀ x ∈ k.binderAtoms, x ∉ S) ∧
    Ctx.BindersFresh K' (S ∪ k.binderAtoms)

omit [Countable rT] [MeasurableSingletonClass rT] in
/-- If a `CtxItem`'s binder atoms are empty, the freshness predicate at the
extended union reduces to freshness at the original set. -/
theorem Ctx.BindersFresh.cast_no_binder
    {K' : Ctx rT} {S : Finset Var} {bAtoms : Finset Var}
    (hEmpty : bAtoms = ∅)
    (h : Ctx.BindersFresh K' (S ∪ bAtoms)) :
    Ctx.BindersFresh K' S :=
  Finset.union_empty S ▸ hEmpty ▸ h

omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Anti-monotonicity in the freshness set: if `K`'s binders are fresh in a
larger set `T`, they're fresh in any subset `S ⊆ T`. -/
theorem Ctx.BindersFresh.mono {K : Ctx rT} {S T : Finset Var}
    (hST : S ⊆ T) (h : Ctx.BindersFresh K T) : Ctx.BindersFresh K S := by
  induction K generalizing S T with
  | nil => trivial
  | cons k K' ih =>
    exact ⟨fun y hy hyS => h.1 y hy (hST hyS),
           ih (Finset.union_subset_union hST Finset.Subset.rfl) h.2⟩

omit [Countable rT] [MeasurableSingletonClass rT] in
/-- The `Hbinders` precongruence premise restricts to the tail context `K'`
when shedding the head item `k`. -/
theorem binders_tail
    {k : CtxItem rT} {K' : Ctx rT} {e e' : Exp rT}
    (Hb : ∀ x ∈ Ctx.binderAtoms (k :: K'),
      x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv (k :: K')) :
    ∀ x ∈ Ctx.binderAtoms K',
      x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K' := by
  intro x hxK'
  have hxK : x ∈ Ctx.binderAtoms (k :: K') := Finset.mem_union_right _ hxK'
  obtain ⟨h1, h2, h3⟩ := Hb x hxK
  refine ⟨h1, h2, fun hPay => h3 (Finset.mem_union_right _ hPay)⟩

/-- The empty typing context relates to the empty relational context at any
type environment. -/
theorem TctxRelated.empty_nil {Δ : TyEnv rT GF} :
    TctxRelated Δ Tctx.empty ([] : RelCtx rT GF) := by
  intro x; simp [Tctx.empty, RelCtx.lookup]

/-- A relational context related to the empty typing context is itself empty. -/
theorem TctxRelated.eq_nil_of_empty {Δ : TyEnv rT GF} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Tctx.empty Γrc) : Γrc = [] := by
  cases Γrc with
  | nil => rfl
  | cons p rest =>
    exfalso
    have h := HCtx p.1
    simp [Tctx.empty, RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest p.1 with
    | some _ => rw [hr] at h; cases h
    | none => rw [hr] at h; simp at h

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
/-- A name not in the relational context's domain has no lookup result. -/
theorem RelCtx.lookup_eq_none_of_notMem
    {Γrc : RelCtx rT GF} {x : Var}
    (hxRc : x ∉ (Γrc.map (·.1)).toFinset) :
    Γrc.lookup x = none := by
  cases hRc : Γrc.lookup x with
  | none => rfl
  | some _ =>
    have hsome : (Γrc.lookup x).isSome := by rw [hRc]; rfl
    obtain ⟨p, hpmem, hpeq⟩ := RelCtx.exists_mem_of_lookup_isSome hsome
    exact absurd (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hpmem, hpeq⟩)) hxRc

/-- Bundle the typing/LC/fv-bound facts for a context-filled expression.
Used by the `lam`, `fix`, and `unpackR` cases to package what
`bin_log_related_*_step` expects from `K'.fill e` and `K'.fill e'`. -/
theorem ctx_fill_lc_fv
    {Γtc : Tctx} {Γrc : RelCtx rT GF} {Δ : TyEnv rT GF} {K : Ctx rT} {e : Exp rT} {τ : Ty}
    (HCtxRel : TctxRelated Δ Γtc Γrc)
    (Hty : Typed Γtc (K.fill e) τ) :
    (K.fill e).IsLocallyClosed ∧ (K.fill e).fv ⊆ (Γrc.map (·.1)).toFinset :=
  ⟨Hty.isLocallyClosed, fv_subset_relCtxDom HCtxRel Hty⟩

omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Project the per-hole binder-disjointness premise out of the combined
`Hbinders` predicate. Used in every binder case of the precongruence
induction to feed `TypedCtx.fill_typed` for both `e` and `e'`. -/
theorem binders_proj_pair
    {K : Ctx rT} {e₁ e₂ : Exp rT}
    (Hb : ∀ y ∈ Ctx.binderAtoms K, y ∉ e₁.fv ∧ y ∉ e₂.fv ∧ y ∉ Ctx.payloadFv K) :
    (∀ y ∈ Ctx.binderAtoms K, y ∉ e₁.fv ∧ y ∉ Ctx.payloadFv K) ∧
    (∀ y ∈ Ctx.binderAtoms K, y ∉ e₂.fv ∧ y ∉ Ctx.payloadFv K) :=
  ⟨fun y hy => ⟨(Hb y hy).1, (Hb y hy).2.2⟩,
   fun y hy => ⟨(Hb y hy).2.1, (Hb y hy).2.2⟩⟩

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
/-- Domain of `(x, A) :: Γrc` is `Γrc.dom ∪ {x}`. -/
theorem RelCtx.dom_cons (x : Var) (A : lrel rT GF) (Γrc : RelCtx rT GF) :
    (((x, A) :: Γrc).map (·.1)).toFinset = (Γrc.map (·.1)).toFinset ∪ {x} := by
  simp [List.map_cons, List.toFinset_cons, Finset.union_comm]

omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Lift a tail-freshness witness `Ctx.BindersFresh K' (S ∪ k.binderAtoms)`
across a singleton-binder context item. This is the standard derivation used
in the `lam`, `fix`, and `unpackR` cases of `bin_log_related_under_typed_ctx`,
where we need to establish freshness in the *extended* relational domain
`(x, _) :: Γrc'`. -/
theorem Ctx.BindersFresh.cons_extend
    {K' : Ctx rT} {Γrc : RelCtx rT GF} {x : Var} {A : lrel rT GF} {bAtoms : Finset Var}
    (hSingleton : bAtoms = {x})
    (h : Ctx.BindersFresh K' ((Γrc.map (·.1)).toFinset ∪ bAtoms)) :
    Ctx.BindersFresh K' (((x, A) :: Γrc).map (·.1)).toFinset :=
  RelCtx.dom_cons x A Γrc ▸ hSingleton ▸ h

/-- The shared cofinite-α-rename closer for the `lam` and `fix` binder cases.
Given `x` fresh outside `Γrc'`, the body's LC conditions, and the inner
relational hypothesis at `(x, A) :: Γrc'`, produces the cofinite witness
expected by `bin_log_related_lam` and `bin_log_related_fix`: for every fresh
`y ∉ L`, the body-renamed-to-`y` is related at the *extended* relational
context `(y, A) :: Γrc'` with the closing operation correctly inverted. -/
theorem bin_log_related_close_cofinite
    {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var} {A : lrel rT GF} {τ : Ty}
    {Ke Ke' : Exp rT}
    (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (Hbody : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
      ((x, A) :: Γrc') Ke Ke' τ) :
    ∀ y, y ∉ (Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv →
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ ((y, A) :: Γrc')
        (Exp.open' (Ke.close x) (.fvar y)) (Exp.open' (Ke'.close x) (.fvar y)) τ := by
  intro y hyNotL
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyNotL
  obtain ⟨⟨⟨hyNotRc, hyNotX⟩, hyNotFvKe⟩, hyNotFvKe'⟩ := hyNotL
  have hRename := bin_log_related_ty_rename (E := ⊤) (Δ := Δ) (Γ := Γrc')
    (x := x) (y := y) (A := A) (τE := Ke) (τE' := Ke') (τ := τ)
    (Ne.symm hyNotX) hxRc hyNotRc hyNotFvKe hyNotFvKe'
  rw [Exp.open_close_subst_lc x y _ hKe_lc, Exp.open_close_subst_lc x y _ hKe'_lc]
  exact BIBase.Entails.trans Hbody hRename


omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
/-- An element of `(Ke.close x).fv` came from `Γrc'.dom`, not from `{x}`
(closing erases `x`). The `hKe_fv` hypothesis bounds `Ke.fv` by
`((x, _) :: Γrc').dom = Γrc'.dom ∪ {x}`. -/
theorem close_fv_in_outer_dom
    {Γrc' : RelCtx rT GF} {x : Var} {Ke : Exp rT} {A : lrel rT GF}
    (hKe_fv : Ke.fv ⊆ (((x, A) :: Γrc').map (·.1)).toFinset)
    {z : Var} (hz : z ∈ (Ke.close x).fv) :
    z ∈ (Γrc'.map (·.1)).toFinset := by
  have hzKeDom := hKe_fv (Exp.close_fv_subset _ x hz)
  rw [RelCtx.dom_cons] at hzKeDom
  rcases Finset.mem_union.mp hzKeDom with hz_outer | hz_x
  · exact hz_outer
  · exact absurd (Finset.mem_singleton.mp hz_x ▸ hz) (Exp.close_var_not_fvar x Ke)

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
/-- Locally-closed-after-α-rename: if `Ke` is locally closed, so is its
opening of `close x` at any fresh `y`. Used twice per binder case in
`bin_log_related_lam_step` / `_fix_step`. -/
theorem open_close_subst_lc_at
    {Ke : Exp rT} (x y : Var) (hKe_lc : Ke.IsLocallyClosed) :
    (Exp.open' (Ke.close x) (.fvar y)).IsLocallyClosed := by
  rw [Exp.open_close_subst_lc x y _ hKe_lc]
  exact Exp.subst_lc hKe_lc (Exp.IsLocallyClosed.fvar y)

/-- Helper for the lam binder case of the precongruence. Given that the inner
context `K'` already produces related expressions at the extended `(x, A) :: Γrc'`,
plus typing of `K'.fill e`/`K'.fill e'` at `Γtc.insert x τ`, this lemma produces
the lam'd related expressions at `Γrc'`.

This is the key step that combines (a) `bin_log_related_lam` (cofinite-binder
introduction) with (b) `bin_log_related_ty_rename` (α-renaming the binder atom
from a fixed `x` to a cofinite `y`). -/
theorem bin_log_related_lam_step
    {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var} {τ_arg τ_body : Ty}
    {Ke Ke' : Exp rT}
    (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed)
    (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
      ((x, interp τ_arg Δ) :: Γrc') Ke Ke' τ_body) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc'
      (.lam (Ke.close x)) (.lam (Ke'.close x)) (.arrow τ_arg τ_body) := by
  apply bin_log_related_lam _ _ ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv)
  · exact fun y _ => open_close_subst_lc_at x y hKe_lc
  · exact fun y _ => open_close_subst_lc_at x y hKe'_lc
  · exact fun _ => close_fv_in_outer_dom hKe_fv
  · exact fun _ => close_fv_in_outer_dom hKe'_fv
  exact bin_log_related_close_cofinite hxRc hKe_lc hKe'_lc Hbody

/-- Helper for the fix binder case (same template as `bin_log_related_lam_step`,
applied to `bin_log_related_fix`). -/
theorem bin_log_related_fix_step
    {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {f : Var} {τ1 τ2 : Ty}
    {Ke Ke' : Exp rT}
    (hfRc : f ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed)
    (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ
      ((f, interp (.arrow τ1 τ2) Δ) :: Γrc') Ke Ke' (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc'
      (.fix (Ke.close f)) (.fix (Ke'.close f)) (.arrow τ1 τ2) := by
  apply bin_log_related_fix _ _ ((Γrc'.map (·.1)).toFinset ∪ {f} ∪ Ke.fv ∪ Ke'.fv)
  · exact fun y _ => open_close_subst_lc_at f y hKe_lc
  · exact fun y _ => open_close_subst_lc_at f y hKe'_lc
  · exact fun _ => close_fv_in_outer_dom hKe_fv
  · exact fun _ => close_fv_in_outer_dom hKe'_fv
  exact bin_log_related_close_cofinite hfRc hKe_lc hKe'_lc Hbody

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
    {Γtc : Tctx} {e e' : Exp rT} {τ : Ty} {Γtc' : Tctx} {τ' : Ty} {K : Ctx rT}
    (HK : TypedCtx K Γtc τ Γtc' τ')
    (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hbinders : ∀ x ∈ Ctx.binderAtoms K,
      x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K)
    (Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF),
      TctxRelated Δ Γtc Γrc →
      ⊢@{IProp GF} bin_log_related_ty (⊤ : CoPset) Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv rT GF) (Γrc' : RelCtx rT GF),
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
    -- The explicit hole pattern below pins the implicit args of `TypedCtx.cons`
    -- positionally; named-binder syntax (`| cons HKitem HKtail`) blows the
    -- elaboration heartbeats limit. `τ2` is the only implicit referenced
    -- below (in the `lam` case for the body type); the rest are free
    -- metavariables resolved by unification.
    cases HK with
    | @cons _ _ _ _ _ τ2 _ _ HKitem HKtail =>
    obtain ⟨HfreshHead, HfreshTail⟩ := Hfresh
    have HbindersK' := binders_tail Hbinders
    have IHinner := ih HKtail HbindersK' Δ
    simp only [Ctx.fill_cons, CtxItem.fill]
    cases HKitem with
    | appL Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_app $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | appR Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_app $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | pairL Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_pair $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | pairR Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_pair $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | fst =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_fst $$ [IHk']
      iexact IHk'
    | snd =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_snd $$ [IHk']
      iexact IHk'
    | inl =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_injl $$ [IHk']
      iexact IHk'
    | inr =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_injr $$ [IHk']
      iexact IHk'
    | caseL Hty1 Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_case $$ [IHk' IH1' IH2']
      · iexact IHk'
      · iexact IH1'
      iexact IH2'
    | caseM Hty0 Hty2 =>
      ihave IH0' := fundamental Hty0 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_case $$ [IH0' IHk' IH2']
      · iexact IH0'
      · iexact IHk'
      iexact IH2'
    | caseR Hty0 Hty1 =>
      ihave IH0' := fundamental Hty0 Δ Γrc' HCtx
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_case $$ [IH0' IH1' IHk']
      · iexact IH0'
      · iexact IH1'
      iexact IHk'
    | ifL Hty1 Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_if $$ [IHk' IH1' IH2']
      · iexact IHk'
      · iexact IH1'
      iexact IH2'
    | ifM Hty0 Hty2 =>
      ihave IH0' := fundamental Hty0 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_if $$ [IH0' IHk' IH2']
      · iexact IH0'
      · iexact IHk'
      iexact IH2'
    | ifR Hty0 Hty1 =>
      ihave IH0' := fundamental Hty0 Δ Γrc' HCtx
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_if $$ [IH0' IH1' IHk']
      · iexact IH0'
      · iexact IH1'
      iexact IHk'
    | alloc =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_alloc Δ Γrc') $$ [IHk']
      iexact IHk'
    | load =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_load Δ Γrc') $$ [IHk']
      iexact IHk'
    | storeL Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_store $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | storeR Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_store $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | allocTape =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_alloctape $$ [IHk']
      iexact IHk'
    | randL_unit Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_rand_unit $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | randL_tape Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply bin_log_related_rand_tape $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | randR_unit Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_rand_unit $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | randR_tape Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply bin_log_related_rand_tape $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @unop_int _ op _ Hres =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_int_unop Δ Γrc' op Hres) $$ [IHk']
      iexact IHk'
    | @unop_bool _ op _ Hres =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_bool_unop Δ Γrc' op Hres) $$ [IHk']
      iexact IHk'
    | @binopL_int _ op _ _ Hty2 Hres =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply (bin_log_related_int_binop Δ Γrc' op Hres) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @binopR_int _ op _ _ Hty1 Hres =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_int_binop Δ Γrc' op Hres) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | @binopL_bool _ op _ _ Hty2 Hres =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply (bin_log_related_bool_binop Δ Γrc' op Hres) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | @binopR_bool _ op _ _ Hty1 Hres =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_bool_binop Δ Γrc' op Hres) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | binopL_unboxedEq Hub Hty2 =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      ihave IH2' := fundamental Hty2 Δ Γrc' HCtx
      iapply (bin_log_related_unboxed_eq Δ Γrc' Hub) $$ [IHk' IH2']
      · iexact IHk'
      iexact IH2'
    | binopR_unboxedEq Hub Hty1 =>
      ihave IH1' := fundamental Hty1 Δ Γrc' HCtx
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_unboxed_eq Δ Γrc' Hub) $$ [IH1' IHk']
      · iexact IH1'
      iexact IHk'
    | fold =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_fold Δ Γrc') $$ [IHk']
      iexact IHk'
    | unfold =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_unfold Δ Γrc') $$ [IHk']
      iexact IHk'
    | tapp =>
      ihave IHk' := IHinner Γrc' HCtx (Ctx.BindersFresh.cast_no_binder rfl HfreshTail)
      iapply (bin_log_related_tapp Δ Γrc') $$ [IHk']
      iexact IHk'
    | @lam _ x τ _ =>
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset :=
        HfreshHead x (Finset.mem_singleton_self _)
      have HCtxInner : TctxRelated Δ (Γtc'.insert x τ) ((x, interp τ Δ) :: Γrc') :=
        HCtx.insert x τ (RelCtx.lookup_eq_none_of_notMem hxRc)
      have IHk_at_x := IHinner ((x, interp τ Δ) :: Γrc') HCtxInner
        (Ctx.BindersFresh.cons_extend rfl HfreshTail)
      obtain ⟨HbindersK'_e, HbindersK'_e'⟩ := binders_proj_pair HbindersK'
      obtain ⟨hKfe_lc, hKfe_fv⟩ :=
        ctx_fill_lc_fv HCtxInner (TypedCtx.fill_typed Hty_e HKtail HbindersK'_e)
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ :=
        ctx_fill_lc_fv HCtxInner (TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e')
      exact bin_log_related_lam_step hxRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv IHk_at_x
    | @fix _ f τ τ' =>
      have hfRc : f ∉ (Γrc'.map (·.1)).toFinset :=
        HfreshHead f (Finset.mem_singleton_self _)
      have HCtxInner : TctxRelated Δ (Γtc'.insert f (.arrow τ τ'))
          ((f, interp (.arrow τ τ') Δ) :: Γrc') :=
        HCtx.insert f (.arrow τ τ') (RelCtx.lookup_eq_none_of_notMem hfRc)
      have IHk_at_f := IHinner ((f, interp (.arrow τ τ') Δ) :: Γrc') HCtxInner
        (Ctx.BindersFresh.cons_extend rfl HfreshTail)
      obtain ⟨HbindersK'_e, HbindersK'_e'⟩ := binders_proj_pair HbindersK'
      obtain ⟨hKfe_lc, hKfe_fv⟩ :=
        ctx_fill_lc_fv HCtxInner (TypedCtx.fill_typed Hty_e HKtail HbindersK'_e)
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ :=
        ctx_fill_lc_fv HCtxInner (TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e')
      exact bin_log_related_fix_step hfRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv IHk_at_f
    | tlam =>
      have HfreshK'Outer : Ctx.BindersFresh K' (Γrc'.map (·.1)).toFinset :=
        Ctx.BindersFresh.cast_no_binder rfl HfreshTail
      obtain ⟨HbindersK'_e, HbindersK'_e'⟩ := binders_proj_pair HbindersK'
      have HCtxShift := HCtx.shift (default : lrel rT GF)
      obtain ⟨hKfe_lc, hKfe_fv⟩ :=
        ctx_fill_lc_fv HCtxShift (TypedCtx.fill_typed Hty_e HKtail HbindersK'_e)
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ :=
        ctx_fill_lc_fv HCtxShift (TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e')
      apply bin_log_related_tlam Δ Γrc' hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv
      intro A
      have IHk_at_A := ih HKtail HbindersK' (TyEnv.cons A Δ) Γrc'
        (HCtx.shift A) HfreshK'Outer
      imodintro
      ihave Hf := IHk_at_A
      iexact Hf
    | @unpackL x e2 _ τ_pkg _ hxFvE2 Hty_e2 =>
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset :=
        HfreshHead x (Finset.mem_singleton_self _)
      have HfreshK'Outer : Ctx.BindersFresh K' (Γrc'.map (·.1)).toFinset :=
        Ctx.BindersFresh.mono Finset.subset_union_left HfreshTail
      have HIH1 := IHinner Γrc' HCtx HfreshK'Outer
      let L : Finset Var := insert x e2.fv ∪ (Γrc'.map (·.1)).toFinset
      apply bin_log_related_unpack Δ Γrc' L HIH1
      intro A y hyL
      have hyFresh : y ∉ insert x e2.fv := fun h => hyL (Finset.mem_union_left _ h)
      have hyNotInDom : y ∉ (Γrc'.map (·.1)).toFinset :=
        fun h => hyL (Finset.mem_union_right _ h)
      have HCtxIns : TctxRelated (TyEnv.cons A Δ) ((Γtc'.shift).insert y τ_pkg)
          ((y, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') :=
        (HCtx.shift A).insert y τ_pkg (RelCtx.lookup_eq_none_of_notMem hyNotInDom)
      exact fundamental (Typed.rename_unpack hxFvE2 Hty_e2 y hyFresh)
        (TyEnv.cons A Δ) _ HCtxIns
    | @unpackR x e1 _ τ_pkg _ Hty_e1 =>
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset :=
        HfreshHead x (Finset.mem_singleton_self _)
      have HIH1 := fundamental Hty_e1 Δ Γrc' HCtx
      obtain ⟨HbindersK'_e, HbindersK'_e'⟩ := binders_proj_pair HbindersK'
      have hKfe_lc := (TypedCtx.fill_typed Hty_e HKtail HbindersK'_e).isLocallyClosed
      have hKfe'_lc := (TypedCtx.fill_typed Hty_e' HKtail HbindersK'_e').isLocallyClosed
      apply bin_log_related_unpack Δ Γrc'
        ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ (Ctx.fill K' e).fv ∪ (Ctx.fill K' e').fv) HIH1
      intro A y hyL
      have HCtxIns : TctxRelated (TyEnv.cons A Δ) ((Γtc'.shift).insert x τ_pkg)
          ((x, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') :=
        (HCtx.shift A).insert x τ_pkg (RelCtx.lookup_eq_none_of_notMem hxRc)
      have IHk_at_x := ih HKtail HbindersK' (TyEnv.cons A Δ)
        ((x, interp τ_pkg (TyEnv.cons A Δ)) :: Γrc') HCtxIns
        (Ctx.BindersFresh.cons_extend rfl HfreshTail)
      exact bin_log_related_close_cofinite hxRc hKfe_lc hKfe'_lc IHk_at_x y hyL

end Soundness

section RefinesSound
open MeasureTheory
variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {GF : BundledGFunctors} [RefinesPreGS rT GF]

/-- The bool-equality value relation extracted from `lrel_bool`. -/
def boolEqVal (v v' : Val rT) : Prop :=
  ∃ b : Bool, v.1 = .lit (.bool b) ∧ v'.1 = .lit (.bool b)

omit [RefinesPreGS rT GF] in
/-- `lrel_bool` extracts purely to `boolEqVal`. -/
theorem lrel_bool_to_boolEqVal [ApproxisRGS rT false GF] (v v' : Val rT) :
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
  have hMain := Hcpl fInd gInd (fun {a b} => hCmp a b)
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
    (Γtc : Tctx) (e e' : Exp rT) (τ : Ty)
    (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS rT false GF) (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF),
      TctxRelated Δ Γtc Γrc →
      ⊢@{IProp GF} bin_log_related_ty (hlc := false) (GF := GF)
        (⊤ : CoPset) Δ Γrc e e' τ) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool),
      TypedCtx K Γtc τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K,
        x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  intro K σ₀ b Htyped HfreshK Hbinders
  have hRewriteFb : ∀ (e0 : Exp rT),
      limExec ⟨e0, σ₀⟩ (finalBool b) =
      (limExecV ⟨e0, σ₀⟩) {.lit (.bool b)} := by
    intro e0
    unfold limExecV asExpr
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
    rfl
  rw [hRewriteFb (K.fill e), hRewriteFb (K.fill e')]
  have hCpl :
      AddCoupl 0 (adequacyRel boolEqVal)
        (limExecV ⟨K.fill e,  σ₀⟩)
        (limExecV ⟨K.fill e', σ₀⟩) := by
    apply refines_coupling (GF := GF) (A := fun _ => lrel_bool) (φ := boolEqVal)
    · intro _ v v'; exact lrel_bool_to_boolEqVal v v'
    · intro IR
      have HrelClosed :
          ⊢@{IProp GF}
            bin_log_related_ty (⊤ : CoPset) (default : TyEnv rT GF) []
              (K.fill e) (K.fill e') .bool :=
        bin_log_related_under_typed_ctx Htyped Hty_e Hty_e' Hbinders
          (Hlog IR) _ _ TctxRelated.empty_nil HfreshK
      unfold bin_log_related_ty bin_log_related at HrelClosed
      show ⊢@{IProp GF} refines (⊤ : CoPset)
        (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) (K.fill e))
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) (K.fill e'))
        (interp Ty.bool (default : TyEnv rT GF))
      ihave Hf := HrelClosed
      iapply Hf $$ %([] : ValSubstMap rT)
      iapply env_ltyped2_empty
  apply AddCoupl.set_leq_zero (MeasurableSet.singleton _) (MeasurableSet.singleton _) hCpl
  rintro a b' ⟨v, v', hv, hv', ⟨b'', hvb1, hvb2⟩⟩ ha
  have toVal?_to_eq : ∀ {e : Exp rT} {w : Val rT}, e.toVal? = some w → e = w.1 := fun he => by
    unfold Exp.toVal? at he
    split at he
    · rw [← Option.some.inj he]
    · cases he
  have hvbeq : v.1 = .lit (.bool b) := (toVal?_to_eq hv) ▸ ha
  rw [hvbeq] at hvb1
  injection hvb1 with hbool
  injection hbool with hbb
  subst hbb
  show b' ∈ ({.lit (.bool b)} : Set (Exp rT))
  exact (toVal?_to_eq hv').trans hvb2

/-- **Soundness of the logical relation (closed case), restricted to fresh contexts.** -/
theorem refines_sound_fresh (e e' : Exp rT) (τ : Ty)
    (Hty_e : Typed Tctx.empty e τ) (Hty_e' : Typed Tctx.empty e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS rT false GF) (Δ : TyEnv rT GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF)
        (⊤ : CoPset) e e' (interp τ Δ)) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool),
      TypedCtx K Tctx.empty τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K,
        x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  apply refines_sound_open_fresh (GF := GF) Tctx.empty e e' τ Hty_e Hty_e'
  intro IR Δ Γrc HCtx
  obtain rfl := HCtx.eq_nil_of_empty
  unfold bin_log_related_ty bin_log_related
  iintro %vs Hvs
  ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
  rw [hvs_nil]
  show ⊢@{IProp GF} refines (⊤ : CoPset) e e' (interp τ Δ)
  exact Hlog IR Δ

end RefinesSound

end ProbLang
