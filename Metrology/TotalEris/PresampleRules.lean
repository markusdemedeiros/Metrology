module

public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.TotalLifting
public import Metrology.TotalEris.Glm
public import Metrology.TotalEris.ErrorRules

@[expose] public section

/-!
# Presample rules

Port of `clutch/theories/eris/presample_rules.v`. These rules let the
user *presample* a tape value before the program actually reads it,
useful for amortizing error-credit bookkeeping across recursive calls
(see `unif_rw_1d_terminate` in the random-walk example).

**Status**: `twp_presample` and `twp_presample_adv_comp` both fully
proved (no `sorry`). -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris


variable {rT : Type _} [ProbLang.ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- The support of a `tapePresample` step is a countable set of tape-updated
states, hence measurable (countability-free; `State rT` has measurable
singletons via `ProbLangℝ`). -/
theorem presample_support_measurableSet {σ₁ : State rT} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} :
    MeasurableSet {σ' : State rT | ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)} := by
  have hc : {σ' : State rT | ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)}.Countable := by
    apply Set.Countable.mono (s₂ := (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
      σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) '' Set.univ)
    · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
    · exact (Set.countable_univ).image _
  exact hc.measurableSet

/-- Basic *total* presample rule. Given tape ownership `α ↪ₐ ⟨N, bs⟩`
with positive bound `N`, the WP can be advanced by appending a freshly
sampled `n` to the tape; the body then takes back the updated tape and
continues. Rocq: `twp_presample` (`presample_rules.v:49`).

Proof strategy:
1. `twp_lift_step_fupd_glm` to expose the glm goal.
2. Look up the tape via `app_state_lookup_tape`.
3. Apply `glm'_erasable_step` with `μ := tapePresample σ₁ α` (erasable via
   `ErasableExpr.tapePresample`), the singleton/uniform R, slack ε₁ = 0,
   and per-outcome `X₂ ≡ ε_now` (no credit spent on presample).
4. Per outcome: update ghost tape via `app_state_update_tape`, feed
   the IH via `tglWp_unfold_step`, mod through the body fupd. -/
theorem twp_presample {E : CoPset} {e : Exp rT} {α : Loc} {Φ : Val rT → IProp GF}
    {t : Tape} (hN : 0 < t.bound) (hv : e.toVal? = none) :
    iprop(α ↪ₐ t ∗
      (∀ (n : { z : Int // 0 ≤ z ∧ z < t.bound }),
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply (twp_lift_step_fupd_glm hv)
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  ihave %hlookup := app_state_lookup_tape (GF := GF) $$ Hσ Htape
  -- Need to deconstruct `t` so the tape-update produces a matching shape.
  obtain ⟨N, bs⟩ := t
  simp only at hN hlookup
  -- Mask shift E → ∅, save the closer to reopen later.
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm'_erasable_step
  iexists (tapePresample σ₁ α),
    (fun σ' => ∃ n : { z : Int // 0 ≤ z ∧ z < N },
            σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)),
    0, (fun _ => ε₁), ε₁
  -- Erasability: presampling onto tape `α` is expression-erasable.
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlookup hN
  -- MeasurableSet of the support: a countable set of tape-updated states.
  isplitr
  · ipureintro
    have hctble : {σ' : State rT | ∃ n : { z : Int // 0 ≤ z ∧ z < N },
        σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)}.Countable := by
      apply Set.Countable.mono (s₂ := (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
        σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) '' Set.univ)
      · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
      · exact (Set.countable_univ).image _
    exact hctble.measurableSet
  isplitr; · ipureintro; intro _; exact _root_.le_refl _
  isplitr
  · ipureintro
    -- 0 + ∫⁻ σ', ε₁ ∂(tapePresample σ₁ α) ≤ ε₁
    -- The integral over a probability measure equals ε₁ * 1 = ε₁.
    haveI : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one, zero_add]
  isplitr
  · ipureintro
    -- Pgl 0 R (tapePresample σ₁ α). Use `tapePresample_ae` to characterize
    -- the support: every σ' has the form `σ₁.update_tapes (· insert ⟨N, bs ++ [n]⟩)`.
    show (tapePresample σ₁ α) {σ' | ¬ _} ≤ 0
    refine _root_.le_of_eq ?_
    rw [← MeasureTheory.ae_iff]
    -- Support of `tapePresample` is exactly the `R`-states (countability-free).
    exact tapePresample_ae hlookup presample_support_measurableSet (fun n => ⟨n, rfl⟩)
  iintro %σ' %hR
  rcases hR with ⟨n, hσ'⟩
  subst hσ'
  -- Close ∅→E via `Hclose`, then update tape, then mod the Hwp's fupd
  -- which gives back the glm.
  imod Hclose with _
  imod (app_state_update_tape (GF := GF) (l := α) (t := ⟨N, bs⟩)
        (s := ⟨N, bs ++ [n]⟩)) $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave Hwp := Hcont $$ %n [Htape']
  · iexact Htape'
  ihave Hwp' := (BI.equiv_iff.mp (tglWp_unfold_step hv)).1 $$ Hwp
  ihave HwpBody := Hwp' $$ %_ %ε₁ [Hσ' Hε]
  · isplitl [Hσ']; · iexact Hσ'
    iexact Hε
  imod HwpBody with HGlm
  imodintro
  iapply execStutter_free
  -- Bridge the `ExtTreeMap.insert` (from `tapePresample`) vs
  -- `PartialMap.insert` (from `app_state_update_tape`) syntactic gap.
  simp only [ExtTreeMap.insert_eq_PartialMap_insert]
  iexact HGlm

/-! ## Advanced-composition presample

Generalizes `twp_presample` to per-outcome error spending. The sum of
per-outcome errors weighted by the uniform measure must match `ε₁`. -/

section AdvComp

open Classical in
/-- Per-outcome error function `X₂ : State → ENNReal` for advanced
composition. On any `σ'` that has the form `σ.update_tapes (insert α
⟨N, bs ++ [n]⟩)` for some `n`, extracts `ε₂ n`; off-support, returns
`0`. Used as the `glmErasable'` continuation's per-outcome credit. -/
noncomputable def presampleAdvCompX₂
    (σ : State rT) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) (σ' : State rT) : ENNReal :=
  if h : ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)
    then ε₂ (Classical.choose h)
    else 0

open Classical in
/-- `presampleAdvCompX₂` is measurable. It is supported on the (finite) set of
tape-updated states indexed by the sample `n : {z // 0 ≤ z ∧ z < N}`, and — using
that distinct samples produce distinct states — equals the countable sum of
singleton-indicators `∑' n, {update n}.indicator (ε₂ n)`. Countability-free: the
sum ranges over the finite sample index, and singleton measurability comes from
`MeasurableSingletonClass (State rT)` (not `Countable rT`). -/
theorem presampleAdvCompX₂.measurable
    (σ : State rT) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) :
    Measurable (presampleAdvCompX₂ σ α N bs ε₂) := by
  -- Distinct samples yield distinct tape-updated states.
  have hInj : Function.Injective
      (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
        σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) := by
    intro n₁ n₂ heq
    have htape_eq : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩)
                  = (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩) := by
      have := congrArg State.tapes heq
      simpa [State.update_tapes] using this
    have hget₁ : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩)[α]? = some ⟨N, bs ++ [n₁]⟩ :=
      Std.ExtTreeMap.getElem?_insert_self
    have hget₂ : (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩)[α]? = some ⟨N, bs ++ [n₂]⟩ :=
      Std.ExtTreeMap.getElem?_insert_self
    rw [htape_eq] at hget₁
    rw [hget₂] at hget₁
    have hbs : bs ++ [n₂] = bs ++ [n₁] := by simpa using hget₁
    have : [n₂] = [n₁] := List.append_cancel_left hbs
    exact ((List.cons.injEq _ _ _ _).mp this |>.1).symm
  -- Rewrite as a countable sum of singleton-indicators.
  have hrw : presampleAdvCompX₂ σ α N bs ε₂
      = fun σ' => ∑' n : { z : Int // 0 ≤ z ∧ z < N },
          ({σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)} : Set (State rT)).indicator
            (fun _ => ε₂ n) σ' := by
    funext σ'
    unfold presampleAdvCompX₂
    by_cases h : ∃ n : { z : Int // 0 ≤ z ∧ z < N },
        σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)
    · rw [dif_pos h]
      have hc : σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [Classical.choose h]⟩) :=
        Classical.choose_spec h
      rw [tsum_eq_single (Classical.choose h) ?_]
      · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr hc)]
      · intro n hn
        apply Set.indicator_of_notMem
        rw [Set.mem_singleton_iff]
        intro hcontra
        exact hn (hInj (hc.symm.trans hcontra)).symm
    · rw [dif_neg h]
      refine (ENNReal.tsum_eq_zero.mpr fun n => ?_).symm
      apply Set.indicator_of_notMem
      rw [Set.mem_singleton_iff]
      intro hcontra
      exact h ⟨n, hcontra⟩
  rw [hrw]
  exact Measurable.tsum fun n =>
    measurable_const.indicator (measurableSet_singleton _)

/-- **Advanced-composition presample rule** (Rocq: `twp_presample_adv_comp`,
`presample_rules.v:115`).

Given an existing tape `α` of positive bound `N`, credit `↯ε₁`, and a
per-outcome continuation that receives `↯(ε₂ n)` together with the
updated tape, the WP can advance by presampling — provided the expected
per-outcome credit matches `ε₁` (the HSum side condition).

**Status**: Fully proved. The integral side condition
`0 + ∫⁻ σ', (ε_now - ε₁) + ε₂(extracted) ∂(tapePresample σ₁ α) ≤ ε_now`
is discharged by reducing to `HSum`: `tapePresample_lintegral` unfolds
the presample integral, `hPointwise` collapses the integrand to `ε₂ n`,
`tapeIndexUniform_lintegral_eq_cfg_uniform` routes through the proven
`Cfg.uniform` computation to a finite sum, and the HSum-image form is
matched via `Finset.sum_image` + `Finset.sum_attach`. -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp rT} {α : Loc}
    {Φ : Val rT → IProp GF} {t : Tape} (hN : 0 < t.bound)
    {ε₁ : ENNReal}
    {ε₂ : { z : Int // 0 ≤ z ∧ z < t.bound } → ENNReal}
    (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ (Finset.Ico 0 t.bound).attach.image
              (fun ⟨z, hz⟩ => (⟨z, by
                rw [Finset.mem_Ico] at hz; exact hz⟩ :
                { z : Int // 0 ≤ z ∧ z < t.bound })),
              ε₂ n) / t.bound.toNat ≤ ε₁)
    (hv : e.toVal? = none) :
    iprop(↯ε₁ ∗ α ↪ₐ t ∗
      (∀ (n : { z : Int // 0 ≤ z ∧ z < t.bound }),
        ↯(ε₂ n) ∗
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply (twp_lift_step_fupd_glm hv)
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape (GF := GF) $$ Hσ Htape
  obtain ⟨N, bs⟩ := t
  simp only at hN hlookup Hbd ε₂ HSum
  -- Get the supply bound `ε₁ ≤ ε_now`.
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp (rT := rT) ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
      $$ [Hε_now Herr]
  · iapply errInterp_supply_bound
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  -- Mask shift E → ∅.
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  -- Injectivity of `n ↦ σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)`:
  -- different sampled values produce different states. Used by both
  -- the integral-bound and per-outcome paths to invert `Classical.choose`.
  have hInj : ∀ (n₁ n₂ : { z : Int // 0 ≤ z ∧ z < N }),
      σ₁.update_tapes (·.insert α ⟨N, bs ++ [n₁]⟩) =
        σ₁.update_tapes (·.insert α ⟨N, bs ++ [n₂]⟩) → n₁ = n₂ := by
    intro n₁ n₂ heq
    have htape_eq : (σ₁.tapes.insert α ⟨N, bs ++ [n₁]⟩)
                  = (σ₁.tapes.insert α ⟨N, bs ++ [n₂]⟩) := by
      have := congrArg State.tapes heq
      simpa [State.update_tapes] using this
    have hget₁ : (σ₁.tapes.insert α ⟨N, bs ++ [n₁]⟩)[α]? = some ⟨N, bs ++ [n₁]⟩ :=
      Std.ExtTreeMap.getElem?_insert_self
    have hget₂ : (σ₁.tapes.insert α ⟨N, bs ++ [n₂]⟩)[α]? = some ⟨N, bs ++ [n₂]⟩ :=
      Std.ExtTreeMap.getElem?_insert_self
    rw [htape_eq] at hget₁
    rw [hget₂] at hget₁
    have hbs : bs ++ [n₂] = bs ++ [n₁] := by
      simpa using hget₁
    have : [n₂] = [n₁] := List.append_cancel_left hbs
    exact ((List.cons.injEq _ _ _ _).mp this |>.1).symm
  iapply glm'_erasable_step
  iexists (tapePresample σ₁ α),
    (fun σ' => ∃ n : { z : Int // 0 ≤ z ∧ z < N },
              σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)),
    0, (fun σ' => (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ'),
    ((ε_now - ε₁) + 1)
  -- Erasability: presampling onto tape `α` is expression-erasable.
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlookup hN
  -- Sub-goal 0: MeasurableSet of the support (countable set of tape-updated states).
  isplitr
  · ipureintro
    have hctble : {σ' : State rT | ∃ n : { z : Int // 0 ≤ z ∧ z < N },
        σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)}.Countable := by
      apply Set.Countable.mono (s₂ := (fun n : { z : Int // 0 ≤ z ∧ z < N } =>
        σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) '' Set.univ)
      · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
      · exact (Set.countable_univ).image _
    exact hctble.measurableSet
  -- Sub-goal 1: bound on X₂.
  isplitr
  · ipureintro
    intro σ'
    simp only
    gcongr
    unfold presampleAdvCompX₂
    split <;> first | exact Hbd _ | exact zero_le
  -- Sub-goal 2: integral bound.
  isplitr
  · ipureintro
    rw [zero_add]
    haveI : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    -- Split the integral: `∫ (c + f) = c * μ.univ + ∫ f`.
    rw [MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    -- Pointwise: `presampleAdvCompX₂ σ₁ α N bs ε₂ (update_n) = ε₂ n` for any n.
    have hPointwise : ∀ n : { z : Int // 0 ≤ z ∧ z < N },
        presampleAdvCompX₂ σ₁ α N bs ε₂
            (σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) = ε₂ n := by
      intro n
      unfold presampleAdvCompX₂
      rw [dif_pos ⟨n, rfl⟩]
      have hch_spec := Classical.choose_spec
        (⟨n, rfl⟩ : ∃ n' : { z : Int // 0 ≤ z ∧ z < N },
          σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩) =
            σ₁.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))
      have : Classical.choose _ = n := (hInj n _ hch_spec).symm
      rw [this]
    have hint_bound :
        ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤ ε₁ := by
      classical
      -- Push the integral through `tapePresample`'s unfolding and collapse the
      -- integrand pointwise to `ε₂ n` (via `hPointwise`).
      rw [tapePresample_lintegral hlookup (presampleAdvCompX₂ σ₁ α N bs ε₂)
            (presampleAdvCompX₂.measurable σ₁ α N bs ε₂)]
      simp_rw [hPointwise]
      -- Goal: `∫⁻ n, ε₂ n ∂tapeIndexUniform N ≤ ε₁`.
      -- Common integrand `F : Int → ℝ≥0∞`, total via a `0` default off-bounds.
      set F : Int → ℝ≥0∞ :=
        (fun z => if hz : 0 ≤ z ∧ z < N then ε₂ ⟨z, hz⟩ else 0) with hF
      have hNonempty : (Finset.Ico (0:Int) N).Nonempty :=
        ⟨0, Finset.mem_Ico.mpr ⟨_root_.le_refl _, hN⟩⟩
      have hCard : (Finset.Ico (0:Int) N).card = N.toNat := by
        rw [Int.card_Ico, sub_zero]
      -- `ε₂ n = F ↑n` (the membership-proof inside the subtype is irrelevant).
      have hεF : ∀ n : { z : Int // 0 ≤ z ∧ z < N }, ε₂ n = F (↑n) := by
        intro n; rw [hF]; simp only [dif_pos n.2]
      -- Step A: compute the lintegral as `(∑ z ∈ Ico 0 N, F z) / N.toNat` by
      -- routing through `Cfg.uniform` (reusing the proven uniform computation).
      have hLI : ∫⁻ n : { z : Int // 0 ≤ z ∧ z < N }, ε₂ n ∂tapeIndexUniform N
          = ∑ z ∈ Finset.Ico (0:Int) N, F z / (N.toNat : ℝ≥0∞) := by
        have hf_eq : ∀ n : { z : Int // 0 ≤ z ∧ z < N },
            ε₂ n = (fun ρ : Cfg rT => match ρ.expr with
              | .lit (.int m) => F m | _ => 0) ⟨.lit (.int (↑n)), σ₁⟩ := by
          intro n; rw [hεF n]
        simp_rw [hf_eq]
        rw [tapeIndexUniform_lintegral_eq_cfg_uniform hN σ₁ (fun ρ => match ρ.expr with
              | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr)]
        -- Now over `Cfg.uniform N σ₁`; mirror the `ErrorRules` computation.
        have hCfgUniform :
            Cfg.uniform N σ₁ =
              (PMF.uniformOfFinset (Finset.Ico (0:Int) N) hNonempty).toMeasure.map
                (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := by
          unfold Cfg.uniform; simp only [Int.isPos, dif_pos hN]
        rw [hCfgUniform, MeasureTheory.lintegral_map
              (f := fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr) .of_discrete]
        -- `∫⁻ z, F z ∂uniform = ∑ z ∈ Ico 0 N, F z / N.toNat`.
        have hIndic : (fun z : Int => (match (⟨.lit (.int z), σ₁⟩ : Cfg rT).expr with
              | .lit (.int m) => F m | _ => 0))
            = ((Finset.Ico (0:Int) N) : Set Int).indicator F := by
          funext z
          by_cases hz : z ∈ Finset.Ico (0:Int) N
          · rw [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            simp only [Finset.mem_Ico, not_and, _root_.not_lt] at hz
            show F z = 0
            simp only [hF]
            by_cases h0 : 0 ≤ z
            · rw [dif_neg]; exact fun ⟨_, h⟩ => (_root_.not_lt.mpr (hz h0)) h
            · rw [dif_neg]; exact fun ⟨h, _⟩ => h0 h
        rw [hIndic, MeasureTheory.lintegral_indicator
              ((Finset.Ico (0:Int) N).measurableSet),
            MeasureTheory.lintegral_finset]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z),
            PMF.uniformOfFinset_apply, if_pos hz, hCard,
            ENNReal.div_eq_inv_mul, mul_comm]
      -- Step B: match the HSum numerator `∑ n ∈ image, ε₂ n = ∑ z ∈ Ico, F z`.
      have hSumImage :
          (∑ n ∈ (Finset.Ico (0:Int) N).attach.image
              (fun x : { z : Int // z ∈ Finset.Ico (0:Int) N } =>
                (⟨x.1, Finset.mem_Ico.mp x.2⟩ :
                  { z : Int // 0 ≤ z ∧ z < N })), ε₂ n)
            = ∑ z ∈ Finset.Ico (0:Int) N, F z := by
        rw [Finset.sum_image
              (by
                intro x _ y _ hxy
                apply Subtype.ext
                have h := congrArg Subtype.val hxy
                simpa using h)]
        rw [← Finset.sum_attach (Finset.Ico (0:Int) N) F]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hb := Finset.mem_Ico.mp a.2
        simp only [hF, dif_pos hb]
      have hdiv : ∑ z ∈ Finset.Ico (0:Int) N, F z / (N.toNat : ℝ≥0∞)
          = (∑ z ∈ Finset.Ico (0:Int) N, F z) / (N.toNat : ℝ≥0∞) := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
      rw [hLI, hdiv, ← hSumImage]
      exact HSum
    calc (ε_now - ε₁) + ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
        ≤ (ε_now - ε₁) + ε₁ := by gcongr
      _ = ε_now := tsub_add_cancel_of_le hLe
  -- Sub-goal 3: Pgl 0 R. Support of tapePresample = R-states.
  isplitr
  · ipureintro
    show (tapePresample σ₁ α) {σ' | ¬ _} ≤ 0
    refine _root_.le_of_eq ?_
    rw [← MeasureTheory.ae_iff]
    -- Support of `tapePresample` is exactly the `R`-states (countability-free).
    exact tapePresample_ae hlookup presample_support_measurableSet (fun n => ⟨n, rfl⟩)
  -- Per-outcome continuation.
  iintro %σ' %hR
  rcases hR with ⟨n, hσ'⟩
  subst hσ'
  imod Hclose with _
  -- Update tape ghost: appStateAuth σ₁ + α ↪ ⟨N,bs⟩ → appStateAuth σ' + α ↪ ⟨N, bs++[n]⟩.
  imod (app_state_update_tape (GF := GF) (l := α) (t := ⟨N, bs⟩)
        (s := ⟨N, bs ++ [n]⟩)) $$ Hσ Htape with ⟨Hσ', Htape'⟩
  -- `presampleAdvCompX₂` at this specific σ' equals ε₂ n.
  have hX₂_eq : presampleAdvCompX₂ σ₁ α N bs ε₂
      (σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) = ε₂ n := by
    unfold presampleAdvCompX₂
    rw [dif_pos ⟨n, rfl⟩]
    have hch_spec := Classical.choose_spec
      (⟨n, rfl⟩ : ∃ n' : { z : Int // 0 ≤ z ∧ z < N },
        σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩) =
          σ₁.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))
    have : Classical.choose _ = n := (hInj n _ hch_spec).symm
    rw [this]
  -- Peel ε₁ off the supply: ε_now → ε_now - ε₁ = ε_rem.
  ihave HbupdDec : iprop(|==> ErisWpGS.errInterp (rT := rT) (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod HbupdDec with Hε_rem
  -- Case split on whether (ε_rem + ε₂ n) < 1.
  by_cases hlt : ε_now - ε₁ + ε₂ n < 1
  · -- Sub-case `< 1`: increase supply by ε₂ n, feed Hcont.
    ihave HbupdInc : iprop(|==> (ErisWpGS.errInterp (rT := rT) (ε_now - ε₁ + ε₂ n) ∗ ↯(ε₂ n))) $$ [Hε_rem]
    · iapply errInterp_supply_increase hlt
      iexact Hε_rem
    imod HbupdInc with ⟨Hε_new, Hε₂_cr⟩
    simp only [hX₂_eq]
    ihave Hwp := Hcont $$ %n [Hε₂_cr Htape']
    · isplitl [Hε₂_cr]; · iexact Hε₂_cr
      iexact Htape'
    ihave Hwp' := (BI.equiv_iff.mp (tglWp_unfold_step hv)).1 $$ Hwp
    ihave HwpBody := Hwp' $$ %_ %(ε_now - ε₁ + ε₂ n) [Hσ' Hε_new]
    · isplitl [Hσ']; · iexact Hσ'
      iexact Hε_new
    imod HwpBody with HGlm
    imodintro
    iapply execStutter_free
    simp only [ExtTreeMap.insert_eq_PartialMap_insert]
    iexact HGlm
  · -- Sub-case `≥ 1`: stutter-spend (vacuous).
    push Not at hlt
    simp only [hX₂_eq]
    imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with _
    imodintro
    iapply execStutter_spend hlt

end AdvComp

end TotalEris
end ProbLang
