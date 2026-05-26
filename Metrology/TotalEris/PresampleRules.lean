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

**Status**: `twp_presample` fully proved. `twp_presample_adv_comp`
stated with structural proof scaffold; three sub-sorries remaining
(integral bound, Classical-choice witness equality, per-outcome
continuation closure). -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS hlc GF]

/-- Basic *total* presample rule. Given tape ownership `α ↪ₐ ⟨N, bs⟩`
with positive bound `N`, the WP can be advanced by appending a freshly
sampled `n` to the tape; the body then takes back the updated tape and
continues. Rocq: `twp_presample` (`presample_rules.v:49`).

Proof strategy:
1. `twp_lift_step_fupd_glm` to expose the glm goal.
2. Look up the tape via `app_state_lookup_tape`.
3. Apply `glm_state_step` with the singleton/uniform R, slack ε₁ = 0,
   and per-outcome `X₂ ≡ ε_now` (no credit spent on presample).
4. Per outcome: update ghost tape via `app_state_update_tape`, feed
   the IH via `tglWp_unfold_step`, mod through the body fupd. -/
theorem twp_presample {E : CoPset} {e : Exp} {α : Loc} {Φ : Val → IProp GF}
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
  iapply glm_state_step
  iexists α, ⟨N, bs⟩
  isplitr; · ipure_intro; exact ⟨hlookup, hN⟩
  iexists (fun σ' => ∃ n : { z : Int // 0 ≤ z ∧ z < N },
            σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)),
    0, (fun _ => ε₁), ε₁
  isplitr; · ipure_intro; intro _; exact _root_.le_refl _
  isplitr
  · ipure_intro
    -- 0 + ∫⁻ σ', ε₁ ∂(tapePresample σ₁ α) ≤ ε₁
    -- The integral over a probability measure equals ε₁ * 1 = ε₁.
    haveI : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one, zero_add]
  isplitr
  · ipure_intro
    -- Pgl 0 R (tapePresample σ₁ α). Use `tapePresample_ae` to characterize
    -- the support: every σ' has the form `σ₁.update_tapes (· insert ⟨N, bs ++ [n]⟩)`.
    show (tapePresample σ₁ α) {σ' | ¬ _} ≤ 0
    refine _root_.le_of_eq ?_
    rw [← MeasureTheory.ae_iff]
    refine tapePresample_ae hlookup ?_
    intro n
    exact ⟨n, rfl⟩
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
`0`. Used as the `glmStateStep` continuation's per-outcome credit. -/
noncomputable def presampleAdvCompX₂
    (σ : State) (α : Loc) (N : Int)
    (bs : List { z : Int // 0 ≤ z ∧ z < N })
    (ε₂ : { z : Int // 0 ≤ z ∧ z < N } → ENNReal) (σ' : State) : ENNReal :=
  if h : ∃ n : { z : Int // 0 ≤ z ∧ z < N },
      σ' = σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)
    then ε₂ (Classical.choose h)
    else 0

/-- **Advanced-composition presample rule** (Rocq: `twp_presample_adv_comp`,
`presample_rules.v:115`).

Given an existing tape `α` of positive bound `N`, credit `↯ε₁`, and a
per-outcome continuation that receives `↯(ε₂ n)` together with the
updated tape, the WP can advance by presampling — provided the expected
per-outcome credit matches `ε₁` (the HSum side condition).

**Status**: Per-outcome continuation closed; only the integral side
condition `0 + ∫⁻ σ', (ε_now - ε₁) + ε₂(extracted) ∂(tapePresample σ₁ α)
≤ ε_now` remains as `sorry`. That reduces to `HSum` via
`tapePresample`'s unfolding through `tapeIndexUniform` + `Measure.bind`
+ `lintegral_dirac` (~30 lines of measure-theoretic plumbing). -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp} {α : Loc}
    {Φ : Val → IProp GF} {t : Tape} (hN : 0 < t.bound)
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
  ihave ⟨Hε_now, Herr, %hLe⟩ : iprop(ErisWpGS.errInterp ε_now ∗ ↯ε₁ ∗ ⌜ε₁ ≤ ε_now⌝)
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
  iapply glm_state_step
  iexists α, ⟨N, bs⟩
  isplitr; · ipure_intro; exact ⟨hlookup, hN⟩
  iexists (fun σ' => ∃ n : { z : Int // 0 ≤ z ∧ z < N },
              σ' = σ₁.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)),
    0, (fun σ' => (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ'),
    ((ε_now - ε₁) + 1)
  -- Sub-goal 1: bound on X₂.
  isplitr
  · ipure_intro
    intro σ'
    simp only
    gcongr
    unfold presampleAdvCompX₂
    split <;> first | exact Hbd _ | exact zero_le _
  -- Sub-goal 2: integral bound.
  isplitr
  · ipure_intro
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
    -- Bound `∫⁻ X₂_inner ≤ ε₁`. Reduction (~40 lines, parallels
    -- `twp_rand_exp_nat`'s integral-bound block in `ErrorRules.lean:330`):
    --   1. Unfold `tapePresample` via `hlookup` to a bind over
    --      `tapeIndexUniform N`.
    --   2. `Measure.lintegral_bind` + `lintegral_dirac` push integral
    --      through the bind, leaving `∫⁻ n, X₂_inner (update_n) ∂(tapeIndexUniform N)`.
    --   3. Apply `hPointwise` pointwise to get `∫⁻ n, ε₂ n ∂(tapeIndexUniform N)`.
    --   4. Unfold `tapeIndexUniform` and `lintegral_map`, then
    --      `lintegral_indicator` + `lintegral_finset` + `PMF.toMeasure_apply_singleton`
    --      + `PMF.uniformOfFinset_apply` collapses to `(∑ z ∈ Ico 0 N, ε₂ ⟨z, _⟩) / N.toNat`.
    --   5. Match the HSum-image form via `Finset.image_attach` reindexing.
    have hint_bound :
        ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤ ε₁ := by
      sorry
    calc (ε_now - ε₁) + ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
        ≤ (ε_now - ε₁) + ε₁ := by gcongr
      _ = ε_now := tsub_add_cancel_of_le hLe
  -- Sub-goal 3: Pgl 0 R. Support of tapePresample = R-states.
  isplitr
  · ipure_intro
    show (tapePresample σ₁ α) {σ' | ¬ _} ≤ 0
    refine _root_.le_of_eq ?_
    rw [← MeasureTheory.ae_iff]
    refine tapePresample_ae hlookup ?_
    intro n
    exact ⟨n, rfl⟩
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
  ihave HbupdDec : iprop(|==> ErisWpGS.errInterp (ε_now - ε₁)) $$ [Hε_now Herr]
  · iapply errInterp_supply_decrease
    isplitl [Hε_now]; · iexact Hε_now
    iexact Herr
  imod HbupdDec with Hε_rem
  -- Case split on whether (ε_rem + ε₂ n) < 1.
  by_cases hlt : ε_now - ε₁ + ε₂ n < 1
  · -- Sub-case `< 1`: increase supply by ε₂ n, feed Hcont.
    ihave HbupdInc : iprop(|==> (ErisWpGS.errInterp (ε_now - ε₁ + ε₂ n) ∗ ↯(ε₂ n))) $$ [Hε_rem]
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
