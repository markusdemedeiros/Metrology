import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Real.OfDigits

import Metrology.Couplings.AdditiveCouplings

section Couplings


variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

open MeasureTheory Measure

/-- Exact relational coupling: the zero-slack case of `ARcoupl`. -/
def RelCoupl (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling id Φ μₗ μᵣ

namespace RelCoupl

theorem relCoupl_addCoupl {Φ : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β} :
    RelCoupl Φ μₗ μᵣ = AddCoupl 0 Φ μₗ μᵣ := by
  sorry

/-- `ARcoupl 0` at the equality relation, i.e. `Rcoupl` refl. -/
theorem refl_zero (μ : Measure α) : RelCoupl (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ (refl _)
/-!
#### Change of variables

The core measure-theoretic coupling: any measure is exactly coupled to its pushforward
along a measurable map. This is the analogue of Clutch's `ARcoupl_map` and is the key
lemma behind all uniform-measure couplings — a bijection from `Fin N` to itself that
preserves the uniform measure immediately gives `ARcoupl 0` on `(dunifP N, dunifP N)`.
-/

/-- Any measure `μ` is `Rcoupl`-coupled to its pushforward `μ.map h` along the graph of `h`. -/
theorem map {h : α → β} (hm : Measurable h) (μ : Measure α) :
    RelCoupl (fun v => v.2 = h v.1) μ (μ.map h) := by
  rintro ⟨f, _, _⟩ ⟨g, gm, _⟩ Hfg
  sorry
  -- show ∫⁻ a, f a ∂μ ≤ ∫⁻ b, g b ∂(μ.map h) + 0
  -- rw [add_zero]
  -- calc ∫⁻ a, f a ∂μ
  --     _ ≤ ∫⁻ a, g (h a) ∂μ := lintegral_mono fun a => Hfg rfl
  --     _ = ∫⁻ b, g b ∂(μ.map h) := (lintegral_map gm hm).symm

/-- A measure-preserving map `h : α → β` gives an exact coupling of the source measure with
any target measure it preserves. In particular, with `α = β` and `h` a measurable permutation
that fixes `μ` (i.e. `μ.map h = μ`), this gives `Rcoupl` of `μ` with itself along `h`. -/
theorem map_of_measurePreserving {h : α → β} {μ : Measure α} {ν : Measure β}
    (hp : MeasurePreserving h μ ν) :
    RelCoupl (fun v => v.2 = h v.1) μ ν := by
  rw [← hp.map_eq]
  exact map hp.measurable μ

/-- Specialization: a measure is exactly self-coupled along any permutation that preserves
it. This is the measure-theoretic analogue of Clutch's `ARcoupl_dunif`: if `h : α → α`
preserves `μ` (e.g. `μ` is uniform on a finite type and `h` is a bijection), then
`Rcoupl (fun (a, a') => a' = h a) μ μ`. -/
theorem self_of_measurePreserving {h : α → α} {μ : Measure α}
    (hp : MeasurePreserving h μ μ) :
    RelCoupl (fun v => v.2 = h v.1) μ μ :=
  map_of_measurePreserving hp

/-- Two probability measures are exactly coupled under the universal relation, provided
every test function `f` is pointwise ≤ every test function `g`. The argument threads
through the sup of `f` and the inf of `g`: `∫⁻ f dμ ≤ ⨆ f ≤ ⨅ g ≤ ∫⁻ g dμ'`. -/
theorem trivial {μₗ : Measure α} {μᵣ : Measure β}
    (Hμₗ : μₗ .univ = 1) (Hμᵣ : μᵣ .univ = 1) :
    RelCoupl Set.univ μₗ μᵣ := by
  intro ⟨f, _, Hfb⟩ ⟨g, _, Hgb⟩ Hfg
  sorry
  -- show ∫⁻ a, f a ∂μₗ ≤ ∫⁻ b, g b ∂μᵣ + 0
  -- rw [add_zero]
  -- -- ∫⁻ f dμ ≤ ⨆ a, f a
  -- -- ∫⁻ f dμ ≤ ⨆ a, f a  (since μₗ is a prob measure)
  -- have hf_le_sup : ∫⁻ a, f a ∂μₗ ≤ ⨆ a, f a :=
  --   (lintegral_le_iSup_mul f).trans (by rw [Hμₗ, mul_one])
  -- -- ⨆ a, f a ≤ ⨅ b, g b  (since ∀ a b, f a ≤ g b)
  -- have hlt : ⨆ a, f a ≤ ⨅ b, g b :=
  --   iSup_le fun a => le_iInf fun b => Hfg (Set.mem_univ (a, b))
  -- -- ⨅ b, g b ≤ ∫⁻ g dμ'  (since μᵣ is a prob measure)
  -- have hg_ge_inf : ⨅ b, g b ≤ ∫⁻ b, g b ∂μᵣ :=
  --   (by rw [Hμᵣ, mul_one] : (⨅ b, g b) * μᵣ .univ = ⨅ b, g b) ▸ iInf_mul_le_lintegral g
  -- exact hf_le_sup.trans (hlt.trans hg_ge_inf)

/-- Exact coupling implies approximate coupling for any `ε`: just use `mono_ε`. -/
theorem exact {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : RelCoupl S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ :=
  sorry
  -- AddCoupling.mono_ε (zero_le ε) H

/-- Limit lemma: if the coupling holds for every `ε' > ε`, it holds at `ε` itself.
Equivalently, `ε` is an infimum of achievable slacks. -/
theorem limit {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ ε', ε < ε' → AddCoupl ε' S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  -- Need: a ≤ b + ε. By contradiction: if b + ε < a, pick c strictly between, then
  -- find ε' > ε with b + ε' = c (when b ≠ ∞), contradicting H.
  set a := ∫⁻ x, f.1 x ∂μₗ
  set b := ∫⁻ x, g.1 x ∂μᵣ
  -- Use: a is a lower bound for {b + ε' | ε' > ε}, which has infimum b + ε.
  suffices ∀ c > b + ε, a ≤ c from forall_gt_imp_ge_iff_le_of_dense.mp this
  intro c hc
  -- ε' = c - b satisfies ε' > ε and b + ε' = c (when b ≠ ∞; when b = ∞, a ≤ ∞ trivially)
  have hbc : b ≤ c := le_self_add.trans hc.le
  have hε' : ε < c - b := lt_tsub_iff_left.mpr (add_comm b ε ▸ hc)
  calc a ≤ b + (c - b) := H _ hε' f g Hfg
      _ = c             := add_tsub_cancel_of_le hbc

end RelCoupl
end Couplings
