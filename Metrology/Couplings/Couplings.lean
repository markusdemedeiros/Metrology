module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.UnitInterval
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.Real.OfDigits

public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

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
  unfold RelCoupl AddCoupl
  congr
  exact add_zero_eq_id.symm

theorem refl_zero (μ : Measure α) : RelCoupl (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ (refl _)

/-- Any measure `μ` is `Rcoupl`-coupled to its pushforward `μ.map h` along the graph of `h`. -/
theorem map {h : α → β} (hm : Measurable h) (μ : Measure α) :
    RelCoupl (fun v => v.2 = h v.1) μ (μ.map h) := by
  rw [relCoupl_addCoupl]
  rintro ⟨f, _, _⟩ ⟨g, gm, _⟩ Hfg
  show ∫⁻ a, f a ∂μ ≤ ∫⁻ b, g b ∂(μ.map h) + 0
  rw [add_zero]
  calc ∫⁻ a, f a ∂μ
      _ ≤ ∫⁻ a, g (h a) ∂μ := lintegral_mono fun a => Hfg rfl
      _ = ∫⁻ b, g b ∂(μ.map h) := (lintegral_map gm hm).symm

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
  rw [relCoupl_addCoupl]
  intro ⟨f, _, Hfb⟩ ⟨g, _, Hgb⟩ Hfg
  show ∫⁻ a, f a ∂μₗ ≤ ∫⁻ b, g b ∂μᵣ + 0
  rw [add_zero]
  have hf_le_sup : ∫⁻ a, f a ∂μₗ ≤ ⨆ a, f a :=
    (lintegral_le_iSup_mul f).trans (by rw [Hμₗ, mul_one])
  have hlt : ⨆ a, f a ≤ ⨅ b, g b :=
    iSup_le fun a => le_iInf fun b => Hfg (Set.mem_univ (a, b))
  have hg_ge_inf : ⨅ b, g b ≤ ∫⁻ b, g b ∂μᵣ :=
    (by rw [Hμᵣ, mul_one] : (⨅ b, g b) * μᵣ .univ = ⨅ b, g b) ▸ iInf_mul_le_lintegral g
  exact hf_le_sup.trans (hlt.trans hg_ge_inf)

/-- Exact coupling implies approximate coupling for any `ε`: just use `mono_ε`. -/
theorem exact {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : RelCoupl S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  refine AddCoupl.mono_grading (ε := 0) (zero_le) ?_
  rwa [← relCoupl_addCoupl]

/-- Limit lemma: if the coupling holds for every `ε' > ε`, it holds at `ε` itself.
Equivalently, `ε` is an infimum of achievable slacks. -/
theorem limit {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ ε', ε < ε' → AddCoupl ε' S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  set a := ∫⁻ x, f.1 x ∂μₗ
  set b := ∫⁻ x, g.1 x ∂μᵣ
  suffices ∀ c > b + ε, a ≤ c from forall_gt_imp_ge_iff_le_of_dense.mp this
  intro c hc
  have hbc : b ≤ c := le_self_add.trans hc.le
  have hε' : ε < c - b := lt_tsub_iff_left.mpr (add_comm b ε ▸ hc)
  calc a ≤ b + (c - b) := H _ hε' f g Hfg
      _ = c             := add_tsub_cancel_of_le hbc

end RelCoupl
end Couplings
