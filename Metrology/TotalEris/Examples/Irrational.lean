module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Mathlib.Topology.Instances.Irrational
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.Invariants

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS MeasureTheory HeapView Auth
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

noncomputable def irratErr : ℝ → ℝ≥0∞ :=
  {r : ℝ | ¬ Irrational r}.indicator (fun _ => 1)

@[simp]
theorem irratErr_irr {r : ℝ} (h : Irrational r) : irratErr r = 0 := by
  rw [irratErr, Set.indicator_of_notMem (by simpa using h)]

@[simp]
theorem irratErr_rat {r : ℝ} (h : ¬ Irrational r) : irratErr r = 1 := by
  rw [irratErr, Set.indicator_of_mem h]

theorem measurableSet_not_irrational : MeasurableSet {r : ℝ | ¬ Irrational r} :=
  (IsGδ.setOf_irrational.measurableSet).compl.congr (by ext r; simp)

theorem irratErr_measurable : Measurable irratErr :=
  measurable_const.indicator measurableSet_not_irrational

theorem irratErr_le_one (r : ℝ) : irratErr r ≤ 1 := by
  by_cases h : Irrational r <;> simp [h]

theorem irratErr_lintegral_zero : ∫⁻ r, irratErr r ∂(ProbLangℝ.unifUnit (T := ℝ)) = 0 := by
  rw [irratErr, lintegral_indicator_const measurableSet_not_irrational, one_mul]
  show volume.restrict (Set.Icc (0 : ℝ) 1) {r : ℝ | ¬ Irrational r} = 0
  rw [Measure.restrict_apply measurableSet_not_irrational]
  refine measure_mono_null Set.inter_subset_left ?_
  refine _root_.Set.Countable.measure_zero ?_ volume
  have Hrw : {r : ℝ | ¬ Irrational r} = Set.range ((↑) : ℚ → ℝ) := by
    ext r; simp [Irrational]
  rw [Hrw]
  exact Set.countable_range _

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]

/-- `urand` samples irrational values with probability 1 -/
theorem twp_urand_irrational (E : CoPset) :
    ⊢@{IProp GF} tglWp E pl(urand)
       (fun w => iprop% ⌜∃ r : ℝ, w = .real r ∧ Irrational r⌝) := by
  iapply twp_err_pos solve_not_red
  iintro %ε %Hε Herr
  iapply (twp_urand_exp irratErr_measurable irratErr_le_one ?Gexp) $$ Herr
  case Gexp => simp [irratErr_lintegral_zero]
  iintro %r Hcr
  by_cases h : Irrational r
  · ipureintro; exact ⟨r, rfl, h⟩
  · iexfalso
    iapply ec_contradict $$ Hcr
    rw [irratErr_rat h]

end Wp



/-! Adequacy -/

theorem measurableSet_irrational_val :
    MeasurableSet {v : Val ℝ | ∃ r : ℝ, v = .real r ∧ Irrational r} := by
  rw [show {v : Val ℝ | ∃ r : ℝ, v = .real r ∧ Irrational r}
        = Val.fst ⁻¹' {e : Exp ℝ | ∃ r : ℝ, e = .lit (.real r) ∧ Irrational r} by
      ext v; simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨r, rfl, hr⟩; exact ⟨r, rfl, hr⟩
      · rintro ⟨r, hvr, hr⟩; exact ⟨r, Val.ext hvr, hr⟩]
  refine Val.fst.measurable ?_
  rw [show {e : Exp ℝ | ∃ r : ℝ, e = .lit (.real r) ∧ Irrational r}
        = (fun r : ℝ => (Exp.lit (.real r) : Exp ℝ)) '' {r | Irrational r} by
      ext e; simp only [Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨r, he, hr⟩ => ⟨r, hr, he.symm⟩, fun ⟨r, hr, he⟩ => ⟨r, he.symm, hr⟩⟩]
  exact (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding).measurableSet_image'
    IsGδ.setOf_irrational.measurableSet

theorem urand_irrational_pgl (σ : State ℝ) :
    Pgl 0 (fun ρ => ∃ v : Val ℝ,
            ρ.expr = Exp.ofVal v ∧
            ∃ r : ℝ, v = .real r ∧ Irrational r)
      (limExec ⟨pl(urand), σ⟩) := by
  refine twp_pgl_lim (GF := erisGF) (e := pl(urand)) (σ := σ)
    (φ := fun v => ∃ r : ℝ, v = .real r ∧ Irrational r)
    measurableSet_irrational_val ?_
  intro _; iintro _; iapply twp_urand_irrational

/-- info: 'ProbLang.TotalEris.urand_irrational_pgl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(info) in
#print axioms urand_irrational_pgl

end TotalEris
end ProbLang
