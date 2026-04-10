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

import Metrology.Couplings.ApproximateCouplings

section AdditiveCoupling

open MeasureTheory Measure

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

/-- Approximate relational coupling with additive error slack `ε`. -/
def AddCoupl (ε : ENNReal) (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling (· + ε) Φ μₗ μᵣ

namespace AddCoupl

/-- Reflexivity of `ARcoupl` at the equality relation. -/
theorem refl {ε : ENNReal} (μ : Measure α) : AddCoupl ε (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ le_self_add

/-- Dirac coupling: two point masses are `ARcoupl ε`-related for any `ε` as long as the
relation holds on the points. -/
theorem dirac {ε : ENNReal} {a : α} {b : β} (S : Set (α × β)) (H : S (a, b)) :
    AddCoupl ε S (.dirac a) (.dirac b) :=
  ARCoupling.dirac le_self_add S H

/-- Enlarging the relation weakens the coupling. -/
theorem mono_rel {ε : ENNReal} {S S' : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (HS : S ⊆ S') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε S' μₗ μᵣ :=
  ARCoupling.mono_rel HS H

/-- Enlarging the error slack weakens the coupling. -/
theorem mono_grading {ε ε' : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (Hε : ε ≤ ε') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε' S μₗ μᵣ :=
  ARCoupling.mono_F (fun x => by gcongr) H

/-- The zero measure is trivially coupled on the left. -/
theorem zero_left {ε : ENNReal} (S : Set (α × β)) (μᵣ : Measure β) : AddCoupl ε S 0 μᵣ :=
  ARCoupling.zero_left S μᵣ

/-- Coupling against the zero measure on the right requires `μₗ .univ ≤ ε`. -/
theorem zero_right {ε : ENNReal} (S : Set (α × β)) {μₗ : Measure α} (Hε : μₗ .univ ≤ ε) :
    AddCoupl ε S μₗ 0 :=
  ARCoupling.zero_right S (by simpa using Hε)

/-- Monad bind for `ARcoupl`: the error slacks add.

Given `ARcoupl ε` between `μₗ` and `μᵣ`, and `ARcoupl ε'` between `f a` and `g b` whenever
`S (a, b)`, we get `ARcoupl (ε + ε')` between the bound measures `μₗ.bind f` and `μᵣ.bind g`,
provided `μₗ` and each `f a` are sub-probability measures. -/
theorem bind {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}{μₗ : Measure α} {μᵣ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'}
    (Hfm : Measurable f) (Hgm : Measurable g)
    (Hμₗ : μₗ .univ ≤ 1) (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl ε' T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a :=
    calc ∫⁻ y, f' y ∂f a
      _ ≤ (f a) .univ := lintegral_le_meas Hf'b (by simp)
      _ ≤ 1 := Hfsprob _
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a) - ε') ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact (measurable_lintegral Hf'm |>.comp Hfm).sub measurable_const
  case Fb => exact (tsub_le_self).trans (HFle a)
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b)) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm => exact (measurable_lintegral Hg'm |>.comp Hgm).inf measurable_const
  case Gb => exact inf_le_right
  /- The key pointwise inequality on `S`: `Fh a ≤ Gh b`. -/
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    have Hinner : ∫⁻ y, f' y ∂(f a) ≤ ∫⁻ y, g' y ∂(g b) + ε' :=
      Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
    simp only [Fh, Gh, le_inf_iff]
    refine ⟨tsub_le_iff_right.mpr Hinner, ?_⟩
    exact tsub_le_iff_right.mpr ((HFle a).trans le_self_add)
  /- Main inequality. -/
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc  ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ ≤ ∫⁻ a, Fh.1 a + ε' ∂μₗ := by
            refine lintegral_mono (fun a => ?_); exact le_tsub_add
      _ = ∫⁻ a, Fh.1 a ∂μₗ + ε' * μₗ .univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, mul_comm]
      _ ≤ ∫⁻ a, Fh.1 a ∂μₗ + ε' := by
            gcongr
            exact mul_le_of_le_one_right' Hμₗ
      _ ≤ (∫⁻ b, Gh.1 b ∂μᵣ + ε) + ε' := by
            gcongr
            exact Hcpl Fh Gh HFhGh
      _ ≤ (∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε) + ε' := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc]

/-- Mass comparison: `ARcoupl ε` bounds the total mass of `μₗ` by that of `μᵣ` plus `ε`.
Obtained by testing against the constant-`1` coupling function. -/
theorem mass_leq {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : AddCoupl ε S μₗ μᵣ) : μₗ .univ ≤ μᵣ .univ + ε := by
  let oneA : CouplingFunction α := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  let oneB : CouplingFunction β := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  have h := H oneA oneB (fun _ => le_refl _)
  rwa [show (∫⁻ _, oneA.1 _ ∂μₗ) = μₗ .univ from by
        simp [oneA, lintegral_const],
      show (∫⁻ _, oneB.1 _ ∂μᵣ) = μᵣ .univ from by
        simp [oneB, lintegral_const]] at h

/-- Left transitivity with an equality-coupling: chain an exact-equality coupling into an
arbitrary coupling, adding the error slacks. -/
theorem eq_trans_l {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ μ₂ : Measure α} {μ₃ : Measure β}
    (Heq : AddCoupl ε₁ (fun v => v.1 = v.2) μ₁ μ₂) (HR : AddCoupl ε₂ R μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  -- Chain: ∫⁻ f dμ₁ ≤ ∫⁻ f dμ₂ + ε₁ ≤ (∫⁻ g dμ₃ + ε₂) + ε₁ = ∫⁻ g dμ₃ + (ε₁ + ε₂)
  have step1 : ∫⁻ x, f.1 x ∂μ₁ ≤ ∫⁻ x, f.1 x ∂μ₂ + ε₁ :=
    Heq f f (fun {a b} (h : a = b) => h ▸ le_refl _)
  have step2 : ∫⁻ x, f.1 x ∂μ₂ ≤ ∫⁻ x, g.1 x ∂μ₃ + ε₂ := HR f g Hfg
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, f.1 x ∂μ₂ + ε₁ := step1
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by gcongr
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

/-- Right transitivity with an equality-coupling: chain an arbitrary coupling into an
exact-equality coupling, adding the error slacks. -/
theorem eq_trans_r {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ : Measure α} {μ₂ μ₃ : Measure β}
    (HR : AddCoupl ε₁ R μ₁ μ₂) (Heq : AddCoupl ε₂ (fun v => v.1 = v.2) μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  have step1 : ∫⁻ x, f.1 x ∂μ₁ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := HR f g Hfg
  have step2 : ∫⁻ x, g.1 x ∂μ₂ ≤ ∫⁻ x, g.1 x ∂μ₃ + ε₂ :=
    Heq g g (fun {a b} (h : a = b) => h ▸ le_refl _)
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := step1
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by gcongr
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

end AddCoupl
