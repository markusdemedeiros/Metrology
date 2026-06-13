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

public import Metrology.Couplings.ApproximateCouplings

@[expose] public section

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

/-- **Advanced-composition bind**: the continuation's slack is allowed to
depend on the RHS sample, and the final slack is bounded by the expected
value of the variable slack plus the outer slack.

Compared to `bind`, the key difference is that the continuation hypothesis
`Hbind` provides `AddCoupl (E₂ b) T (f a) (g b)` with `E₂ b` depending on
the RHS sample, and we only need `∫⁻ b, E₂ b ∂μᵣ ≤ ε'` (the expected
slack). This is weaker than requiring a pointwise bound. -/
theorem bind_adv {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : β → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g) (HE₂m : Measurable E₂)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ b, E₂ b ∂μᵣ ≤ ε')
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ b) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a :=
    calc ∫⁻ y, f' y ∂f a
      _ ≤ (f a) .univ := lintegral_le_meas Hf'b (by simp)
      _ ≤ 1 := Hfsprob _
  -- Core idea: define Fh a := ∫ f' ∂(f a), Gh b := (∫ g' ∂(g b)) + E₂ b,
  -- capped at 1. Then `S a b → Fh a ≤ Gh b` because the inner coupling
  -- gives `∫ f' ∂(f a) ≤ ∫ g' ∂(g b) + E₂ b`. We use `Hcpl` to get
  -- `∫ Fh ∂μₗ ≤ ∫ Gh ∂μᵣ + ε`. The RHS expands to `∫ (∫ g') ∂μᵣ + ∫ E₂ ∂μᵣ + ε`,
  -- which is bounded by the target `∫ (∫ g') ∂μᵣ + (ε + ε')` via `HE₂sum`.
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a)) ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact (measurable_lintegral Hf'm |>.comp Hfm)
  case Fb => exact HFle a
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b) + E₂ b) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm =>
    refine Measurable.inf ?_ measurable_const
    exact ((measurable_lintegral Hg'm).comp Hgm).add HE₂m
  case Gb => exact inf_le_right
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    have Hinner : ∫⁻ y, f' y ∂(f a) ≤ ∫⁻ y, g' y ∂(g b) + E₂ b :=
      Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
    simp only [Fh, Gh, le_inf_iff]
    exact ⟨Hinner, (HFle a).trans (by simp)⟩
  -- Apply the outer coupling to Fh, Gh.
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ = ∫⁻ a, Fh.1 a ∂μₗ := by rfl
      _ ≤ ∫⁻ b, Gh.1 b ∂μᵣ + ε := Hcpl Fh Gh HFhGh
      _ ≤ ∫⁻ b, (∫⁻ x, g' x ∂(g b) + E₂ b) ∂μᵣ + ε := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ∫⁻ b, E₂ b ∂μᵣ + ε := by
            rw [lintegral_add_right _ HE₂m]
      _ ≤ ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε' + ε := by
            gcongr
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc, add_comm ε' ε]

/-- Advanced-composition bind with **LHS-indexed variable slack**: the
continuation's slack `E₂` depends on the LHS sample `a`, and the final
slack is bounded by `ε + ε'` where `∫⁻ a, E₂ a ∂μₗ ≤ ε'`.

This is the LHS-symmetric companion of `bind_adv`. -/
theorem bind_adv_lhs {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : α → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g) (HE₂m : Measurable E₂)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ a, E₂ a ∂μₗ ≤ ε')
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ a) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a :=
    calc ∫⁻ y, f' y ∂f a
      _ ≤ (f a) .univ := lintegral_le_meas Hf'b (by simp)
      _ ≤ 1 := Hfsprob _
  -- Define Fh a := max(0, ∫ f' ∂f a - E₂ a) so that the inner coupling
  -- `∫ f' ∂(f a) ≤ ∫ g' ∂(g b) + E₂ a` gives `Fh a ≤ ∫ g' ∂(g b)`.
  -- For the outer `Hcpl` application, we take Gh b := ∫ g' ∂g b (capped at 1).
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a) - E₂ a)
    ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact ((measurable_lintegral Hf'm |>.comp Hfm)).sub HE₂m
  case Fb => exact (tsub_le_self).trans (HFle a)
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b)) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm => exact (measurable_lintegral Hg'm |>.comp Hgm).inf measurable_const
  case Gb => exact inf_le_right
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    have Hinner : ∫⁻ y, f' y ∂(f a) ≤ ∫⁻ y, g' y ∂(g b) + E₂ a :=
      Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
    simp only [Fh, Gh, le_inf_iff]
    refine ⟨?_, ?_⟩
    · exact tsub_le_iff_right.mpr Hinner
    · exact (tsub_le_self).trans (HFle a)
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ ≤ ∫⁻ a, Fh.1 a + E₂ a ∂μₗ := by
            refine lintegral_mono (fun a => ?_); exact le_tsub_add
      _ = ∫⁻ a, Fh.1 a ∂μₗ + ∫⁻ a, E₂ a ∂μₗ := by
            rw [lintegral_add_right _ HE₂m]
      _ ≤ ∫⁻ a, Fh.1 a ∂μₗ + ε' := by gcongr
      _ ≤ (∫⁻ b, Gh.1 b ∂μᵣ + ε) + ε' := by
            gcongr
            exact Hcpl Fh Gh HFhGh
      _ ≤ (∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε) + ε' := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc]

/-- **Kantorovich-style bind, plain variant**: advanced composition with
bilateral variable slack `E₂ : α → β → ENNReal`. Mirrors Rocq
`ARcoupl_dbind_adv_kanto_plain` (couplings_app.v:114–221).

The outer distributions are coupled by a *test-function expectation bound*
rather than by a separate `AddCoupl`: for every pair of `[0,1]`-bounded
measurable `h₁, h₂` satisfying `h₁ a ≤ h₂ b + E₂ a b` pointwise, the
expectations satisfy `∫⁻ h₁ ∂μ₁ ≤ ∫⁻ h₂ ∂μ₂ + ε`. Together with inner
couplings `AddCoupl (E₂ a b) S (f a) (g b)` at every pair, this yields
`AddCoupl ε S (μ₁.bind f) (μ₂.bind g)`. -/
theorem bind_adv_kanto {ε : ENNReal} {S : Set (α' × β')}
    {μ₁ : Measure α} {μ₂ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : α → β → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1) (Hgsprob : ∀ b, (g b) .univ ≤ 1)
    (Hexp : ∀ (h₁ : α → ENNReal) (h₂ : β → ENNReal),
        Measurable h₁ → Measurable h₂ →
        (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
        (∀ a b, h₁ a ≤ h₂ b + E₂ a b) →
        ∫⁻ a, h₁ a ∂μ₁ ≤ ∫⁻ b, h₂ b ∂μ₂ + ε)
    (Hcont : ∀ a b, AddCoupl (E₂ a b) S (f a) (g b)) :
    AddCoupl ε S (μ₁.bind f) (μ₂.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  -- Define the inner-integral functions X a := ∫ f' ∂f a, Y b := ∫ g' ∂g b.
  -- Both are `[0,1]`-bounded thanks to subprobability of f a / g b.
  let X : α → ENNReal := fun a => ∫⁻ x, f' x ∂(f a)
  let Y : β → ENNReal := fun b => ∫⁻ y, g' y ∂(g b)
  have HXm : Measurable X := (measurable_lintegral Hf'm).comp Hfm
  have HYm : Measurable Y := (measurable_lintegral Hg'm).comp Hgm
  have HXb : ∀ a, X a ≤ 1 := fun a =>
    (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  have HYb : ∀ b, Y b ≤ 1 := fun b =>
    (lintegral_le_meas Hg'b (by simp)).trans (Hgsprob b)
  -- Pointwise: X a ≤ Y b + E₂ a b, from the inner couplings at (a, b).
  have HXY : ∀ a b, X a ≤ Y b + E₂ a b := fun a b =>
    Hcont a b ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  -- Apply the expectation hypothesis to X, Y — this closes the outer integral.
  have Hmain : ∫⁻ a, X a ∂μ₁ ≤ ∫⁻ b, Y b ∂μ₂ + ε :=
    Hexp X Y HXm HYm HXb HYb HXY
  -- Push the bind through the outer integrals.
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  exact Hmain

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

/-! ### Stubs — lemmas needed by Approxis, to be proved on demand.

These parallel the Rocq `couplings_app.v` / `couplings_kanto.v` API. Grouped by
tier of priority for unblocking the Approxis port. -/

section Stubs

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

/-! #### Tier 1 — core plumbing (blocks `app_weakestpre`, `adequacy`). -/

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- Pointed `dret`/`dirac` variant: if `R (f a) (g b)` then the pushforward Diracs are
coupled. Specialization of `AddCoupl.dirac`. -/
theorem dret {ε : ENNReal} {R : α' → β' → Prop} {a : α} {b : β}
    (f : α → α') (g : β → β') (H : R (f a) (g b)) :
    AddCoupl ε (fun v => R v.1 v.2) (Measure.dirac (f a)) (Measure.dirac (g b)) :=
  AddCoupl.dirac (ε := ε) _ H

/-- Push an `AddCoupl` through measurable maps. The Rocq form is
`ARcoupl_map : ARcoupl μ₁ μ₂ R ε → ARcoupl (dmap f μ₁) (dmap g μ₂) (λ a' b', ∃ a b, ...) ε`. -/
theorem map {ε : ENNReal} {S : Set (α × β)} {R : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} (f : α → α') (g : β → β')
    (Hfm : Measurable f) (Hgm : Measurable g)
    (HR : ∀ {a b}, S (a, b) → R (f a, g b))
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε R (μₗ.map f) (μᵣ.map g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  let F : CouplingFunction α := .mk (f' ∘ f) ⟨Hf'm.comp Hfm, fun _ => Hf'b _⟩
  let G : CouplingFunction β := .mk (g' ∘ g) ⟨Hg'm.comp Hgm, fun _ => Hg'b _⟩
  have HFG {a b} (HS : S (a, b)) : F.1 a ≤ G.1 b := Hle (HR HS)
  rw [MeasureTheory.lintegral_map Hf'm Hfm, MeasureTheory.lintegral_map Hg'm Hgm]
  exact H F G HFG

/-- Inverse of `AddCoupl.map`: pulling back along measurable maps.

Specialized to countable discrete spaces on the codomain side (so every function on
`α'` / `β'` is measurable). The trick: lift `f'` to `fT(a') := ⨆_{a : f a = a'} f'(a)` and
`g'` to `gT(b') := ⨅_{b : g b = b'} g'(b)` (capped at 1). -/
theorem map_inv [Countable α'] [Countable β']
    [MeasurableSingletonClass α'] [MeasurableSingletonClass β']
    {ε : ENNReal} {R : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} (f : α → α') (g : β → β')
    (Hfm : Measurable f) (Hgm : Measurable g)
    (H : AddCoupl ε R (μₗ.map f) (μᵣ.map g)) :
    AddCoupl ε (fun v => R (f v.1, g v.2)) μₗ μᵣ := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  -- Lift f' to α' via supremum over the fiber; g' via infimum capped at 1.
  let fT : α' → ENNReal := fun a' => ⨆ (a : α) (_ : f a = a'), f' a
  let gT : β' → ENNReal := fun b' => (⨅ (b : β) (_ : g b = b'), g' b) ⊓ 1
  have HfTm : Measurable fT := measurable_of_countable _
  have HgTm : Measurable gT := measurable_of_countable _
  have HfTb : ∀ a', fT a' ≤ 1 := fun a' =>
    iSup_le fun a => iSup_le fun _ => Hf'b a
  have HgTb : ∀ b', gT b' ≤ 1 := fun b' => inf_le_right
  let FT : CouplingFunction α' := ⟨fT, HfTm, HfTb⟩
  let GT : CouplingFunction β' := ⟨gT, HgTm, HgTb⟩
  -- Relation: R(a',b') → fT(a') ≤ gT(b').
  have HFG : ∀ {a' b'}, R (a', b') → FT.1 a' ≤ GT.1 b' := by
    intro a' b' HR
    simp only [FT, GT, fT, gT, le_inf_iff]
    refine ⟨?_, HfTb a'⟩
    refine iSup_le fun a => iSup_le fun Ha => ?_
    refine le_iInf fun b => le_iInf fun Hb => ?_
    -- R(fa, gb) since fa = a', gb = b', and R(a', b').
    exact Hle (by subst Ha; subst Hb; exact HR)
  -- Pointwise: f' a ≤ fT (f a)
  have Hf'_le : ∀ a, f' a ≤ fT (f a) := fun a => by
    simp only [fT]; exact le_iSup_of_le a (le_iSup_of_le rfl le_rfl)
  -- Pointwise: gT (g b) ≤ g' b
  have HgT_le : ∀ b, gT (g b) ≤ g' b := fun b => by
    simp only [gT]
    calc (⨅ (b' : β) (_ : g b' = g b), g' b') ⊓ 1
        ≤ (⨅ (b' : β) (_ : g b' = g b), g' b') := inf_le_left
      _ ≤ g' b := iInf_le_of_le b (iInf_le_of_le rfl le_rfl)
  -- Assemble: ∫ f' dμₗ ≤ ∫ fT∘f dμₗ = ∫ fT d(μₗ.map f) ≤ ∫ gT d(μᵣ.map g) + ε
  --                                  = ∫ gT∘g dμᵣ + ε ≤ ∫ g' dμᵣ + ε.
  calc ∫⁻ a, f' a ∂μₗ
      ≤ ∫⁻ a, fT (f a) ∂μₗ := lintegral_mono Hf'_le
    _ = ∫⁻ a', fT a' ∂(μₗ.map f) := (MeasureTheory.lintegral_map HfTm Hfm).symm
    _ ≤ ∫⁻ b', gT b' ∂(μᵣ.map g) + ε := H FT GT HFG
    _ = ∫⁻ b, gT (g b) ∂μᵣ + ε := by
          rw [MeasureTheory.lintegral_map HgTm Hgm]
    _ ≤ ∫⁻ b, g' b ∂μᵣ + ε := by
          gcongr
          · exact HgT_le _

/-- Strengthen the relation to its intersection with the product of supports.

Specialized to countable discrete measurable spaces, matching Rocq's setting. In general
measure-theoretic land this statement is false for continuous measures (every singleton
has measure zero). -/
theorem pos_R [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S v ∧ μₗ {v.1} ≠ 0 ∧ μᵣ {v.2} ≠ 0) μₗ μᵣ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  -- Modified test functions: zero out `f` off μₗ-atoms; set `g` to 1 off μᵣ-atoms.
  let f' : α → ENNReal := fun a => if μₗ {a} = 0 then 0 else f a
  let g' : β → ENNReal := fun b => if μᵣ {b} = 0 then 1 else g b
  -- Countable + MeasurableSingletonClass makes every function measurable.
  have Hf'm : Measurable f' := measurable_of_countable _
  have Hg'm : Measurable g' := measurable_of_countable _
  have Hf'b : ∀ a, f' a ≤ 1 := fun a => by
    simp only [f']; split_ifs
    · exact zero_le_one
    · exact Hfb a
  have Hg'b : ∀ b, g' b ≤ 1 := fun b => by
    simp only [g']; split_ifs
    · exact le_refl _
    · exact Hgb b
  let F : CouplingFunction α := ⟨f', Hf'm, Hf'b⟩
  let G : CouplingFunction β := ⟨g', Hg'm, Hg'b⟩
  -- Key: F a ≤ G b on S. Three cases on the ifs.
  have HFG : ∀ {a b}, S (a, b) → F.1 a ≤ G.1 b := by
    intro a b HS
    simp only [F, G, f', g']
    split_ifs with Hμa Hμb Hμb
    · exact zero_le
    · exact zero_le
    · exact (Hfb a).trans (le_refl _)
    · exact Hle ⟨HS, Hμa, Hμb⟩
  -- Now show ∫ f dμₗ = ∫ f' dμₗ via countable decomposition.
  have Hfeq : ∫⁻ a, f a ∂μₗ = ∫⁻ a, f' a ∂μₗ := by
    rw [MeasureTheory.lintegral_countable' f, MeasureTheory.lintegral_countable' f']
    refine tsum_congr (fun a => ?_)
    by_cases Hμa : μₗ {a} = 0
    · simp [f', Hμa]
    · simp [f', Hμa]
  have Hgeq : ∫⁻ b, g b ∂μᵣ = ∫⁻ b, g' b ∂μᵣ := by
    rw [MeasureTheory.lintegral_countable' g, MeasureTheory.lintegral_countable' g']
    refine tsum_congr (fun b => ?_)
    by_cases Hμb : μᵣ {b} = 0
    · simp [g', Hμb]
    · simp [g', Hμb]
  rw [Hfeq, Hgeq]
  exact H F G HFG

/-- Exact couplings embed into approximate couplings at any `ε`. -/
theorem of_RelCoupl {ε : ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β}
    (H : ARCoupling (fun x => x) S μₗ μᵣ) :
    AddCoupl ε S μₗ μᵣ :=
  ARCoupling.mono_F (fun _ => le_self_add) H

/-- Limit/closure: an `AddCoupl` at every `ε + δ` (for `δ > 0`) implies one at `ε`. -/
theorem limit {ε : ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ δ : ENNReal, 0 < δ → AddCoupl (ε + δ) S μₗ μᵣ) :
    AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  have Hδ : ∀ δ : ENNReal, 0 < δ → ∫⁻ x, f x ∂μₗ ≤ (∫⁻ x, g x ∂μᵣ + ε) + δ := by
    intro δ Hδpos
    have := H δ Hδpos f g Hfg
    rw [show (∫⁻ x, g x ∂μᵣ + ε) + δ = ∫⁻ x, g x ∂μᵣ + (ε + δ) by ring]
    exact this
  exact ENNReal.le_of_forall_pos_le_add (fun δ Hδpos _ =>
    Hδ δ (by exact_mod_cast Hδpos))

/-- Zero-measure couplings on the right when the slack absorbs the LHS mass. -/
theorem dzero {ε : ENNReal} (S : Set (α × β)) (μᵣ : Measure β) :
    AddCoupl ε S (0 : Measure α) μᵣ :=
  AddCoupl.zero_left S μᵣ

/-- Two zero measures are coupled at any relation and slack. -/
theorem dzero_dzero {ε : ENNReal} (S : Set (α × β)) :
    AddCoupl ε S (0 : Measure α) (0 : Measure β) :=
  AddCoupl.zero_left S 0

/-- Inverse direction: coupling to zero forces the LHS mass bound. -/
theorem dzero_r_inv {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α}
    (H : AddCoupl ε S μₗ (0 : Measure β)) : μₗ .univ ≤ ε := by
  have := AddCoupl.mass_leq H
  simpa using this

/-- Antisymmetry: mutual `AddCoupl 0` at equality implies measure equality. -/
theorem antisym {μ₁ μ₂ : Measure α}
    (H₁ : AddCoupl 0 (fun v => v.1 = v.2) μ₁ μ₂)
    (H₂ : AddCoupl 0 (fun v => v.1 = v.2) μ₂ μ₁) : μ₁ = μ₂ := by
  refine MeasureTheory.Measure.ext fun A HA => ?_
  -- Test with the indicator of A. Indicator values are in {0,1} ⊆ [0,1].
  let χ : CouplingFunction α :=
    ⟨A.indicator (fun _ => 1), Measurable.indicator measurable_const HA, fun a => by
      simp only [Set.indicator]; split_ifs
      · exact le_refl _
      · exact zero_le⟩
  have Hle : ∀ {a b : α}, a = b → χ.1 a ≤ χ.1 b := fun h => h ▸ le_refl _
  have H12 := H₁ χ χ Hle
  have H21 := H₂ χ χ Hle
  simp only [add_zero] at H12 H21
  have Hχint : ∀ μ : Measure α, ∫⁻ x, χ.1 x ∂μ = μ A := fun μ => by
    simp only [χ, MeasureTheory.lintegral_indicator HA, MeasureTheory.lintegral_const,
      MeasureTheory.Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, one_mul]
  rw [Hχint μ₁, Hχint μ₂] at H12
  rw [Hχint μ₂, Hχint μ₁] at H21
  exact le_antisymm H12 H21

/-- Swap the arguments of an `AddCoupl`. Requires equal total masses and both measures
sub-probability — without those the asymmetric inequality cannot flip. Standard proof
tests the original coupling against `(1-g, 1-f)` and uses `∫(1-h) = μ.univ - ∫h`. -/
theorem swap {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (Hmass : μₗ .univ = μᵣ .univ) (HμₗP : μₗ .univ ≤ 1) (HμᵣP : μᵣ .univ ≤ 1)
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S (v.2, v.1)) μᵣ μₗ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  -- Apply H at F := (fun a => 1 - g a), G := (fun b => 1 - f b).
  let F : CouplingFunction α :=
    ⟨fun a => 1 - g a, measurable_const.sub Hgm, fun _ => tsub_le_self⟩
  let G : CouplingFunction β :=
    ⟨fun b => 1 - f b, measurable_const.sub Hfm, fun _ => tsub_le_self⟩
  have HFG : ∀ {a b}, S (a, b) → F.1 a ≤ G.1 b := fun HS =>
    tsub_le_tsub_left (Hle HS) 1
  have Hcpl := H F G HFG
  -- ∫(1-h) dμ = μ.univ - ∫h dμ  (when ∫h ≤ μ.univ < ∞).
  have Hgint_le : (∫⁻ a, g a ∂μₗ) ≤ μₗ .univ := lintegral_le_meas Hgb (by simp)
  have Hfint_le : (∫⁻ b, f b ∂μᵣ) ≤ μᵣ .univ := lintegral_le_meas Hfb (by simp)
  have HμL_ne : μₗ .univ ≠ ⊤ := ne_top_of_le_ne_top (by simp) HμₗP
  have HμR_ne : μᵣ .univ ≠ ⊤ := ne_top_of_le_ne_top (by simp) HμᵣP
  have HFint : ∫⁻ a, (1 - g a) ∂μₗ = μₗ .univ - ∫⁻ a, g a ∂μₗ := by
    rw [MeasureTheory.lintegral_sub Hgm (ne_of_lt (lt_of_le_of_lt Hgint_le HμL_ne.lt_top))
      (ae_of_all _ Hgb)]
    simp
  have HGint : ∫⁻ b, (1 - f b) ∂μᵣ = μᵣ .univ - ∫⁻ b, f b ∂μᵣ := by
    rw [MeasureTheory.lintegral_sub Hfm (ne_of_lt (lt_of_le_of_lt Hfint_le HμR_ne.lt_top))
      (ae_of_all _ Hfb)]
    simp
  rw [HFint, HGint] at Hcpl
  -- Hcpl : μₗ.univ - ∫g ≤ (μᵣ.univ - ∫f) + ε
  -- Goal: ∫f dμᵣ ≤ ∫g dμₗ + ε
  -- Using Hmass, substitute μᵣ.univ → μₗ.univ, then use ENNReal.sub_le_sub_iff_right / add arithmetic.
  rw [← Hmass] at Hcpl
  -- Hcpl : μₗ.univ - ∫g ≤ (μₗ.univ - ∫f) + ε
  -- Since ∫f, ∫g ≤ μₗ.univ < ∞, this is equivalent to ∫f ≤ ∫g + ε.
  have Hfint_le' : (∫⁻ b, f b ∂μᵣ) ≤ μₗ .univ := Hmass ▸ Hfint_le
  -- Rearrange: add ∫g dμₗ to both sides of Hcpl: μₗ.univ ≤ (μₗ.univ - ∫f) + ε + ∫g.
  --            Then use tsub_le_iff_left: ∫f ≤ (something).
  -- Cleanest: ENNReal arithmetic via `tsub_le_iff_right` and `le_tsub_add`.
  -- Equivalent formulation: μₗ.univ + (∫f + 0) ≤ μₗ.univ + (∫g + ε).
  -- Use add_le_add_iff_left (requires finiteness).
  -- Name the integrals for legibility.
  set IF := ∫⁻ b, f b ∂μᵣ with hIF
  set IG := ∫⁻ a, g a ∂μₗ with hIG
  set M := μₗ .univ with hM
  -- Hcpl : M - IG ≤ (M - IF) + ε. Goal: IF ≤ IG + ε.
  -- Step 1: add IG to both sides → M ≤ (M - IF) + ε + IG (using IG ≤ M)
  have Step1 : M ≤ (M - IF) + ε + IG := by
    calc M = (M - IG) + IG := (tsub_add_cancel_of_le Hgint_le).symm
      _ ≤ ((M - IF) + ε) + IG := by gcongr
  -- Step 2: add IF both sides → M + IF ≤ M + ε + IG
  have Step2 : M + IF ≤ M + ε + IG := by
    calc M + IF ≤ ((M - IF) + ε + IG) + IF := by gcongr
      _ = ((M - IF) + IF) + (ε + IG) := by ring_nf
      _ = M + (ε + IG) := by rw [tsub_add_cancel_of_le Hfint_le']
      _ = M + ε + IG := by ring_nf
  -- Step 3: cancel M on the left.
  have Step3 : IF ≤ ε + IG := ENNReal.le_of_add_le_add_left HμL_ne (by
    calc M + IF ≤ M + ε + IG := Step2
      _ = M + (ε + IG) := by ring_nf)
  calc IF ≤ ε + IG := Step3
    _ = IG + ε := by ring_nf

end Stubs

/-- Trivial coupling: if the LHS has mass at most 1 and `1 ≤ ε`, then any
`AddCoupl` claim holds — the LHS mass is absorbed by the slack alone.
Rocq analogue: `ARcoupl_1`. -/
theorem trivial_of_one_le {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α}
    {μᵣ : Measure β} (Hε : 1 ≤ ε) (Hmass : μₗ Set.univ ≤ 1) :
    AddCoupl ε S μₗ μᵣ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ _Hle
  calc ∫⁻ x, f x ∂μₗ
      _ ≤ μₗ Set.univ := lintegral_le_meas Hfb (by simp)
      _ ≤ 1 := Hmass
      _ ≤ ε := Hε
      _ ≤ ∫⁻ y, g y ∂μᵣ + ε := le_add_self

end AddCoupl
