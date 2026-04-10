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

-- abbrev BinarySequence := ℕ → Fin 2
-- -- #synth MeasurableSpace BinarySequence
--
-- namespace BinarySequence
-- open MeasureTheory
--
-- noncomputable def expand : unitInterval → BinarySequence :=
--   fun ⟨r, _⟩ => if (r = 1) then (fun _ => 1) else Real.digits (b := 2) r
--
-- noncomputable def unexpand (b : BinarySequence) : unitInterval where
--   val := Real.ofDigits (b := 2) b
--   property := Set.mem_Icc.mpr ⟨Real.ofDigits_nonneg b, Real.ofDigits_le_one b⟩
--
-- @[simp] theorem expand_unexpand {r : unitInterval} : (expand r).unexpand = r := by
--   rcases r with ⟨v, H⟩
--   rcases Classical.em (v = 1) with (rfl|H')
--   · simp [expand, unexpand, Real.ofDigits, Real.ofDigitsTerm]
--     congr
--     -- 0.1111... = 1
--     sorry
--   · simp [expand, unexpand, H']
--     refine Real.ofDigits_digits Nat.one_lt_two ?_
--     grind
--
-- -- refine measurable_iff_comap_le.mpr ?_
-- -- apply measurable_generateFrom
--
-- def expand_measurable : Measurable expand := by
--   refine measurable_pi_iff.mpr (fun n => ?_)
--   intro S _
--   -- Inelegant
--   -- have HZ : MeasurableSet ((fun x ↦ expand x n) ⁻¹' {0}) := sorry
--   -- have HO : MeasurableSet ((fun x ↦ expand x n) ⁻¹' {1}) := sorry
--   -- have S_cases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0} ∪ {1} := by
--   --   rcases em (S 0) with (hz|hz) <;> rcases em (S 1) with (ho|ho)
--   --   · right; right; right
--   --     sorry
--   --   · sorry
--   --   · sorry
--   --   · sorry
--
--   -- unfold expand
--   -- -- Preimage of each coordinate is a measurable subset of the unit interval
--   sorry
--
-- @[simp] noncomputable def uniformIntervalSequences : Measure BinarySequence :=
--   volume.map expand
--
-- @[simp] noncomputable def BernHalf : Measure Bool :=
--   PMF.bernoulli _ (NNReal.half_le_self _) |>.toMeasure
--
-- -- theorem uniformIntervalSequences.project_bern i :
-- --     uniformIntervalSequences.map (· i) = BernHalf := by
-- --   sorry
--
-- end BinarySequence

def BoundedFunction {α : Type _} (f : α → ENNReal) : Prop :=
  ∀ a, f a ≤ 1

def CouplingFunction (α : Type _) [MeasurableSpace α] :=
  { f : α → ENNReal // Measurable f ∧ BoundedFunction f}

theorem CouplingFunction.measurable {α : Type} [MeasurableSpace α] (f : CouplingFunction α) :
    Measurable f.1 := f.property.1

theorem CouplingFunction.bounded {α : Type} [MeasurableSpace α] (f : CouplingFunction α) :
    ∀ a, f.1 a ≤ 1 := f.property.2

instance {α : Type _} [MeasurableSpace α] : CoeFun (CouplingFunction α) (fun _ => α → ENNReal) where
  coe := (·.1)

namespace MeasureTheory

section ApproximateCoupling

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

def ARCoupling (F : ENNReal → ENNReal) (S : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) :=
  ∀ (f : CouplingFunction α) (g : CouplingFunction β),
    (∀ {a b}, S (a, b) → f a ≤ g b) → ∫⁻ x, f x ∂μₗ ≤ F (∫⁻ x, g x ∂μᵣ)

theorem ARCoupling.refl {F : ENNReal → ENNReal} (μ : Measure α) (HF : ∀ {x}, x ≤ F x) :
    ARCoupling F (fun v => v.1 = v.2) μ μ :=
  fun _ _ Hle => (lintegral_mono fun _ ↦ Hle rfl).trans HF

theorem ARCoupling.dirac {F : ENNReal → ENNReal} {a : α} {b : β} (HF : ∀ {x}, x ≤ F x)
    (S : Set (α × β)) (H : S (a, b)) : ARCoupling F S (.dirac a) (.dirac b) := by
  refine fun ⟨f, Hf, _⟩ ⟨g, Hg, _⟩ Hle => ?_
  refine .trans ?_ HF
  rw [lintegral_dirac' _ Hf, lintegral_dirac' _ Hg]
  exact Hle H

/-- Enlarging the output bound `F` weakens the coupling: if `F ≤ F'` pointwise then any
`ARCoupling F S` is also an `ARCoupling F' S`. -/
theorem ARCoupling.mono_F {F F' : ENNReal → ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β} (HF : ∀ x, F x ≤ F' x)
    (H : ARCoupling F S μₗ μᵣ) : ARCoupling F' S μₗ μᵣ :=
  fun f g Hle => (H f g Hle).trans (HF _)

/-- Enlarging the relation `S` weakens the coupling: coupling under the smaller relation
implies coupling under the larger one. -/
theorem ARCoupling.mono_rel {F : ENNReal → ENNReal} {S S' : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β} (HS : S ⊆ S')
    (H : ARCoupling F S μₗ μᵣ) : ARCoupling F S' μₗ μᵣ :=
  fun f g Hle => H f g fun hab => Hle (HS hab)

/-- The zero measure is trivially coupled on the left: `∫⁻ f ∂0 = 0 ≤ F _`. -/
theorem ARCoupling.zero_left {F : ENNReal → ENNReal} (S : Set (α × β)) (μᵣ : Measure β) :
    ARCoupling F S (0 : Measure α) μᵣ := by
  intro _ _ _
  simp

/-- Symmetric zero case on the right: coupling against the zero measure requires the total
mass of `μₗ` to fit within the slack budget `F 0`. This is the analogue of Clutch's
`ARcoupl_dzero_r` (which needs `ε ≥ μₗ .univ`). -/
theorem ARCoupling.zero_right {F : ENNReal → ENNReal} (S : Set (α × β)) {μₗ : Measure α}
    (HF : μₗ .univ ≤ F 0) : ARCoupling F S μₗ (0 : Measure β) := by
  intro ⟨f, _, Hfb⟩ _ _
  refine (lintegral_le_meas (s := .univ) Hfb (fun _ => (·.elim trivial))).trans ?_
  refine HF.trans ?_
  simp

-- TODO: Perhaps show that couplings lift when two things are measure_eq
-- Define follow lintergal_map for this proof

end ApproximateCoupling

section AdditiveCoupling

open Measure

/-!
### ε-additive specialization (`ARcoupl`)

The specialization `ARcoupl ε := ARCoupling (· + ε)` is the approximate relational coupling
used by Clutch's Approxis. Setting `ε = 0` recovers the exact relational coupling `Rcoupl`.
Unlike the DP instantiation, the additive slack composes without truncation, so the
`bind` lemma is significantly shorter.
-/

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

/-- Approximate relational coupling with additive error slack `ε`. -/
abbrev ARcoupl (ε : ENNReal) (S : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling (· + ε) S μₗ μᵣ

/-- Exact relational coupling: the zero-slack case of `ARcoupl`. -/
abbrev Rcoupl (S : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARcoupl 0 S μₗ μᵣ

namespace ARcoupl

/-- Reflexivity of `ARcoupl` at the equality relation. -/
theorem refl {ε : ENNReal} (μ : Measure α) : ARcoupl ε (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ le_self_add

/-- `ARcoupl 0` at the equality relation, i.e. `Rcoupl` refl. -/
theorem refl_zero (μ : Measure α) : Rcoupl (fun v => v.1 = v.2) μ μ :=
  refl μ

/-- Dirac coupling: two point masses are `ARcoupl ε`-related for any `ε` as long as the
relation holds on the points. -/
theorem dirac {ε : ENNReal} {a : α} {b : β} (S : Set (α × β)) (H : S (a, b)) :
    ARcoupl ε S (.dirac a) (.dirac b) :=
  ARCoupling.dirac le_self_add S H

/-- Enlarging the relation weakens the coupling. -/
theorem mono_rel {ε : ENNReal} {S S' : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (HS : S ⊆ S') (H : ARcoupl ε S μₗ μᵣ) : ARcoupl ε S' μₗ μᵣ :=
  ARCoupling.mono_rel HS H

/-- Enlarging the error slack weakens the coupling. -/
theorem mono_ε {ε ε' : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (Hε : ε ≤ ε') (H : ARcoupl ε S μₗ μᵣ) : ARcoupl ε' S μₗ μᵣ :=
  ARCoupling.mono_F (fun x => by gcongr) H

/-- The zero measure is trivially coupled on the left. -/
theorem zero_left {ε : ENNReal} (S : Set (α × β)) (μᵣ : Measure β) :
    ARcoupl ε S (0 : Measure α) μᵣ :=
  ARCoupling.zero_left S μᵣ

/-- Coupling against the zero measure on the right requires `μₗ .univ ≤ ε`. -/
theorem zero_right {ε : ENNReal} (S : Set (α × β)) {μₗ : Measure α}
    (Hε : μₗ .univ ≤ ε) : ARcoupl ε S μₗ (0 : Measure β) :=
  ARCoupling.zero_right S (by simpa using Hε)

/-- Monad bind for `ARcoupl`: the error slacks add.

Given `ARcoupl ε` between `μₗ` and `μᵣ`, and `ARcoupl ε'` between `f a` and `g b` whenever
`S (a, b)`, we get `ARcoupl (ε + ε')` between the bound measures `μₗ.bind f` and `μᵣ.bind g`,
provided `μₗ` and each `f a` are sub-probability measures. -/
theorem bind {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} {f : α → Measure α'} {g : β → Measure β'}
    (Hfm : Measurable f) (Hgm : Measurable g)
    (Hμₗ : μₗ .univ ≤ 1) (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (Hcpl : ARcoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → ARcoupl ε' T (f a) (g b)) :
    ARcoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  /- Subprobability of `f a` gives `∫⁻ f' ∂(f a) ≤ 1`. Nothing similar is assumed on `g`, so
     we truncate the right-hand test function with `⊓ 1` to keep it in `[0,1]`. -/
  have HFle a : ∫⁻ y, f' y ∂(f a) ≤ 1 :=
    (lintegral_le_meas (s := .univ) Hf'b (fun _ => (·.elim trivial))).trans (Hfsprob a)
  /- Build `Fh a := ∫⁻ f' ∂(f a) - ε'` and `Gh b := (∫⁻ g' ∂(g b)) ⊓ 1`. -/
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
    (H : ARcoupl ε S μₗ μᵣ) : μₗ .univ ≤ μᵣ .univ + ε := by
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
    (Heq : ARcoupl ε₁ (fun v => v.1 = v.2) μ₁ μ₂) (HR : ARcoupl ε₂ R μ₂ μ₃) :
    ARcoupl (ε₁ + ε₂) R μ₁ μ₃ := by
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
    (HR : ARcoupl ε₁ R μ₁ μ₂) (Heq : ARcoupl ε₂ (fun v => v.1 = v.2) μ₂ μ₃) :
    ARcoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  have step1 : ∫⁻ x, f.1 x ∂μ₁ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := HR f g Hfg
  have step2 : ∫⁻ x, g.1 x ∂μ₂ ≤ ∫⁻ x, g.1 x ∂μ₃ + ε₂ :=
    Heq g g (fun {a b} (h : a = b) => h ▸ le_refl _)
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := step1
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by gcongr
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

/-!
#### Change of variables

The core measure-theoretic coupling: any measure is exactly coupled to its pushforward
along a measurable map. This is the analogue of Clutch's `ARcoupl_map` and is the key
lemma behind all uniform-measure couplings — a bijection from `Fin N` to itself that
preserves the uniform measure immediately gives `ARcoupl 0` on `(dunifP N, dunifP N)`.
-/

/-- Any measure `μ` is `Rcoupl`-coupled to its pushforward `μ.map h` along the graph of `h`. -/
theorem map {h : α → β} (hm : Measurable h) (μ : Measure α) :
    Rcoupl (fun v => v.2 = h v.1) μ (μ.map h) := by
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
    Rcoupl (fun v => v.2 = h v.1) μ ν := by
  rw [← hp.map_eq]
  exact map hp.measurable μ

/-- Specialization: a measure is exactly self-coupled along any permutation that preserves
it. This is the measure-theoretic analogue of Clutch's `ARcoupl_dunif`: if `h : α → α`
preserves `μ` (e.g. `μ` is uniform on a finite type and `h` is a bijection), then
`Rcoupl (fun (a, a') => a' = h a) μ μ`. -/
theorem self_of_measurePreserving {h : α → α} {μ : Measure α}
    (hp : MeasurePreserving h μ μ) :
    Rcoupl (fun v => v.2 = h v.1) μ μ :=
  map_of_measurePreserving hp

/-- Two probability measures are exactly coupled under the universal relation, provided
every test function `f` is pointwise ≤ every test function `g`. The argument threads
through the sup of `f` and the inf of `g`: `∫⁻ f dμ ≤ ⨆ f ≤ ⨅ g ≤ ∫⁻ g dμ'`. -/
theorem trivial {μₗ : Measure α} {μᵣ : Measure β}
    (Hμₗ : μₗ .univ = 1) (Hμᵣ : μᵣ .univ = 1) :
    Rcoupl Set.univ μₗ μᵣ := by
  intro ⟨f, _, Hfb⟩ ⟨g, _, Hgb⟩ Hfg
  show ∫⁻ a, f a ∂μₗ ≤ ∫⁻ b, g b ∂μᵣ + 0
  rw [add_zero]
  -- ∫⁻ f dμ ≤ ⨆ a, f a
  -- ∫⁻ f dμ ≤ ⨆ a, f a  (since μₗ is a prob measure)
  have hf_le_sup : ∫⁻ a, f a ∂μₗ ≤ ⨆ a, f a :=
    (lintegral_le_iSup_mul f).trans (by rw [Hμₗ, mul_one])
  -- ⨆ a, f a ≤ ⨅ b, g b  (since ∀ a b, f a ≤ g b)
  have hlt : ⨆ a, f a ≤ ⨅ b, g b :=
    iSup_le fun a => le_iInf fun b => Hfg (Set.mem_univ (a, b))
  -- ⨅ b, g b ≤ ∫⁻ g dμ'  (since μᵣ is a prob measure)
  have hg_ge_inf : ⨅ b, g b ≤ ∫⁻ b, g b ∂μᵣ :=
    (by rw [Hμᵣ, mul_one] : (⨅ b, g b) * μᵣ .univ = ⨅ b, g b) ▸ iInf_mul_le_lintegral g
  exact hf_le_sup.trans (hlt.trans hg_ge_inf)

/-- Exact coupling implies approximate coupling for any `ε`: just use `mono_ε`. -/
theorem exact {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : Rcoupl S μₗ μᵣ) : ARcoupl ε S μₗ μᵣ :=
  mono_ε (zero_le ε) H

/-- Limit lemma: if the coupling holds for every `ε' > ε`, it holds at `ε` itself.
Equivalently, `ε` is an infimum of achievable slacks. -/
theorem limit {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ ε', ε < ε' → ARcoupl ε' S μₗ μᵣ) : ARcoupl ε S μₗ μᵣ := by
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

end ARcoupl

end AdditiveCoupling

-- noncomputable section BinaryCoupling
--
-- open BinarySequence
--
-- @[simp] def ARCoupling.binary_eqv : Set (BinarySequence × unitInterval) :=
--   fun ⟨b, r⟩ => b.unexpand = r
--
-- theorem ARCoupling.binary : ARCoupling id binary_eqv uniformIntervalSequences volume := by
--   intro ⟨_, Hfm, _⟩ _ HS; simp only [uniformIntervalSequences, id_eq]
--   rw [lintegral_map Hfm expand_measurable]
--   refine lintegral_mono (fun _ => ?_)
--   apply HS
--   simp
--
-- end BinaryCoupling

noncomputable section DPCoupling

open Measure EReal

abbrev DPF (ε δ x : ENNReal) := exp ε * x + δ

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']
variable (ε δ : ENNReal)

abbrev ARCoupling.DP (S : Set (α × β)) := ARCoupling (DPF ε δ) S

theorem ARCoupling.DP.trivial_δ {μₗ : Measure α} {μᵣ : Measure β} {S} (Hδ : μₗ .univ ≤ δ) :
    ARCoupling.DP ε δ S μₗ μᵣ := by
  refine fun ⟨f, _, Hf⟩ _ _ => ?_
  refine lintegral_le_meas (s := .univ) Hf (fun _ => (·.elim trivial)) |>.trans ?_
  refine Hδ.trans ?_
  exact le_add_self

theorem ARCoupling.DP.dirac {a : α} {b : β} (S : Set (α × β)) :
    S (a, b) → ARCoupling.DP ε δ S (.dirac a) (.dirac b) := by
  refine (ARCoupling.dirac (@fun _ => ?_) _ ·)
  refine .trans ?_ le_self_add
  refine le_mul_of_one_le_left' ?_
  exact EReal.one_le_exp_iff.mpr <| EReal.coe_ennreal_nonneg ε

-- TODO: remove ε ≠ ⊤ case by reduction (needs g ≠ 0?)
theorem ARCoupling.DP.bind {ε'} {δ' : NNReal} {f : α → Measure α'} {g : β → Measure β'} {S T}
   {μₗ μᵣ} (Hfm : Measurable f) (Hgm : Measurable g) (Huniv : μₗ .univ ≤ 1) (Hε : ε ≠ ⊤)
   (Hfsprob : ∀ {a}, (f a) Set.univ ≤ 1)
   (Hcpl : ARCoupling.DP ε δ S μₗ μᵣ)
   (Hbind : ∀ {a b}, S (a, b) → ARCoupling.DP ε' δ' T (f a) (g b)) :
   ARCoupling.DP (ε + ε') (δ + δ') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have Hf'le a : ∫⁻ (y : α'), f' y ∂f a - δ' ≤ 1 := by
    refine tsub_le_iff_left.mpr (.trans ?_ le_add_self)
    refine (lintegral_le_iSup_mul (f := f')).trans ?_
    exact Left.mul_le_one (iSup_le (Hf'b ·)) Hfsprob

  /- Set up the reduction -/
  let F : CouplingFunction α := .mk (max 0 <| ∫⁻ y, f' y ∂ f · - δ') ⟨?Fm, fun a => ?Fb⟩
  case Fm =>
    refine measurable_const.max ?_
    refine .sub ?_ measurable_const
    exact measurable_lintegral Hf'm |>.comp Hfm
  case Fb => exact max_le (zero_le_one' _) (Hf'le _)
  let G : CouplingFunction β := .mk (min 1 <| (exp ε') * ∫⁻ y, g' y ∂ g ·) ⟨?Gm, fun b => ?Gb⟩
  case Gm =>
    refine measurable_const.min ?_
    refine measurable_const.mul ?_
    exact measurable_lintegral Hg'm |>.comp Hgm
  case Gb => exact min_le_left _ _

  /- The main inequality -/
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc  ∫⁻ a, ∫⁻ (x : α'), f' x ∂f a ∂μₗ
    _ ≤ ∫⁻ a, δ' + F a ∂μₗ := ?_
    _ ≤ δ' + ∫⁻ a, F a ∂μₗ := ?_
    _ ≤ δ' + δ + exp ε * ∫⁻ b, G b ∂μᵣ := ?_
    _ ≤ δ' + δ + exp ε * ∫⁻ b, exp ε' * ∫⁻ b', g' b' ∂g b ∂μᵣ := ?_
  · refine lintegral_mono (fun x => ?_)
    simp only [zero_le, sup_of_le_right, F]
    exact le_add_tsub
  · rw [lintegral_add_left measurable_const, lintegral_const]
    refine (ENNReal.add_le_add_iff_right ?_).mpr ?_
    · refine LT.lt.ne (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
      refine (lintegral_le_iSup_mul (f := F)).trans ?_
      refine Left.mul_le_one (iSup_le ?_) Huniv
      exact F.property.2
    exact mul_le_of_le_one_right' Huniv
  · rw [add_assoc]; refine add_le_add (le_refl _) ?_
    rw [add_comm]
    refine Hcpl F G (fun {a b} HS => ?_)
    simp only [F, G]
    refine max_le (zero_le _) (le_min ?_ ?_)
    · exact Hf'le _
    · refine tsub_le_iff_left.mpr ?_
      rw [add_comm]; exact Hbind HS ⟨f', ⟨Hf'm, Hf'b⟩⟩ ⟨g', ⟨Hg'm, Hg'b⟩⟩ Hf'g'
  · dsimp only [G]; refine add_le_add (le_refl _) ?_
    refine (ENNReal.mul_le_mul_iff_right (by simp) (by simp [Hε])).mpr ?_
    refine lintegral_mono (fun b => ?_)
    exact min_le_right _ _
  · simp [DPF, exp_add, add_comm, mul_assoc]
    refine le_of_eq ?_
    congr
    exact lintegral_const_mul (exp ε') (measurable_lintegral Hg'm |>.comp Hgm)

end DPCoupling

end MeasureTheory
