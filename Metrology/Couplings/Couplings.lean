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

-- TODO: Perhaps show that couplings lift when two things are measure_eq
-- Define follow lintergal_map for this proof

end ApproximateCoupling

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
