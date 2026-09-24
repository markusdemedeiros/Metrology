module

public import Metrology.ProbLang.Syntax.Syntax
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Function.Floor

/-! # The continuous `LawfulProbLangℝ ℝ` instance -/
namespace ProbLang

open MeasureTheory


/-- ProbLang's real parameter instantiated with `ℝ`, the continuous semantics.
The measurable structure is the Borel σ-algebra; `unifUnit` is `Uniform[0,1]`. -/
public noncomputable instance instProbLangℝReal : LawfulProbLangℝ ℝ where
  -- `BEq`/`LawfulBEq` via classical decidable equality on `ℝ`.
  beq a b := decide (a = b)
  eq_of_beq h := of_decide_eq_true h
  rfl := by exact decide_eq_true (Eq.refl _)
  -- `MeasurableEq ℝ`: the diagonal of `ℝ × ℝ` is closed (ℝ is `T2`), hence measurable.
  measurableSet_diagonal := isClosed_diagonal.measurableSet
  instDecidableEq := inferInstance
  -- The unit-interval sampling measure: `Uniform[0,1] = volume ∣ [0,1]`.
  unifUnit := volume.restrict (Set.Icc (0 : ℝ) 1)
  unifUnit_isProbabilityMeasure := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  -- Concentration set: the *open* interval `(0,1)`. `unifUnitSupport` need only be a
  -- measurable set on whose complement the measure vanishes; the two endpoints carry no
  -- `volume`, so `(0,1)` qualifies and gives callers the strict range `0 < r < 1`.
  unifUnitSupport := Set.Ioo (0 : ℝ) 1
  unifUnitSupportMeasurable := measurableSet_Ioo
  -- `Uniform[0,1]` puts no mass outside `(0,1)`: restricting to `[0,1]` measures
  -- `· ∩ [0,1]`, and `(0,1)ᶜ ∩ [0,1] ⊆ {0, 1}`, a null (countable) set.
  unifUnitIsConcentrated := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    refine measure_mono_null (t := ({0, 1} : Set ℝ)) ?_ ?_
    · rintro x ⟨hx, h0, h1⟩
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases eq_or_lt_of_le h0 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm h1 (hx h))
    · exact ((Set.finite_singleton (1 : ℝ)).insert 0).countable.measure_zero volume
  -- Real comparison is classical decidable `<`/`≤`; measurable since `{p | p.1 < p.2}`
  -- and `{p | p.1 ≤ p.2}` are Borel-measurable in `ℝ × ℝ`.
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  measurable_realLt := by
    apply measurable_to_bool
    have h : (Function.uncurry (fun a b : ℝ => decide (a < b)) ⁻¹' {true})
        = {p : ℝ × ℝ | p.1 < p.2} := by
      ext p; simp [Function.uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_lt measurable_fst measurable_snd
  measurable_realLe := by
    apply measurable_to_bool
    have h : (Function.uncurry (fun a b : ℝ => decide (a ≤ b)) ⁻¹' {true})
        = {p : ℝ × ℝ | p.1 ≤ p.2} := by
      ext p; simp [Function.uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_le measurable_fst measurable_snd
  -- Arithmetic is Lean's own on `ℝ`; both operations are Borel-measurable.
  realAdd a b := a + b
  realNeg a := -a
  realOfInt z := (z : ℝ)
  realFrac r := Int.fract r
  measurable_realAdd := measurable_add
  measurable_realNeg := measurable_neg
  measurable_realFrac := measurable_fract

/-! ### Arithmetic reduction lemmas

`BinOp.eval`/`UnOp.eval` produce `ProbLangℝ.realAdd`/`realNeg`/`realOfInt`
applications. At `rT = ℝ` these are Lean's own operations; these `simp` lemmas
let `twp_pures` and the stepping display normalise them away. -/

@[simp] public theorem realAdd_real (a b : ℝ) : ProbLangℝ.realAdd a b = a + b := rfl

@[simp] public theorem realNeg_real (a : ℝ) : ProbLangℝ.realNeg a = -a := rfl

@[simp] public theorem realOfInt_real (z : ℤ) : ProbLangℝ.realOfInt z = (z : ℝ) := rfl

@[simp] public theorem realFrac_real (r : ℝ) : ProbLangℝ.realFrac r = Int.fract r := rfl

/-- For the `ℝ` instance, `unifUnitSupport` is the open interval `(0,1)`, so membership
unpacks to the strict range `0 < r < 1`. Used by `urand` samplers to read off sample
bounds from the strengthened `twp_urand_exp'` continuation. -/
public theorem mem_unifUnitSupport_real {r : ℝ} :
    r ∈ LawfulProbLangℝ.unifUnitSupport ↔ 0 < r ∧ r < 1 := Set.mem_Ioo

/-! ### Rotation invariance of `Uniform[0,1]`

The one-time-pad combiner. `x ↦ frac (m + x)` is the rotation of the unit
interval by `m`; it is a piecewise translation swapping the blocks `[0, 1-m)`
and `[1-m, 1)`, so it preserves `Uniform[0,1]`. This is exactly the hypothesis
`wp_couple_urand_urand` / `refines_couple_urands_lr` ask for, and it is what
makes a *continuous* one-time pad provable. -/

open MeasureTheory Set in
/-- Auxiliary: rotation invariance for a shift already normalised to `[0,1)`. -/
theorem measurePreserving_fracAdd_aux {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    MeasureTheory.MeasurePreserving
      (fun r : ℝ => ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))
      (LawfulProbLangℝ.unifUnit) (LawfulProbLangℝ.unifUnit) := by
  show MeasurePreserving (fun r : ℝ => Int.fract (m + r))
      (volume.restrict (Icc (0:ℝ) 1)) (volume.restrict (Icc (0:ℝ) 1))
  have hmeas : Measurable (fun r : ℝ => Int.fract (m + r)) :=
    measurable_fract.comp (measurable_const_add m)
  refine ⟨hmeas, ?_⟩
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hmeas hS, Measure.restrict_apply (hmeas hS),
      Measure.restrict_apply hS]
  -- `Icc 0 1` and `Ico 0 1` differ by the null set `{1}`.
  have hIcc : ∀ A : Set ℝ, volume (A ∩ Icc (0:ℝ) 1) = volume (A ∩ Ico (0:ℝ) 1) := by
    intro A
    have hsplit : A ∩ Icc (0:ℝ) 1 = (A ∩ Ico (0:ℝ) 1) ∪ (A ∩ {(1:ℝ)}) := by
      rw [← Set.inter_union_distrib_left, Set.Ico_union_right (by norm_num : (0:ℝ) ≤ 1)]
    have hnull : volume (A ∩ {(1:ℝ)}) = 0 :=
      measure_mono_null Set.inter_subset_right
        (measure_singleton 1)
    rw [hsplit]
    refine le_antisymm ?_ (measure_mono Set.subset_union_left)
    exact (measure_union_le _ _).trans (by rw [hnull, add_zero])
  rw [hIcc, hIcc]
  -- The two blocks of the domain, and the two blocks of the codomain.
  have hlo : (0:ℝ) ≤ 1 - m := by linarith
  have hhi : (1:ℝ) - m ≤ 1 := by linarith
  -- (A) On `[0, 1-m)` the map is the translation `r ↦ m + r`, onto `[m, 1)`.
  have hA : (fun r : ℝ => Int.fract (m + r)) ⁻¹' S ∩ Ico (0:ℝ) (1 - m)
      = (fun r : ℝ => m + r) ⁻¹' (S ∩ Ico m 1) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    constructor
    · rintro ⟨hSr, hr0, hr1⟩
      have hfr : Int.fract (m + r) = m + r :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hfr] at hSr
      exact ⟨hSr, by linarith, by linarith⟩
    · rintro ⟨hSr, hge, hlt⟩
      have hfr : Int.fract (m + r) = m + r :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact ⟨by rw [hfr]; exact hSr, by linarith, by linarith⟩
  -- (B) On `[1-m, 1)` the map is `r ↦ (m-1) + r`, onto `[0, m)`.
  have hB : (fun r : ℝ => Int.fract (m + r)) ⁻¹' S ∩ Ico (1 - m) (1:ℝ)
      = (fun r : ℝ => (m - 1) + r) ⁻¹' (S ∩ Ico (0:ℝ) m) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    have hshift : Int.fract (m + r) = Int.fract (m + r - 1) := (Int.fract_sub_one (m + r)).symm
    constructor
    · rintro ⟨hSr, hr0, hr1⟩
      have hfr : Int.fract (m + r - 1) = m + r - 1 :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hshift, hfr] at hSr
      refine ⟨by convert hSr using 1; ring, by linarith, by linarith⟩
    · rintro ⟨hSr, hge, hlt⟩
      have hfr : Int.fract (m + r - 1) = m + r - 1 :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [hshift, hfr]
      convert hSr using 1; ring
  -- Assemble: both sides split into the same two blocks, swapped.
  have hunion1 : Ico (0:ℝ) (1 - m) ∪ Ico (1 - m) (1:ℝ) = Ico (0:ℝ) 1 :=
    Set.Ico_union_Ico_eq_Ico hlo hhi
  have hunion2 : Ico (0:ℝ) m ∪ Ico m (1:ℝ) = Ico (0:ℝ) 1 :=
    Set.Ico_union_Ico_eq_Ico hm0 (le_of_lt hm1)
  have hL : volume ((fun r : ℝ => Int.fract (m + r)) ⁻¹' S ∩ Ico (0:ℝ) 1)
      = volume ((fun r : ℝ => Int.fract (m + r)) ⁻¹' S ∩ Ico (0:ℝ) (1 - m))
        + volume ((fun r : ℝ => Int.fract (m + r)) ⁻¹' S ∩ Ico (1 - m) (1:ℝ)) := by
    rw [← hunion1, Set.inter_union_distrib_left]
    exact measure_union
      ((Set.Ico_disjoint_Ico_same).mono
        Set.inter_subset_right Set.inter_subset_right)
      ((hmeas hS).inter measurableSet_Ico)
  have hR : volume (S ∩ Ico (0:ℝ) 1)
      = volume (S ∩ Ico (0:ℝ) m) + volume (S ∩ Ico m (1:ℝ)) := by
    rw [← hunion2, Set.inter_union_distrib_left]
    exact measure_union
      ((Set.Ico_disjoint_Ico_same).mono
        Set.inter_subset_right Set.inter_subset_right)
      (hS.inter measurableSet_Ico)
  rw [hL, hR, hA, hB, measure_preimage_add, measure_preimage_add]
  exact add_comm _ _

/-- **Rotation invariance of `Uniform[0,1]`**, for an arbitrary shift.

`frac` is `1`-periodic in the shift, so the general case reduces to
`measurePreserving_fracAdd_aux` at `Int.fract m ∈ [0,1)`. This is the hypothesis
`refines_couple_urands_lr` wants, with no side condition on `m`. -/
public theorem measurePreserving_fracAdd (m : ℝ) :
    MeasureTheory.MeasurePreserving
      (fun r : ℝ => ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))
      (LawfulProbLangℝ.unifUnit) (LawfulProbLangℝ.unifUnit) := by
  have hper : (fun r : ℝ => Int.fract (m + r))
      = fun r : ℝ => Int.fract (Int.fract m + r) := by
    funext r
    have hshift : Int.fract m + r = (m + r) - (⌊m⌋ : ℝ) := by
      have := Int.fract_add_floor m
      linarith
    rw [hshift, Int.fract_sub_intCast]
  show MeasureTheory.MeasurePreserving (fun r : ℝ => Int.fract (m + r)) _ _
  rw [hper]
  exact measurePreserving_fracAdd_aux (Int.fract_nonneg m) (Int.fract_lt_one m)

/-- `fract` absorbs a `fract` on the right of a sum. -/
public theorem fract_add_fract_right (x y : ℝ) :
    Int.fract (x + Int.fract y) = Int.fract (x + y) := by
  have h : x + Int.fract y = (x + y) - (⌊y⌋ : ℝ) := by
    have := Int.fract_add_floor y; linarith
  rw [h, Int.fract_sub_intCast]

end ProbLang