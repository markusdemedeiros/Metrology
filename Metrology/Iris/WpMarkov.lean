import Iris
import Mathlib.Probability.Kernel.Basic
import Mathlib.Data.ENNReal.Basic
import Iris.Instances.IProp.Instance
import Iris.Algebra.Auth
import Iris.Algebra.Numbers
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Iris.Algebra.HeapView

-- FIXME: (Iris) Expose IProp
-- FIXME: (Iris) Scope Iris.Set

namespace MarkovTest
noncomputable section

open Iris Std COFE ProbabilityTheory MeasureTheory

-- This instance is just used for the Auth construction, we only ever
-- use the One.one of this.
local instance : UFraction ℕ+ where
  Proper := (· ≤ 1)
  add_comm := by grind
  add_assoc := by grind
  add_left_cancel := by simp
  add_ne {a b} H := by
    cases a; cases b
    rename_i va ha vb hb
    have : va = vb + va := by injection H
    omega
  proper_add_mono_left := by
    intro a b hab
    cases a; cases b
    rename_i va ha vb hb
    change va + vb ≤ 1 at hab
    change va ≤ 1
    omega
  one_whole := by
    simp only [Fraction.Whole, _root_.le_refl, Fraction.Fractional,
      PNat.le_one_iff, not_exists, true_and]
    intro b
    have : 1 + b ≠ 1 := by
      cases b; rename_i vb hb
      intro H
      have : 1 + vb = 1 := by injection H
      omega
    exact this

-- Now we make a local CMRA instance for the ENNReals under addition

local instance : COFE ENNReal := COFE.ofDiscrete _ ⟨congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩
local instance : OFE.Discrete ENNReal := { discrete_0 := congrArg id }
local instance : OFE.Leibniz ENNReal := ⟨(·)⟩
local instance : Associative (Add.add (α := ENNReal)) where
  assoc a b c := add_assoc a b c
local instance : Commutative (Add.add (α := ENNReal)) where
  comm a b := add_comm a b
local instance : LawfulLeftIdentity (Add.add (α := ENNReal)) Zero.zero where
  left_id := zero_add

open CommMonoidLike in
noncomputable local instance : CMRA ENNReal := CommMonoidLike.instCMRA

noncomputable local instance : UCMRA ENNReal where
  unit := 0
  unit_valid := trivial
  unit_left_id := CMRA.pcore_op_left rfl
  pcore_unit := rfl

/-

-- CMRA of subprobability distributions with maximum as the operation
instance [MeasurableSpace α] : CMRA (Measure α) where
  pcore μ := .some μ
  op μ₁ μ₂ := max μ₁ μ₂
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne := by simp
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_succ := (·)
  validN_op_left {_ μ₁ μ₂} h := by
    refine .trans ?_ h
    refine .trans (le_sup_left (a := μ₁ .univ) (b := μ₂ .univ)) ?_
    refine ge_of_eq ?_
    -- Evaluating the max of two measures equals evaluation in the max measure
    -- unfold max
    -- simp [SemilatticeSup.toMax, SemilatticeSup.sup]
    -- unfold SemilatticeSup.sup
    -- simp [CompleteLattice.toConditionallyCompleteLattice]
    -- simp [Measure.instCompleteLattice]
    -- simp [completeLatticeOfCompleteSemilatticeInf]
    -- simp [completeLatticeOfInf]
    -- simp [sInf]
    -- unfold DFunLike.coe
    -- unfold OuterMeasure.instFunLikeSetENNReal
    -- dsimp
    sorry
  assoc := by
    refine .of_eq ?_
    symm
    exact sup_assoc _ _ _
  comm := .of_eq (sup_comm ..)
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono {μ₁ μ₂} := by
    rintro ⟨rfl⟩
    exact fun μ => ⟨μ, rfl⟩
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩)

-/

-- Use the trivial OFE on measures
instance measureOFE [MeasurableSpace α] : OFE (Measure α) where
  Equiv x y := x = y
  Dist _ x y := x = y
  dist_eqv := ⟨fun _ => rfl, (Eq.symm ·), (Eq.trans · ·)⟩
  equiv_dist := .symm <| forall_const _
  dist_lt H _ := H

/-
-- CMRA of subprobability distributions with addition
instance [MeasurableSpace α] : CMRA (Measure α) where
  pcore _ := .some 0
  op μ₁ μ₂ := μ₁ + μ₂
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne := by simp
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_succ := (·)
  validN_op_left := (le_of_add_le_of_nonneg_left · <| zero_le _)
  assoc := by simp [add_assoc]
  comm := by simp [add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ Y
    exact ⟨0, .of_eq <| Option.some_inj.mpr (zero_add 0).symm⟩
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩)

instance [MeasurableSpace α] : UCMRA (Measure α) where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by
    intro μ
    refine .of_eq (zero_add _)
  pcore_unit := by simp [CMRA.pcore]
-/



inductive DisjointMeasure (T : Type _) [MeasurableSpace T]
  | err
  | ok (S : _root_.Set T) (H : MeasurableSet S) (μ : Measure T) (Hex : μ Sᶜ = 0)

-- @[simp]
-- def DisjointMeasure.alter [MeasurableSpace T] (μ : Measure T) :
--     DisjointMeasure T → DisjointMeasure T
--   | .err => .err
--   | .ok S H _ => .ok S H μ

-- -- Change the value of the measure on the set S to be μ
-- @[simp]
-- def DisjointMeasure.alterOn [MeasurableSpace T] (S : _root_.Set T) (μ : Measure T) :
--     DisjointMeasure T → DisjointMeasure T
--   | .err => .err
--   | .ok S' H' μ' => .ok S' H' (μ'.restrict Sᶜ + μ.restrict S)

@[simp]
def DisjointMeasure.toMeasure [MeasurableSpace T] : DisjointMeasure T -> Option (Measure T)
  | err => .none
  | ok S _ μ _ => .some <| μ.restrict S

open Classical in
@[simp]
noncomputable def DisjointMeasure.DisjointUnion [MeasurableSpace T] :
    DisjointMeasure T → DisjointMeasure T → DisjointMeasure T
  | .err, _ => .err
  | _, .err => .err
  | .ok S₁ H₁ μ₁ Hc₁, .ok S₂ H₂ μ₂ Hc₂ =>
    if H' : _root_.Disjoint S₁ S₂ then
      .ok (S₁ ∪ S₂) (.union H₁ H₂) (μ₁ + μ₂) (by
        simp only [Measure.coe_add, Pi.add_apply, add_eq_zero]
        constructor
        · -- Show: μ₁ (S₁ ∪ S₂)ᶜ = 0
          -- Since (S₁ ∪ S₂)ᶜ ⊆ S₁ᶜ and μ₁ S₁ᶜ = 0
          refine Measure.mono_null ?_ Hc₁
          exact Set.compl_subset_compl.mpr Set.subset_union_left
        · -- Show: μ₂ (S₁ ∪ S₂)ᶜ = 0
          -- Since (S₁ ∪ S₂)ᶜ ⊆ S₂ᶜ and μ₂ S₂ᶜ = 0
          refine Measure.mono_null ?_ Hc₂
          exact Set.compl_subset_compl.mpr Set.subset_union_right
        )
      else .err

@[simp]
noncomputable def DisjointMeasure.Valid [MeasurableSpace T] (M : DisjointMeasure T) : Prop :=
  match M.toMeasure with
  | .none => False
  | .some μ => μ .univ ≤ 1

instance [MeasurableSpace α] : OFE (DisjointMeasure α) where
  Equiv x y := x = y
  Dist _ x y := x = y
  dist_eqv := ⟨fun _ => rfl, (Eq.symm ·), (Eq.trans · ·)⟩
  equiv_dist := .symm <| forall_const _
  dist_lt H _ := H

-- FIXME: Cleanup
set_option linter.style.setOption false
set_option linter.flexible false
instance [MeasurableSpace α] : CMRA (DisjointMeasure α) where
  pcore _ := .some <| .ok ∅ .empty 0 rfl
  op μ₁ μ₂ := μ₁.DisjointUnion μ₂
  Valid μ := μ.Valid
  ValidN _ μ := μ.Valid
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne {n x y z} := by
    rintro ⟨rfl⟩
    rintro ⟨rfl⟩
    exists (DisjointMeasure.ok ∅ .empty 0 rfl)
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_succ := (·)
  validN_op_left {n x y} := by
    rcases x <;> cases y
    · simp
    · simp
    · simp
    rename_i S₁ H₁ μ₁ Hc₁ S₂ H₂ μ₂ Hc₂
    simp only [DisjointMeasure.Valid, DisjointMeasure.toMeasure, DisjointMeasure.DisjointUnion,
      MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
    by_cases H : _root_.Disjoint S₁ S₂
    · rw [dif_pos H]
      simp only [Measure.restrict_add, Measure.coe_add, Pi.add_apply,
        MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
      rw [measure_union' H H₁, measure_union' H H₁, add_assoc]
      refine .trans le_self_add
    · simp [H]
  assoc {x y z} := by
    rcases x <;> cases y <;> cases z
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp; split <;> simp_all
    · simp only [DisjointMeasure.DisjointUnion]
      rename_i S₁ H₁ μ₁ Hc₁ S₂ H₂ μ₂ Hc₂ S₃ H₃ μ₃ Hc₃
      by_cases HD1 : _root_.Disjoint S₂ S₃ <;>
      by_cases HD2 : _root_.Disjoint S₁ S₂ <;>
      simp [HD1, HD2]
      congr 1
      · grind
      · congr 1
        · exact (Set.union_assoc ..).symm
        · exact (add_assoc ..).symm
  comm {x y} := by
    rcases x <;> cases y
    · simp
    · simp
    · simp
    · simp
      rename_i S₁ H₁ μ₁ Hc₁ S₂ H₂ μ₂ Hc₂
      congr 1
      · exact Eq.propIntro (fun a ↦ id (Disjoint.symm a)) fun a ↦ id (Disjoint.symm a)
      congr 1
      · exact Set.union_comm S₁ S₂
      · exact AddCommMagma.add_comm μ₁ μ₂
  pcore_op_left {x y} := by
    cases x
    · simp
      rintro ⟨rfl⟩
      simp
    · rintro ⟨rfl⟩
      simp
  pcore_idem {x y} := by
    cases x
    · simp
      rintro ⟨rfl⟩
      simp
    · simp
      rintro ⟨rfl⟩
      simp
  pcore_op_mono {x y} := by
    rintro ⟨rfl⟩
    intro y
    exists (DisjointMeasure.ok ∅ .empty 0 rfl)
    simp
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩)

instance [MeasurableSpace α] : UCMRA (DisjointMeasure α) where
  unit := .ok ∅ .empty 0 rfl
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by intro μ; cases μ <;> simp [CMRA.op]
  pcore_unit := by simp [CMRA.pcore]


-- Measure restrictions => View CMRA
-- The relation only holds when μA has bounded mass on S (≤ 1)
def MeasureViewRel (T : Type _) [MeasurableSpace T] : ViewRel (Measure T) (DisjointMeasure T) :=
  fun _ μA f => match f with
  | .err => False
  | .ok S _ μF _ => μF = μA.restrict S ∧ μA S ≤ 1

/- μ₁ ⟂ₘ μ₃ -/
theorem DisjointMeasure.inc_ok_iff [MeasurableSpace T] {S₁ S₂ : _root_.Set T}
    {H₁ : MeasurableSet S₁} {H₂ : MeasurableSet S₂} {μ₁ μ₂ : Measure T}
    (Hex₁ : μ₁ S₁ᶜ = 0) (Hex₂ : μ₂ S₂ᶜ = 0) :
    ok S₁ H₁ μ₁ Hex₁ ≼ ok S₂ H₂ μ₂ Hex₂ ↔
    ∃ (S₃ : _root_.Set T), ∃ μ₃, MeasurableSet S₃ ∧
      _root_.Disjoint S₁ S₃ ∧ S₁ ∪ S₃ = S₂ ∧ μ₃ S₁ = 0 ∧ μ₂ = μ₁ + μ₃ := by
  constructor
  · rintro ⟨μ₃, H⟩
    cases μ₃ <;> simp [CMRA.op] at H
    · simp [OFE.Equiv] at H
    rename_i S₃ H₃ μ₃ Hc₃
    by_cases H' : _root_.Disjoint S₁ S₃ <;> simp only [H', ↓reduceIte] at H
    · rcases H
      exists S₃, μ₃
      refine ⟨H₃, H', rfl, ?_, rfl⟩
      refine Measure.mono_null ?_ Hc₃
      exact Disjoint.subset_compl_left H'.symm
    · rcases H
  · rintro ⟨S₃, μ₃, H₃, HS₁S₃, HU, Hsing, Hsum⟩
    have Hzero' : μ₃ S₃ᶜ = 0 := by
      subst HU Hsum
      simp only [Measure.coe_add, Pi.add_apply, add_eq_zero] at Hex₂
      rcases Hex₂ with ⟨H1, H2⟩
      have : S₃ᶜ = S₁ ∪ (S₁ ∪ S₃)ᶜ := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_union]
        constructor
        · intro h
          by_cases hx : x ∈ S₁
          · left; exact hx
          · right
            intro h'
            rcases h' with h1 | h3
            · contradiction
            · contradiction
        · intro h hS₃
          rcases h with hS₁ | hcomp
          · exact HS₁S₃.ne_of_mem hS₁ hS₃ rfl
          · exact hcomp (Or.inr hS₃)
      rw [this]
      have H : μ₃ (S₁ ∪ (S₁ ∪ S₃)ᶜ) ≤ μ₃ S₁ + μ₃ ((S₁ ∪ S₃)ᶜ) := measure_union_le _ _
      rw [Hsing, H2] at H
      simp only [add_zero] at H
      exact _root_.le_antisymm H (zero_le _)
    exists (.ok S₃ H₃ (μ₃) Hzero')
    simp [CMRA.op]
    simp only [HS₁S₃, ↓reduceIte]
    congr
    exact HU.symm

theorem DisjointMeasure.inc_iff_incN [MeasurableSpace T] {S₁ S₂ : _root_.Set T}
    {H₁ : MeasurableSet S₁} {H₂ : MeasurableSet S₂} {μ₁ μ₂ : Measure T}
    {Hex₁ : μ₁ S₁ᶜ = 0} {Hex₂ : μ₂ S₂ᶜ = 0} :
    (ok S₁ H₁ μ₁ Hex₁ ≼ ok S₂ H₂ μ₂ Hex₂) ↔ (ok S₁ H₁ μ₁ Hex₁ ≼{n} ok S₂ H₂ μ₂ Hex₂) := by
  rfl

instance [MeasurableSpace T] : IsViewRel (MeasureViewRel T) where
  mono {n₁ μA₁ μF₁ n₂ μA₂ μF₂} := by
    intro Hrel Ha_eq Hb_incl Hn
    cases μF₁ with
    | err => simp [MeasureViewRel] at Hrel
    | ok S₁ HS₁ μF₁ Hex₁ =>
      cases μF₂ with
      | err =>
        simp [MeasureViewRel] at Hrel
        simp [CMRA.IncludedN, CMRA.op] at Hb_incl
        rcases Hb_incl with ⟨_, H⟩
        rcases H
      | ok S₂ HS₂ μF₂ Hex₂ =>
        have HH := (DisjointMeasure.inc_ok_iff ..).mp <| DisjointMeasure.inc_iff_incN.mpr Hb_incl
        clear Hb_incl
        simp [MeasureViewRel]
        subst Ha_eq
        simp [MeasureViewRel] at Hrel
        rcases Hrel with ⟨H1, H2⟩
        rcases HH with ⟨S₃, μF₃, HS₃, HD, HU, Hc, Hsum⟩
        subst HU
        subst H1
        simp [Hsum] at Hex₁
        rcases Hex₁ with ⟨H3, H4⟩
        refine ⟨?_, measure_le_measure_union_left.trans H2⟩
        -- Goal: μF₂ = μA₁.restrict S₂
        -- We have: Hsum : μA₁.restrict (S₂ ∪ S₃) = μF₂ + μF₃
        -- HD : Disjoint S₂ S₃, Hc : μF₃ S₂ = 0
        -- Strategy: Show both measures agree on all measurable sets
        ext A HA
        -- For any measurable set A, show: μF₂ A = (μA₁.restrict S₂) A
        have key := congr_fun (congr_arg DFunLike.coe Hsum) A
        simp [Measure.restrict_apply HA, Measure.add_apply] at key ⊢
        -- key : μA₁ (A ∩ (S₂ ∪ S₃)) = μF₂ A + μF₃ A
        -- Use set distributivity: A ∩ (S₂ ∪ S₃) = (A ∩ S₂) ∪ (A ∩ S₃)
        rw [Set.inter_union_distrib_left] at key
        -- Now key : μA₁ ((A ∩ S₂) ∪ (A ∩ S₃)) = μF₂ A + μF₃ A
        -- Since S₂ and S₃ are disjoint, so are A ∩ S₂ and A ∩ S₃
        have disj_inter : _root_.Disjoint (A ∩ S₂) (A ∩ S₃) := by
          rw [Set.disjoint_iff_inter_eq_empty]
          ext x
          simp [Set.mem_inter_iff]
          intro _ hS₂ _ hS₃
          exact HD.ne_of_mem hS₂ hS₃ rfl
        -- Decompose the measure on the union
        rw [measure_union disj_inter (HA.inter HS₃)] at key
        -- Now: μA₁ (A ∩ S₂) + μA₁ (A ∩ S₃) = μF₂ A + μF₃ A
        -- Since μF₂ is supported on S₂ (from Hex₂), we have μF₂ A = μF₂ (A ∩ S₂)
        have hF₂_support : μF₂ A = μF₂ (A ∩ S₂) := by
          conv_lhs => rw [← Set.inter_union_compl A S₂]
          rw [measure_union]
          · have : A ∩ S₂ᶜ ⊆ S₂ᶜ := Set.inter_subset_right
            simp [Measure.mono_null this Hex₂]
          · rw [Set.disjoint_iff_inter_eq_empty]
            ext x
            simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false,
              iff_false, not_and]
            intro _; tauto
          · exact HA.inter HS₂.compl
        -- Similarly, μF₃ A = μF₃ (A ∩ S₃) since μF₃ is supported on S₃
        have hF₃_support : μF₃ A = μF₃ (A ∩ S₃) := by
          -- μF₃ is zero on S₂ (from Hc) and zero outside S₂ ∪ S₃ (from H4)
          -- So μF₃ is supported on S₃
          conv_lhs => rw [← Set.inter_union_compl A S₃]
          rw [measure_union]
          · -- Need to show μF₃ (A ∩ S₃ᶜ) = 0
            -- We have: A ∩ S₃ᶜ = (A ∩ S₂) ∪ (A ∩ (S₂ᶜ ∩ S₃ᶜ))
            have decomp : A ∩ S₃ᶜ = (A ∩ S₂) ∪ (A ∩ (S₂ᶜ ∩ S₃ᶜ)) := by
              ext x
              simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union]
              constructor
              · intro ⟨hA, hS₃⟩
                by_cases h : x ∈ S₂
                · left; exact ⟨hA, h⟩
                · right; exact ⟨hA, h, hS₃⟩
              · intro h
                cases h with
                | inl h => exact ⟨h.1, fun hS₃ => HD.ne_of_mem h.2 hS₃ rfl⟩
                | inr h => exact ⟨h.1, h.2.2⟩
            rw [decomp, measure_union']
            · simp [Measure.mono_null (Set.inter_subset_right) Hc,
                     Measure.mono_null (Set.inter_subset_right) H4]
            · rw [Set.disjoint_iff_inter_eq_empty]; ext x; simp; tauto
            · exact HA.inter HS₂
          · rw [Set.disjoint_iff_inter_eq_empty]; ext x; simp; tauto
          · exact HA.inter HS₃.compl
        -- Now combine everything
        rw [hF₂_support, hF₃_support] at key
        -- key : μA₁ (A ∩ S₂) + μA₁ (A ∩ S₃) = μF₂ (A ∩ S₂) + μF₃ (A ∩ S₃)
        -- We need to extract: μF₂ (A ∩ S₂) = μA₁ (A ∩ S₂)
        -- Use Hsum directly on A ∩ S₂
        have key2 := congr_fun (congr_arg DFunLike.coe Hsum) (A ∩ S₂)
        simp [Measure.restrict_apply (HA.inter HS₂), Measure.add_apply] at key2
        -- key2 : μA₁ ((A ∩ S₂) ∩ (S₂ ∪ S₃)) = μF₂ (A ∩ S₂) + μF₃ (A ∩ S₂)
        have simp1 : (A ∩ S₂) ∩ (S₂ ∪ S₃) = A ∩ S₂ := by
          ext x; simp; tauto
        rw [simp1] at key2
        -- key2 : μA₁ (A ∩ S₂) = μF₂ (A ∩ S₂) + μF₃ (A ∩ S₂)
        have μF₃_zero : μF₃ (A ∩ S₂) = 0 := Measure.mono_null (Set.inter_subset_right) Hc
        rw [μF₃_zero, add_zero] at key2
        -- Now: key2 : μA₁ (A ∩ S₂) = μF₂ (A ∩ S₂)
        -- And: hF₂_support : μF₂ A = μF₂ (A ∩ S₂)
        rw [hF₂_support, key2]
  rel_validN := by
    intro n μA μF Hrel
    cases μF with
    | err => simp [MeasureViewRel] at Hrel
    | ok S HS μF Hex =>
      simp [MeasureViewRel] at Hrel
      rcases Hrel with ⟨Hrel_eq, Hrel_valid⟩
      simp [CMRA.ValidN, DisjointMeasure.Valid, DisjointMeasure.toMeasure]
      subst Hrel_eq
      calc (μA.restrict S) S
        _ = μA S := by simp [Measure.restrict_apply HS]
        _ ≤ 1 := Hrel_valid
  rel_unit := by
    intro n
    exists 0
    simp [MeasureViewRel]

-- variable [MeasurableSpace T]
-- #synth CMRA (View ℕ+ (MeasureViewRel T) )

class WpMarkov (GF : BundledGFunctors) (T : Type _) [MeasurableSpace T] where
  ec : ElemG GF (constOF (Auth ℕ+ ENNReal))
  ec_γ : GName
  state : ElemG GF (constOF (View ℕ+ (MeasureViewRel T)))
  state_γ : GName

export WpMarkov (ec_γ state_γ)
attribute [reducible, instance] WpMarkov.ec
attribute [reducible, instance] WpMarkov.state

section logic

variable {GF : BundledGFunctors} {T : Type _} [MeasurableSpace T] [WpMarkov GF T]

def ec (r : ENNReal) := @iOwn GF _ _ (WpMarkov.ec T) (WpMarkov.ec_γ GF T) (◯ r)
def ec_auth (v : ENNReal) := @iOwn GF _ _ (WpMarkov.ec T) (WpMarkov.ec_γ GF T) (● v)
notation "↯" r:50 => ec r

def bound (μ : DisjointMeasure T) := @iOwn GF _ _ WpMarkov.state (WpMarkov.state_γ GF T) (◯V μ)
def bound_auth (μ : Measure T) := @iOwn GF _ _ WpMarkov.state (WpMarkov.state_γ GF T) (●V μ)


-- Can apply updates
example (μ : Measure T) : bound_auth μ ⊢@{IProp GF} |==> bound_auth μ := by
  apply iOwn_update
  exact View.auth_one_update fun n bf a ↦ a

-- Example update
example {μA μA' : Measure T} {μF μF' : DisjointMeasure T} :
    bound_auth μA ∗ bound μF ⊢@{IProp GF} |==> (bound_auth μA' ∗ bound μF') := by
  refine iOwn_op.mpr.trans (.trans ?_ (BIUpdate.mono iOwn_op.mp))
  apply iOwn_update
  apply View.auth_one_op_frag_update
  intros n bf
  cases bf
  · simp [MeasureViewRel, CMRA.op]
    cases μF <;> simp
  rename_i Sb HSb μb Hcb
  cases μF
  · simp [MeasureViewRel, CMRA.op]
  rename_i Sf Hf μF Hcf
  intros H
  simp [MeasureViewRel, CMRA.op] at H
  by_cases Hdisj : _root_.Disjoint Sf Sb <;> simp [Hdisj] at H
  rcases H with ⟨Hsum, Hmass⟩
  sorry
  -- refine Auth.auth_update ?_

-- Local update:
-- example (μA : DisjointMeasure T) S HS (μF μF' : Measure T) :
--     (μA, .ok S HS μF) ~l~> (.alterOn S μF' μA, .ok S HS μF') := by
--   simp only [LocalUpdate]
--   intros n mz Hv He
--   cases μA <;> simp [CMRA.ValidN] at Hv
--   rename_i SA HSA μA
--   refine ⟨?_, ?_⟩
--   · simp [CMRA.ValidN]
--     rw [Measure.restrict_apply HSA, Measure.restrict_apply HSA]
--     -- Mass inequality
--     sorry
--   · simp
--     cases mz <;> simp_all [CMRA.op?]
--     · cases He
--       congr
--       -- Do I want equivalence to just be on the set?
--       sorry
--     · sorry

-- Idea: Can I formalize that argument from SampCert? Like, the lower bound on one
-- part stops chaging, so it suffices to show the postcondition holds there?

-- Idea: Heap (or View) of a measure as indexed by sets
-- The sets need to be measurable, but maybe we can Hilbert's epsilon that.
-- Is the trivial map (always .none) a map? I think not. So Hilbert's epsilon might not help.
-- Idea: Use the subtype of measurable sets as keys.


section wp

variable (κ : Kernel T T)

-- Probably stupid

def step (μ : Measure T) : Measure T := μ.bind κ

def is_value (μ : Measure T) : Prop := step κ μ = μ

/-- TV distance between μ₁ and μ₂ -/
def tv (μ₁ μ₂ : Measure T) : ENNReal :=
  iSup (fun S : _root_.Set T =>  EReal.abs <| (μ₁ S : EReal) - (μ₂ S : EReal))

def state_interp (μ : Measure T) : IProp GF := iprop(∃ μD, bound μD ∗ ⌜ μD.toMeasure = some μ ⌝)

-- In this WP the values also need access to the state_interp.
-- Since our value cases will look something like:
--   On the domain S, the measure μ is a fixpoint, and Φ holds on μ.
def wp_F (μ : Measure T) (Φ : Measure T → IProp GF)
  (wp : Measure T → (Measure T → IProp GF) → IProp GF) : IProp GF := iprop(
  (⌜is_value κ μ⌝ ∗ |==> Φ μ) ∨
  (∀ ε, ec_auth (T := T) ε -∗
    ∃ μ' ε', ⌜tv (step κ μ) μ' ≤ ε⌝ ∗ ▷ |==> (ec_auth (T := T) ε' ∗ wp μ' Φ)))

open Iris.OFE BI in
instance wp_F_contractive : Contractive (fun wp μ Φ => wp_F (GF := GF) κ μ Φ wp) where
  distLater_dist {n x y HL} μ Φ := by
    refine or_ne.ne .rfl ?_
    refine forall_ne (fun _ => ?_)
    refine wand_ne.ne (.of_eq rfl) ?_
    refine exists_ne (fun v => ?_)
    refine exists_ne (fun _ => ?_)
    refine sep_ne.ne (.of_eq rfl) ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine BIUpdate.bupd_ne.ne ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    exact DistLater.dist_lt (HL · · v Φ) Hm

def wp (μ : Measure T) (Φ : Measure T → IProp GF) : IProp GF :=
  (fixpoint <| (fun wp μ Φ => @wp_F GF T _ _ κ μ Φ wp)) μ Φ

theorem wp_unfold (Φ : Measure T → IProp GF) :
    wp κ μ Φ ≡ iprop(
    (⌜is_value κ μ⌝ ∗ |==> Φ μ) ∨
    (∀ ε, ec_auth (T := T) ε -∗
      ∃ μ' ε', ⌜tv (step κ μ) μ' ≤ ε⌝ ∗ ▷ |==> (ec_auth (T := T) ε' ∗ wp κ μ' Φ))) := by
  apply fixpoint_unfold (f := ⟨(fun wp μ Φ => wp_F (GF := GF) κ μ Φ wp),
    OFE.ne_of_contractive fun wp μ Φ ↦ wp_F κ μ Φ wp⟩)

theorem wp_val (μ : Measure T) (Φ : Measure T → IProp GF) :
    ⌜is_value κ μ ⌝ ∗ Φ μ ⊢ wp κ μ Φ := by
  iintro ⟨%H, HΦ⟩
  iapply wp_unfold
  ileft
  isplitr
  · ipure_intro; trivial
  · iexact HΦ

-- This is the rule I want to support, in some form or another.
-- It suffices to split the
theorem wp_split (μ₁ μ₂ μ₃ : Measure T) (Φ : Measure T → IProp GF) :
    wp κ μ₁ Φ ∗ wp κ μ₂ Φ ⊢ wp κ μ₃ Φ := by
  sorry

-- Idea: Auth over the state of the measure
-- Problem: Split the state into two parts. Both are cyclic, but together they are fixed.
-- This should be impossible.
-- Adequacy: Lower bound on the fixed point?
-- Question: Is the measure CMRA a Heap?
-- Question: Is the DisjointSets CMRA a View

end wp
end logic
end

end MarkovTest
