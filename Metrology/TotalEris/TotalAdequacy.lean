module

public import Metrology.TotalEris.ErrorRules
public import Metrology.TotalEris.FupdPlainlyForall
public import Metrology.ProbLang.Erasure

@[expose] public section

/-!
# Total adequacy

Port of `clutch/theories/eris/total_adequacy.v`. The three user-facing
soundness theorems for total-correctness Eris:

* `twp_tgl` — a `tglWp` triple with error `↯ε` and pure post `φ` gives
  the graded-probability statement `Tgl (limExec (e, σ)) φ ε`.
* `twp_mass_lim_exec` — total mass `≥ 1 - ε`: the program terminates
  with probability at least `1 - ε`.
* `twp_pgl_lim` — Pgl bound for the limiting execution.

**Status: complete (modulo `[AppPreGS] [ECPreGS] [InvGpreS]` preconditions).**
All five user-facing theorems proved without any `sorry`:
* `Tgl` theory: `termination_ineq`, `implies_pgl`, plus a full helper
  library (`mono_grading`, `mono_pred`, `of_ge_one`, `ext`,
  `epsilon_limit`, `of_dirac_val`, `of_limExec_val`,
  `tgl_prim_step`, `dbind_prim_step`).
* `twp_step_fupd_tgl` — iris-side adequacy: `tglWp_ind_simple` over the
  WP, value/non-value case split, `glm_strong_mono` to fit the glm leaf
  to `glm_implies_tgl`'s shape, then pure-`Tgl` extraction.
* `glm_implies_tgl` — `glm_strong_ind` induction with each disjunct
  closed using `Tgl.epsilon_limit` (ε-limit) and `Tgl.dbind_prim_step`
  (prim-step), and `iProp_fupd_plainly_forall_pure_impl_no_lc` to
  commute the per-leaf fupd over the universal at each branch.
* `twp_tgl` itself: `fupd_soundness_no_lc` + `app_ra_init` + `ec_alloc`
  to allocate the ghost state, then `twp_step_fupd_tgl`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {hlc : Bool} {GF : BundledGFunctors}

/-- Graded-probability total lift `Tgl μ φ ε`: the measure `μ` has mass at
least `1 - ε` concentrated on value-cfg outcomes satisfying `φ`. Rocq:
`tgl` (`clutch/common/graded_predicate_lifting.v`).

The Rocq form is `1 - ε ≤ prob μ φ` where `prob μ φ = μ {ρ | φ ρ}`
restricted to value outcomes. Here we phrase it directly using the
predicate `∃ v, ρ.expr = .ofVal v ∧ φ v` which lifts `φ : Val → Prop`
to a `Cfg → Prop`. -/
@[expose]
def Tgl (μ : MeasureTheory.Measure Cfg) (φ : Val → Prop) (ε : ENNReal) : Prop :=
  1 - ε ≤ μ {ρ : Cfg | ∃ v : Val, ρ.expr = Exp.ofVal v ∧ φ v}

namespace Tgl

/-- Termination-mass inequality. Rocq: `tgl_termination_ineq`
(`graded_predicate_lifting.v:744`). The masses on the φ-set bound the
overall mass from below. -/
theorem termination_ineq {μ : MeasureTheory.Measure Cfg} {φ : Val → Prop}
    {ε : ENNReal} (h : Tgl μ φ ε) : 1 - ε ≤ μ Set.univ :=
  h.trans (MeasureTheory.measure_mono (Set.subset_univ _))

/-- `Tgl μ φ ε` together with `μ Set.univ ≤ 1` (sub-probability) gives
`Pgl ε (¬ value-and-φ) μ`. Rocq: `tgl_implies_pgl`. -/
theorem implies_pgl {μ : MeasureTheory.Measure Cfg} {φ : Val → Prop}
    {ε : ENNReal} (hμ : μ Set.univ ≤ 1) (h : Tgl μ φ ε) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) μ := by
  -- Chain: `μ Sᶜ ≤ μ univ - μ S ≤ 1 - μ S ≤ ε`, the first from
  -- `μ S + μ Sᶜ = μ univ` (with μ S ≠ ⊤), the third from `Tgl`'s
  -- `1 - ε ≤ μ S` via `tsub_le_iff_left`.
  set S : Set Cfg := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  show μ Sᶜ ≤ ε
  have hSc_add : μ Sᶜ + μ S = μ Set.univ := by
    rw [add_comm, MeasureTheory.measure_add_measure_compl MeasurableSet.of_discrete]
  have hμS_le_one : μ S ≤ 1 := (MeasureTheory.measure_mono (Set.subset_univ _)).trans hμ
  have hS_ne_top : μ S ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top ENNReal.one_ne_top hμS_le_one
  have h_one_minus_le : 1 - μ S ≤ ε := by
    have hh : 1 - ε ≤ μ S := h
    rw [_root_.tsub_le_iff_left]
    rw [_root_.tsub_le_iff_left] at hh
    rwa [add_comm]
  -- `μ S + μ Sᶜ ≤ μ S + ε` via the chain, then cancel left.
  have hcomb : μ S + μ Sᶜ ≤ μ S + ε := by
    rw [add_comm (μ S) (μ Sᶜ), hSc_add]
    refine hμ.trans ?_
    rw [_root_.tsub_le_iff_left] at h_one_minus_le
    exact h_one_minus_le
  exact (ENNReal.add_le_add_iff_left hS_ne_top).mp hcomb

/-- Monotonicity in the error grade. Rocq: `tgl_mon_grading`. -/
theorem mono_grading {μ : MeasureTheory.Measure Cfg} {φ : Val → Prop}
    {ε ε' : ENNReal} (hε : ε ≤ ε') (h : Tgl μ φ ε) : Tgl μ φ ε' :=
  (tsub_le_tsub_left hε 1).trans h

/-- `1 ≤ ε` trivially gives `Tgl μ φ ε` for any `μ`, `φ`. Rocq:
`tgl_ge_1`. -/
theorem of_ge_one {μ : MeasureTheory.Measure Cfg} {φ : Val → Prop}
    {ε : ENNReal} (hε : 1 ≤ ε) : Tgl μ φ ε := by
  show 1 - ε ≤ _
  rw [tsub_eq_zero_of_le hε]
  exact zero_le _

/-- Monotonicity in the predicate (covariant). Rocq: `tgl_mon_pred`. -/
theorem mono_pred {μ : MeasureTheory.Measure Cfg} {φ ψ : Val → Prop}
    {ε : ENNReal} (hφψ : ∀ v, φ v → ψ v) (h : Tgl μ φ ε) : Tgl μ ψ ε := by
  refine h.trans (MeasureTheory.measure_mono ?_)
  rintro x ⟨v, hxv, hφ⟩
  exact ⟨v, hxv, hφψ v hφ⟩

/-- Predicate extensionality. Rocq: `tgl_ext`. -/
theorem ext {μ : MeasureTheory.Measure Cfg} {φ ψ : Val → Prop}
    {ε : ENNReal} (h_iff : ∀ v, φ v ↔ ψ v) (h : Tgl μ φ ε) : Tgl μ ψ ε :=
  mono_pred (fun v => (h_iff v).mp) h

/-- Dirac on a value config satisfies `Tgl` at grade 0 whenever the
value satisfies the predicate. Rocq: `tgl_dret`. -/
theorem of_dirac_val {v : Val} {σ : State} {φ : Val → Prop} (hφ : φ v) :
    Tgl (MeasureTheory.Measure.dirac (⟨Exp.ofVal v, σ⟩ : Cfg)) φ 0 := by
  show 1 - 0 ≤ _
  rw [tsub_zero]
  have h_mem : (⟨Exp.ofVal v, σ⟩ : Cfg) ∈
      {ρ : Cfg | ∃ v', ρ.expr = Exp.ofVal v' ∧ φ v'} := ⟨v, rfl, hφ⟩
  rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
  simp [Set.indicator_of_mem h_mem]

/-- `Tgl` for `limExec` at a value config: when `e` is already a value
`v` with `φ v`, the program terminates at grade `0`. Pure structural
fact independent of the WP soundness. -/
theorem of_limExec_val {v : Val} {σ : State} {φ : Val → Prop} (hφ : φ v) :
    Tgl (limExec (⟨Exp.ofVal v, σ⟩ : Cfg)) φ 0 := by
  show Tgl (limExec (⟨v.1, σ⟩ : Cfg)) φ 0
  rw [limExec_of_isVal v.2]
  exact of_dirac_val hφ

/-- ε-limit: if `Tgl μ φ ε` holds for every `ε > ε'`, then `Tgl μ φ ε'`.
Rocq: `tgl_epsilon_limit`. Needed for `twp_tgl_limit`. -/
theorem epsilon_limit {μ : MeasureTheory.Measure Cfg} {φ : Val → Prop}
    {ε' : ENNReal} (h : ∀ ε, ε' < ε → Tgl μ φ ε) : Tgl μ φ ε' := by
  set S : Set Cfg := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  show 1 - ε' ≤ μ S
  -- By contradiction: pick `c` strictly between `μ S` and `1 - ε'`. Then
  -- both `c < 1 - ε'` and the needed `ε' < 1 - c` are equivalent to
  -- `¬ (1 ≤ c + ε')` via `tsub_le_iff_left`, so apply `h` at `ε = 1 - c`.
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hμSc, hc1⟩ := exists_between hcon
  have hc_le_one : c ≤ 1 := hc1.le.trans tsub_le_self
  have hε_gt : ε' < 1 - c := by
    rw [_root_.lt_iff_not_ge]
    rw [_root_.tsub_le_iff_left]
    rw [_root_.lt_iff_not_ge, _root_.tsub_le_iff_left] at hc1
    intro hge; exact hc1 (by rwa [add_comm])
  have hTglε := h (1 - c) hε_gt
  have hTglS : 1 - (1 - c) ≤ μ S := hTglε
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hc_le_one] at hTglS
  exact absurd hTglS (_root_.not_le.mpr hμSc)

/-- Generic measure-theoretic core. Both `tgl_prim_step` (prim-step on
`Cfg`) and `tgl_state_step` (tape presample on `State`) specialize to
this. -/
theorem tgl_lift_prob
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {M : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure M]
    {ε ε₁ : ENNReal} {ε₂ : α → ENNReal}
    {R : α → Prop} {k : α → ENNReal}
    (Hpgl : M {a | ¬ R a} ≤ ε₁)
    (Hsum : ε₁ + (∫⁻ a, ε₂ a ∂M) ≤ ε)
    (Hcont : ∀ a, R a → 1 - ε₂ a ≤ k a) :
    1 - ε ≤ ∫⁻ a, k a ∂M := by
  have hM_univ : M Set.univ = 1 := MeasureTheory.measure_univ
  have hMR : 1 - ε₁ ≤ M {a | R a} := by
    have hMR_eq : M {a | R a} + M {a | ¬ R a} = M Set.univ := by
      have h_compl : {a | ¬ R a} = {a | R a}ᶜ := rfl
      rw [h_compl, MeasureTheory.measure_add_measure_compl MeasurableSet.of_discrete]
    rw [hM_univ] at hMR_eq
    rw [_root_.tsub_le_iff_left]
    calc 1 = M {a | R a} + M {a | ¬ R a} := hMR_eq.symm
      _ ≤ M {a | R a} + ε₁ := by gcongr
      _ = ε₁ + M {a | R a} := add_comm _ _
  have h_int_lb : 1 - ε₁ - (∫⁻ a, ε₂ a ∂M) ≤ ∫⁻ a, k a ∂M := by
    have h_R_bound : ∫⁻ a in {a | R a}, (1 - ε₂ a) ∂M ≤ ∫⁻ a in {a | R a}, k a ∂M := by
      apply MeasureTheory.setLIntegral_mono_ae .of_discrete
      refine .of_forall fun a ha => Hcont a ha
    have h_R_upper : ∫⁻ a in {a | R a}, k a ∂M ≤ ∫⁻ a, k a ∂M :=
      MeasureTheory.setLIntegral_le_lintegral _ _
    have h_split : M {a | R a} ≤ (∫⁻ a in {a | R a}, (1 - ε₂ a) ∂M)
                                + (∫⁻ a in {a | R a}, ε₂ a ∂M) := by
      rw [← MeasureTheory.lintegral_add_left]
      · rw [show M {a | R a} = ∫⁻ _ in {a | R a}, (1 : ENNReal) ∂M by
            rw [MeasureTheory.setLIntegral_const, one_mul]]
        apply MeasureTheory.lintegral_mono
        intro a
        exact le_tsub_add
      · exact .of_discrete
    have h_R_combined : 1 - ε₁ ≤ (∫⁻ a in {a | R a}, (1 - ε₂ a) ∂M)
                                + (∫⁻ a in {a | R a}, ε₂ a ∂M) := hMR.trans h_split
    have step1 : 1 - ε₁ - (∫⁻ a, ε₂ a ∂M) ≤ ∫⁻ a in {a | R a}, (1 - ε₂ a) ∂M := by
      rw [_root_.tsub_le_iff_right]
      refine h_R_combined.trans ?_
      gcongr
      exact MeasureTheory.Measure.restrict_le_self
    refine step1.trans ?_
    exact h_R_bound.trans h_R_upper
  refine _root_.le_trans ?_ h_int_lb
  rw [tsub_tsub]
  exact tsub_le_tsub_left Hsum 1

/-- Pure measure-theoretic step lemma backing the inductive step of
`twp_tgl`. Rocq: `twp_step_fupd_tgl_prim_step` (`total_adequacy.v:9`).

Given an `R`-and-grade decomposition of one prim_step (`Pgl R ε₁`,
expected `ε₂`-grading bounded by `ε - ε₁`), plus a continuation that
holds on the `R`-cone, we get the same bound after stepping. -/
theorem tgl_prim_step
    {e : Exp} {σ : State} {ε ε₁ : ENNReal} {ε₂ : Cfg → ENNReal}
    {R : Cfg → Prop} {P : Set Cfg}
    (Hred : Reducible e σ)
    (Hsum : ε₁ + (∫⁻ ρ, ε₂ ρ ∂primStep ⟨e, σ⟩) ≤ ε)
    (Hpgl : Pgl ε₁ R (primStep ⟨e, σ⟩))
    (Hcont : ∀ ρ, R ρ → 1 - ε₂ ρ ≤ (limExec ρ) P) :
    1 - ε ≤ ∫⁻ ρ, (limExec ρ) P ∂primStep ⟨e, σ⟩ :=
  haveI : MeasureTheory.IsProbabilityMeasure (primStep ⟨e, σ⟩) :=
    prim_step_mass ⟨e, σ⟩ Hred
  tgl_lift_prob (M := primStep ⟨e, σ⟩) (R := R) (ε₂ := ε₂)
    (k := fun ρ => (limExec ρ) P) Hpgl Hsum Hcont

/-- State-step analog of `tgl_prim_step`: the pure measure-theoretic
core for a single tape-presample. Requires the tape `α` to be active
with positive bound (which makes `tapePresample σ α` a probability
measure). Used by the future `tgl_state_step`-driven branch of
`glm_implies_tgl`. -/
theorem tgl_state_step
    {e : Exp} {σ : State} {α : Loc} {t : Tape}
    (htape : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    {ε ε₁ : ENNReal} {ε₂ : State → ENNReal}
    {R : State → Prop} {P : Set Cfg}
    (Hsum : ε₁ + (∫⁻ σ', ε₂ σ' ∂tapePresample σ α) ≤ ε)
    (Hpgl : Pgl ε₁ R (tapePresample σ α))
    (Hcont : ∀ σ', R σ' → 1 - ε₂ σ' ≤ (limExec ⟨e, σ'⟩) P) :
    1 - ε ≤ ∫⁻ σ', (limExec ⟨e, σ'⟩) P ∂tapePresample σ α :=
  haveI : MeasureTheory.IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one htape hN⟩
  tgl_lift_prob (M := tapePresample σ α) (R := R) (ε₂ := ε₂)
    (k := fun σ' => (limExec ⟨e, σ'⟩) P) Hpgl Hsum Hcont

/-- **`Tgl` one-step decomposition** at `limExec`. If `e` is reducible
and we have a Pgl/Tgl decomposition of one prim-step that continues to a
Tgl-bound on `limExec` of the successor, we get a Tgl-bound on
`limExec ⟨e, σ⟩`.

This is the high-level wrapper around `tgl_prim_step`, expressed at the
`Tgl` predicate level so it composes with the rest of the `Tgl` algebra
without needing to unfold to the raw measure inequality.

Mirrors the prim-step branch of Rocq's `twp_step_fupd_tgl_prim_step` +
`tgl_dbind`. -/
theorem dbind_prim_step
    {e : Exp} {σ : State} {ε ε₁ : ENNReal} {ε₂ : Cfg → ENNReal}
    {R : Cfg → Prop} {φ : Val → Prop}
    (Hred : Reducible e σ)
    (Hsum : ε₁ + (∫⁻ ρ, ε₂ ρ ∂primStep ⟨e, σ⟩) ≤ ε)
    (Hpgl : Pgl ε₁ R (primStep ⟨e, σ⟩))
    (Hcont : ∀ ρ, R ρ → Tgl (limExec ρ) φ (ε₂ ρ)) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  set S : Set Cfg := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  show 1 - ε ≤ (limExec ⟨e, σ⟩) S
  -- `e` is reducible, hence non-value, hence `limExec ⟨e, σ⟩ = primStep ⟨e, σ⟩ >>= limExec`.
  have hnv : ¬ (e.isValue) := by
    intro hv
    rcases Hred with ⟨ρ, hρ⟩
    exact val_stuck hρ hv
  rw [limExec_not_final hnv]
  -- `(primStep ρ).bind limExec` evaluated at `S` is `∫⁻ ρ', limExec ρ' S ∂primStep ρ`.
  rw [MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  exact Tgl.tgl_prim_step Hred Hsum Hpgl (fun ρ hρ => Hcont ρ hρ)

/-- **`Tgl` state-step decomposition** at `limExec`. Parallel of
`dbind_prim_step` for tape presampling. Uses the `asExpr`-level tape
erasure equality (`limExec_tape_presample_expr_eq`) to bridge the
presampled bind back to `limExec ⟨e, σ⟩`. -/
theorem dbind_state_step
    {e : Exp} {σ : State} {α : Loc} {t : Tape}
    (htape : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    {ε ε₁ : ENNReal} {ε₂ : State → ENNReal}
    {R : State → Prop} {φ : Val → Prop}
    (Hsum : ε₁ + (∫⁻ σ', ε₂ σ' ∂tapePresample σ α) ≤ ε)
    (Hpgl : Pgl ε₁ R (tapePresample σ α))
    (Hcont : ∀ σ', R σ' → Tgl (limExec ⟨e, σ'⟩) φ (ε₂ σ')) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  set S : Set Cfg := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}
  set S' : Set Exp := {e | ∃ v, e = Exp.ofVal v ∧ φ v}
  have hS_pre : S = (·.expr) ⁻¹' S' := rfl
  show 1 - ε ≤ (limExec ⟨e, σ⟩) S
  -- The Tgl bound on the bind via `tgl_state_step`.
  have h_bind : 1 - ε ≤ ∫⁻ σ', (limExec ⟨e, σ'⟩) S ∂tapePresample σ α :=
    Tgl.tgl_state_step htape hN Hsum Hpgl (fun σ' hσ' => Hcont σ' hσ')
  -- Convert the integral to `((tapePresample σ α).bind (limExec ⟨e, ·⟩)) S`.
  rw [← MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable] at h_bind
  -- Bridge via `asExpr` (image under `(·.expr)`):
  --   (bind) S = (asExpr bind) S' = (limExecV ⟨e, σ⟩) S' = (asExpr (limExec ⟨e, σ⟩)) S'
  --           = (limExec ⟨e, σ⟩) S.
  have h_eq : ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) S
            = (limExec ⟨e, σ⟩) S := by
    have hmap1 : ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) S
        = asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) S' := by
      unfold asExpr
      rw [MeasureTheory.Measure.map_apply Measurable.of_discrete .of_discrete]
      rfl
    have hmap2 : (limExec ⟨e, σ⟩) S
        = asExpr (limExec ⟨e, σ⟩) S' := by
      unfold asExpr
      rw [MeasureTheory.Measure.map_apply Measurable.of_discrete .of_discrete]
      rfl
    rw [hmap1, hmap2]
    congr 1
    exact limExec_tape_presample_expr_eq htape hN
  exact h_eq ▸ h_bind

end Tgl

/-- **Iris-side core**: extract a pure `Tgl` bound from a `glm` claim
whose leaf body carries a per-leaf pure `Tgl` claim under `|={∅}=>`.
Mirrors the inner induction of Rocq's `twp_step_fupd_tgl`. -/
theorem glm_implies_tgl [ErisGS false GF]
    {φ : Val → Prop} {e : Exp} {σ : State} {ε : ENNReal} :
    glm (GF := GF) e σ ε
        (fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝))
      ⊢@{IProp GF} iprop(|={∅}=> ⌜Tgl (limExec ⟨e, σ⟩) φ ε⌝) := by
  let Z : Cfg → ENNReal → IProp GF :=
    fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝)
  let Ψ : GlmState → IProp GF :=
    fun s => iprop(|={∅}=> ⌜Tgl (limExec s.1) φ s.2⌝)
  have : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  iintro HG
  ihave HInd : iprop(□ (∀ s, glmPre Z
      (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre Z) s')) s -∗ Ψ s)) $$ []
  · iintro !> %s HPre
    rcases s with ⟨⟨e', σ'⟩, ε'⟩
    icases HPre with ⟨HOT | HPS⟩
    · -- ε-limit branch.
      ihave Hfa : iprop(∀ ε'', ⌜ε' < ε''⌝ -∗
          |={∅}=> ⌜Tgl (limExec ⟨e', σ'⟩) φ ε''⌝) $$ [HOT]
      · iintro %ε'' %hε
        ihave HE := HOT $$ %ε'' %hε
        imod HE with HS
        icases HS with ⟨%Hvac | HZ⟩
        · imodintro; ipure_intro; exact Tgl.of_ge_one Hvac
        · ihave HZ := and_elim_l $$ HZ
          iexact HZ
      ihave Hf := iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa
      imod Hf with %Hf
      imodintro
      ipure_intro
      exact Tgl.epsilon_limit Hf
    · icases HPS with ⟨HPS | HSS⟩
      · -- prim-step branch. In `glmPrimStep`, the leaf body is `Z ρ`
        -- (not the recursive `Φ`), so `HZ` is already `|={∅}=> ⌜Tgl⌝`.
        icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %_, %Hsum, %Hpgl, HCont⟩
        ihave Hfa : iprop(∀ ρ, ⌜R ρ⌝ -∗
            |={∅}=> ⌜Tgl (limExec ρ) φ (X₂ ρ)⌝) $$ [HCont]
        · iintro %ρ %hR
          ihave HC := HCont $$ %ρ %hR
          imod HC with HS
          icases HS with ⟨%Hvac | HZ⟩
          · imodintro; ipure_intro; exact Tgl.of_ge_one Hvac
          · iexact HZ
        ihave Hf := iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa
        imod Hf with %Hf
        imodintro
        ipure_intro
        exact Tgl.dbind_prim_step Hred Hsum Hpgl Hf
      · -- state-step branch. Same shape, but indexed by σ' rather than
        -- ρ; the continuation references `Ψ` (recursive position), so
        -- `HZ` is `Ψ ∧ glm` — take the `Ψ` (= |={∅}=> ⌜Tgl⌝) side.
        icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %_, %Hsum, %Hpgl, HCont⟩
        ihave Hfa : iprop(∀ σ'', ⌜R σ''⌝ -∗
            |={∅}=> ⌜Tgl (limExec ⟨e', σ''⟩) φ (X₂ σ'')⌝) $$ [HCont]
        · iintro %σ'' %hR
          ihave HC := HCont $$ %σ'' %hR
          imod HC with HS
          icases HS with ⟨%Hvac | HZ⟩
          · imodintro; ipure_intro; exact Tgl.of_ge_one Hvac
          · ihave HZ := and_elim_l $$ HZ
            iexact HZ
        ihave Hf := iProp_fupd_plainly_forall_pure_impl_no_lc $$ Hfa
        imod Hf with %Hf
        imodintro
        ipure_intro
        exact Tgl.dbind_state_step Hαt.1 Hαt.2 Hsum Hpgl Hf
  iapply (glm_strong_ind (GF := GF) (Z := Z) (Ψ := Ψ)) $$ HInd
        %(⟨⟨e, σ⟩, ε⟩ : GlmState)
  iexact HG

/-- **Iris-side adequacy step**: from a `tglWp` triple with pure post
`φ`, plus the resource interps, derive `|={⊤,∅}=> ⌜Tgl (limExec ⟨e, σ⟩) φ ε⌝`.

The outer induction is `tglWp_ind_simple`; per-`e'`, we case-split on
whether `e'` is a value. The non-value case calls `glm_implies_tgl` to
extract the pure `Tgl` from the `glm` body produced by `tglWp_unfold_step`. -/
theorem twp_step_fupd_tgl [ErisGS false GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop} :
    iprop(stateInterp σ ∗ errInterp ε ∗ tglWp ⊤ e (fun v => iprop(⌜φ v⌝)))
      ⊢@{IProp GF} iprop(|={⊤,∅}=> ⌜Tgl (limExec ⟨e, σ⟩) φ ε⌝) := by
  iintro ⟨Hσ, Hε, HW⟩
  let Q : Exp → IProp GF := fun e' => iprop(
    ∀ σ' ε', stateInterp σ' ∗ errInterp ε' -∗
      |={⊤,∅}=> ⌜Tgl (limExec ⟨e', σ'⟩) φ ε'⌝)
  have : NonExpansive Q := nonExpansive_of_discrete_leibniz Q
  ihave Hq : Q e $$ [HW]
  · iapply (tglWp_ind_simple (E := ⊤) (Q := Q)
      (Φ := fun v => iprop(⌜φ v⌝)))
    swap; · iexact HW
    iintro !> %e' HPre %σ' %ε' ⟨Hσ', Hε'⟩
    -- Apply HPre (the `tglWpPre` body) to the resources.
    ihave HBody := HPre $$ %σ' %ε' [Hσ' Hε']
    · isplitl [Hσ']; · iexact Hσ'
      iexact Hε'
    -- HBody now has the `match e'.toVal? with ...` shape — case on htv.
    cases htv : e'.toVal? with
    | some v =>
      -- Value case: HBody reduces to `|={⊤}=> stateInterp σ' ∗ errInterp ε' ∗ ⌜φ v⌝`.
      ihave HBody' : iprop(|={⊤}=> stateInterp σ' ∗ errInterp ε' ∗ ⌜φ v⌝) $$ [HBody]
      · iexact HBody
      imod HBody' with ⟨_, _, %hφ⟩
      imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
      imodintro
      ipure_intro
      -- `Tgl.of_limExec_val` applied to the value cfg, using `htv` to
      -- convert `e'` to `Exp.ofVal v`.
      have heq : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      subst heq
      exact Tgl.mono_grading (zero_le ε') (Tgl.of_limExec_val hφ)
    | none =>
      -- Non-value case: cast HBody to its reduced form, then transform
      -- the glm body via `glm_strong_mono` to fit `glm_implies_tgl`.
      ihave HBody' : iprop(|={⊤,∅}=> glm e' σ' ε'
          (fun ρ ε₂ => iprop(|={∅,⊤}=>
            stateInterp ρ.state ∗ errInterp ε₂ ∗ Q ρ.expr))) $$ [HBody]
      · iexact HBody
      imod HBody' with HG
      -- HG : glm e' σ' ε' (fun ρ ε₂ => |={∅,⊤}=> ...).
      -- Massage the glm body via `glm_strong_mono` to produce a leaf of
      -- the form `|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝`.
      ihave HG' : iprop(glm e' σ' ε'
          (fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝))) $$ [HG]
      · iapply (glm_strong_mono (Z₁ := fun ρ ε₂ => iprop(|={∅,⊤}=>
            stateInterp ρ.state ∗ errInterp ε₂ ∗ Q ρ.expr))
          (Z₂ := fun ρ ε₂ => iprop(|={∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝)))
        isplitr [HG]
        swap
        · iexact HG
        iintro %ρ %ε₂ HL
        imod HL with ⟨Hσ'', Hε'', HQ⟩
        ihave HT := HQ $$ %ρ.state %ε₂ [Hσ'' Hε'']
        · isplitl [Hσ'']; · iexact Hσ''
          iexact Hε''
        -- Goal: `|={⊤,∅}=> ⌜Tgl (limExec ρ) φ ε₂⌝`; `HT` matches modulo
        -- `ρ = ⟨ρ.expr, ρ.state⟩`.
        iexact HT
      -- Goal: `|={∅}=> ⌜Tgl (limExec ⟨e', σ'⟩) φ ε'⌝`. Apply glm_implies_tgl.
      iapply glm_implies_tgl
      iexact HG'
  iapply Hq $$ %σ %ε
  isplitl [Hσ]; · iexact Hσ
  iexact Hε

/-- **Adequacy 1**: `tglWp` triple ⇒ graded probability statement.
Rocq: `twp_tgl` (`total_adequacy.v:407`).

Proof structure: trivial-`ε ≥ 1` case closes from `1 - ε = 0`. For
`ε < 1`, allocate state and error ghost resources via `app_ra_init` +
`ec_alloc`, then invoke `twp_step_fupd_tgl` (the iris-side adequacy
helper) and finally `fupd_soundness_no_lc` to extract the pure
inequality at the metalogic level. -/
theorem twp_tgl [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ [ErisGS false GF], iprop(↯ε) ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ ε := by
  -- Trivial case: `1 ≤ ε` makes the bound `1 - ε = 0 ≤ μ S` vacuous.
  by_cases hε : 1 ≤ ε
  · show 1 - ε ≤ _
    rw [tsub_eq_zero_of_le hε]
    exact zero_le _
  push Not at hε
  -- Substantive case: allocate ghost state, apply `twp_step_fupd_tgl`,
  -- extract pure Tgl via `fupd_soundness_no_lc`.
  refine pure_soundness (PROP := IProp GF) ?_
  refine fupd_soundness_no_lc (GF := GF) (E1 := ⊤) (E2 := ∅) (m := 0)
    (fun Hinv => ?_)
  iintro _
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (ec_alloc (GF := GF) ε hε) with ⟨%γec, HecAuth, HecFrag⟩
  letI IES : ErisGS false GF := {
    appGS := IA
    ecGS := { toECPreGS := inferInstance, γec := γec }
    invGS := Hinv }
  ihave Hwp' := Hwp $$ HecFrag
  iapply twp_step_fupd_tgl (GF := GF) (e := e) (σ := σ) (ε := ε) (φ := φ)
  isplitl [HappAuth]
  · iexact HappAuth
  isplitl [HecAuth]
  · iexact HecAuth
  iexact Hwp'

/-- **Adequacy 1, value specialization**: when `e` is already a value
satisfying the WP triple, we get `Tgl` at grade 0 (regardless of ε).
This is the "easy half" of `twp_tgl` — extractable via iris soundness
without needing the full induction. Requires the `*Pre` typeclasses to
allocate ghost state inside the proof. -/
theorem twp_tgl_value [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {v : Val} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (hε : ε < 1)
    (Hwp : ∀ [ErisGS false GF], iprop(↯ε) ⊢@{IProp GF}
      tglWp ⊤ (Exp.ofVal v) (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  -- Extract `φ v` via iris soundness, then use `of_limExec_val`.
  refine Tgl.of_limExec_val ?_
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness_no_lc (GF := GF) 0 0 (fun Hinv => ?_)
  iintro _
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (ec_alloc (GF := GF) ε hε) with ⟨%γec, HecAuth, HecFrag⟩
  letI IES : ErisGS false GF := {
    appGS := IA
    ecGS := { toECPreGS := inferInstance, γec := γec }
    invGS := Hinv }
  ihave Hwp' := Hwp $$ HecFrag
  ihave HE := ErisWpGS.tglWp_value_inv_with_state
      (E := ⊤) (v := v) (σ := σ) (ε := ε)
      (Φ := fun v => iprop(⌜φ v⌝)) $$ [Hwp' HappAuth HecAuth]
  · isplitl [Hwp']
    · iexact Hwp'
    isplitl [HappAuth]
    · iexact HappAuth
    iexact HecAuth
  imod HE with ⟨_, _, %hφ⟩
  -- Goal: |={⊤,∅}=> |={∅}▷=>^[0] ⌜φ v⌝. With n=0 the iterated fupd is identity.
  simp only [Nat.repeat]
  imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
  imodintro
  ipure_intro
  exact hφ

/-- **Adequacy 2**: termination mass. Rocq: `twp_mass_lim_exec`
(`total_adequacy.v:437`). Derived directly from `twp_tgl` +
`Tgl.termination_ineq`. -/
theorem twp_mass_lim_exec [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ [ErisGS false GF], iprop(↯ε) ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    1 - ε ≤ (limExec ⟨e, σ⟩) Set.univ :=
  Tgl.termination_ineq (twp_tgl Hwp)

/-- **Adequacy 3**: probabilistic graded-lift bound on the limit
execution. Rocq: `twp_pgl_lim` (`total_adequacy.v:447`). Derived from
`twp_tgl` + `Tgl.implies_pgl` + the sub-probability fact that
`limExec ρ Set.univ ≤ 1`. -/
theorem twp_pgl_lim [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ [ErisGS false GF], iprop(↯ε) ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) (limExec ⟨e, σ⟩) := by
  refine Tgl.implies_pgl ?_ (twp_tgl Hwp)
  exact limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)

/-- **Adequacy 1, limit form**: the WP triple only needs to hold for every
`ε' > ε`. Rocq: `twp_tgl_limit` (`total_adequacy.v:463`). Derived from
`twp_tgl` + `Tgl.epsilon_limit`. -/
theorem twp_tgl_limit [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS false GF], iprop(↯ε') ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ ε :=
  Tgl.epsilon_limit (fun ε' hε' => twp_tgl (Hwp ε' hε'))

/-- **Adequacy 2, limit form**: termination mass via the limit form. -/
theorem twp_mass_lim_exec_limit [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS false GF], iprop(↯ε') ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    1 - ε ≤ (limExec ⟨e, σ⟩) Set.univ :=
  Tgl.termination_ineq (twp_tgl_limit Hwp)

/-- **Adequacy 3, limit form**: Pgl bound via the limit form. -/
theorem twp_pgl_lim_limit [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {φ : Val → Prop}
    (Hwp : ∀ ε', ε < ε' → ∀ [ErisGS false GF], iprop(↯ε') ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Pgl ε (fun ρ => ∃ v, ρ.expr = Exp.ofVal v ∧ φ v) (limExec ⟨e, σ⟩) := by
  refine Tgl.implies_pgl ?_ (twp_tgl_limit Hwp)
  exact limExec_leq_mass (fun n => execN_univ_le_one n ⟨e, σ⟩)

/-- **Adequacy 1, generalized value form**: if `e.toVal? = some v` (any
syntactic form that reduces to a value), the WP triple at `e` gives
`Tgl ... 0`. Derived from `twp_tgl_value` by rewriting `e` to
`Exp.ofVal v` via `Exp.ofVal_of_toVal_some`. -/
theorem twp_tgl_of_toVal [AppPreGS GF] [ECPreGS GF] [InvGpreS GF]
    {e : Exp} {σ : State} {ε : ENNReal} {v : Val} {φ : Val → Prop}
    (hev : e.toVal? = some v) (hε : ε < 1)
    (Hwp : ∀ [ErisGS false GF], iprop(↯ε) ⊢@{IProp GF}
      tglWp ⊤ e (fun v => iprop(⌜φ v⌝))) :
    Tgl (limExec ⟨e, σ⟩) φ 0 := by
  have hev' : Exp.ofVal v = e := Exp.ofVal_of_toVal_some hev
  rw [← hev']
  exact twp_tgl_value (σ := σ) hε (by rw [hev']; exact Hwp)

end TotalEris
end ProbLang
