module

public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Discrete
public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

def execN (n : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match n with
  | 0 => 0
  | n + 1 => if ρ.expr.isValue then dirac ρ else (primStep ρ).bind (execN n)

/-- execN conditioned on terminating in exactly N steps -/
def execExactN (N : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match N with
  | 0 => if ρ.expr.isValue then dirac ρ else 0
  | N + 1 => if ρ.expr.isValue then 0 else (primStep ρ).bind (execExactN N)

/-- execN is the sum of its conditional distributions -/
theorem execExactN_sum [Countable rT] [MeasurableSingletonClass rT]
    {n : Nat} {ρ : Cfg rT} {S} :
    execN n ρ S = ∑'(N : Nat), if N < n then execExactN N ρ S else 0 := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ n ih =>
    simp only [execN]
    by_cases hv : ρ.expr.isValue
    · simp only [↓reduceIte, hv]
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [Nat.zero_lt_succ, ↓reduceIte, execExactN, hv]
      simp
    · simp only [↓reduceIte, hv]
      rw [tsum_eq_zero_add' ENNReal.summable]
      have Hzero : (if 0 < n + 1 then (execExactN 0 ρ) S else 0) = 0 := by simp [execExactN, hv]
      rw [Hzero, zero_add]; clear Hzero
      rw [bind_apply .of_discrete Measurable.of_discrete.aemeasurable]
      simp_rw [ih]
      rw [lintegral_tsum (fun k => Measurable.of_discrete.aemeasurable)]
      congr 1; ext k
      by_cases hk : k < n
      · have hk' : ∀ k, k + 1 < n + 1 ↔ k < n  := by omega
        simp only [hk, hk', ↑reduceIte]
        rw [← bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        simp only [execExactN, hv, ↑reduceIte]
      · simp [hk]

theorem execExactN_mono [Countable rT] [MeasurableSingletonClass rT]
    {n : Nat} {ρ : Cfg rT} {S} : execExactN n ρ S ≤ execN (n + 1) ρ S := by
  have Hunfold : execExactN n ρ S = (if n < n + 1 then execExactN n ρ S else 0) := by simp
  rw [execExactN_sum, Hunfold]
  exact ENNReal.le_tsum n

/-- execN term decomposition lemma. Relates execN of K[e] with the execution of e.
Note: the theorem is untrue when execExactN is replaced with execN. -/
theorem Discrete.execN_fill_item_eq [Countable rT] [MeasurableSingletonClass rT]
    (Ki : EctxItem rT) (n : Nat) {ρ ρ'' : Cfg rT} :
    execN n (Ki.fillItemCfg ρ) {ρ''} =
      ∑' (j : Nat) (ρ' : Cfg rT), execExactN j ρ {ρ'} * execN (n - j) (Ki.fillItemCfg ρ') {ρ''} := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ n ih =>
    let ⟨e, σ⟩ := ρ
    by_cases hv : e.isValue
    · -- e is a value: RHS collapses to j=0 term = dirac ⟨e,σ⟩ ⊗ execN(n+1)
      rw [ENNReal.tsum_comm]
      rw [show (∑' (a : Cfg rT) (j : ℕ), execExactN j ⟨e, σ⟩ {a} *
          execN (n + 1 - j) (Ki.fillItemCfg a) {ρ''}) =
          ∑' (a : Cfg rT), execExactN 0 ⟨e, σ⟩ {a} *
          execN (n + 1) ⟨Ki.fillItem a.expr, a.state⟩ {ρ''} from by
        congr 1; ext a
        rw [tsum_eq_zero_add' ENNReal.summable]
        simp [execExactN, hv]]
      simp only [execExactN, hv, ↑reduceIte, dirac_apply, Set.indicator_apply,
        Set.mem_singleton_iff, Pi.one_apply, ite_mul, one_mul, zero_mul, eq_comm]
      rw [tsum_ite_eq]
      exact DFunLike.congr rfl rfl
    · have hfv : ¬(Ki.fillItem e).isValue := EctxItem.fillItem_noVal hv
      have lhs_eq : execN (n + 1) ⟨Ki.fillItem e, σ⟩ = (primStep ⟨Ki.fillItem e, σ⟩).bind (execN n) := by
        unfold execN; rw [if_neg hfv]
      have step2 : (primStep (Ki.fillItemCfg ⟨e, σ⟩)).bind (execN n) = (primStep ⟨e, σ⟩).bind (fun ρ => execN n (Ki.fillItemCfg ρ)) := by
        simp only [EctxItem.fillItemCfg]
        rw [primStep_fillItem Ki hv, Measure.bind_map .of_discrete .of_discrete]; rfl
      have lhs_eq2 := lhs_eq.trans step2
      rw [show (execN (n + 1) (Ki.fillItemCfg ⟨e, σ⟩) {ρ''} = ((primStep ⟨e, σ⟩).bind (fun ρ => execN n (Ki.fillItemCfg ρ))) {ρ''}) from congr_arg (· {ρ''}) lhs_eq2]
      rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      simp_rw [ih]
      rw [lintegral_tsum (fun j => Measurable.of_discrete.aemeasurable)]
      simp_rw [lintegral_tsum (fun a => Measurable.of_discrete.aemeasurable)]
      simp_rw [lintegral_mul_const _ Measurable.of_discrete]
      have bind_exact : ∀ i (a : Cfg rT), ∫⁻ (ρ : Cfg rT), execExactN i ⟨ρ.expr, ρ.state⟩ {a} ∂primStep ⟨e, σ⟩ =
          execExactN (i + 1) ⟨e, σ⟩ {a} := by
        intro i a
        rw [← bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        simp [execExactN, hv]
      simp_rw [bind_exact]
      symm
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [execExactN, hv, ↑reduceIte,
        show ∀ i, n + 1 - (i + 1) = n - i from fun i => by omega,
        Measure.coe_zero, Pi.zero_apply, zero_mul, tsum_zero, zero_add]

/-- Limiting distribution of an execution, over configurations -/
def limExec (ρ : Cfg rT) : Measure (Cfg rT) := ⨆ (i : ℕ), execN i ρ

/-- Extract an expression measure from a Cfg measure -/
def asExpr (μ : Measure (Cfg rT)) : Measure (Exp rT) := μ.map (·.expr)

/-- Limiting distribution of an execution, over return values -/
def limExecV (ρ : Cfg rT) : Measure (Exp rT) := asExpr <| limExec ρ

/-! ### Measurability for arbitrary measurable `rT`.

These are the non-discrete analogues of the `.of_discrete`-shortcutted lemmas
scattered through this file. Each follows by routine kernel algebra (bind, iSup,
map) once `primStep.measurable` lands. -/

/-- `execN n` is measurable as a function `Cfg rT → Measure (Cfg rT)`.

Induction on `n`. Base: constant `0`. Step: `Measurable.ite` with
`isValueR.measurable ∘ Cfg.measurable_expr`, true branch `measurable_dirac`,
false branch `measurable_bind'` (taking the IH as the kernel) composed with
the (stubbed) `primStep.measurable`. -/
theorem execN.measurable [Inhabited rT] (n : Nat) :
    Measurable (execN n : Cfg rT → Measure (Cfg rT)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    -- execN (n+1) ρ = if ρ.expr.isValue then dirac ρ else (primStep ρ).bind (execN n)
    have hpred : MeasurableSet {ρ : Cfg rT | ρ.expr.isValue} := by
      have : {ρ : Cfg rT | ρ.expr.isValue} = {ρ : Cfg rT | ρ.expr.isValueR} := by
        ext ρ; exact Exp.isValue_iff_isValueR
      rw [this]
      exact (Exp.isValueR.measurable.comp Cfg.measurable_expr).setOf
    refine Measurable.ite hpred measurable_dirac ?_
    -- False branch: (primStep ρ).bind (execN n)
    exact (Measure.measurable_bind' ih).comp primStep.measurable

/-- `execExactN N` is measurable as a function `Cfg rT → Measure (Cfg rT)`.
Same shape as `execN.measurable`: induction + ite. -/
theorem execExactN.measurable [Inhabited rT] (N : Nat) :
    Measurable (execExactN N : Cfg rT → Measure (Cfg rT)) := by
  have hpred : MeasurableSet {ρ : Cfg rT | ρ.expr.isValue} := by
    have : {ρ : Cfg rT | ρ.expr.isValue} = {ρ : Cfg rT | ρ.expr.isValueR} := by
      ext ρ; exact Exp.isValue_iff_isValueR
    rw [this]
    exact (Exp.isValueR.measurable.comp Cfg.measurable_expr).setOf
  induction N with
  | zero =>
    -- execExactN 0 ρ = if ρ.expr.isValue then dirac ρ else 0
    exact Measurable.ite hpred measurable_dirac measurable_const
  | succ N ih =>
    -- execExactN (N+1) ρ = if ρ.expr.isValue then 0 else (primStep ρ).bind (execExactN N)
    refine Measurable.ite hpred measurable_const ?_
    exact (Measure.measurable_bind' ih).comp primStep.measurable

/-- `asExpr : Measure (Cfg rT) → Measure (Exp rT)` is measurable in its argument. -/
theorem asExpr.measurable :
    Measurable (asExpr : Measure (Cfg rT) → Measure (Exp rT)) :=
  Measure.measurable_map _ Cfg.measurable_expr

-- (`limExec.measurable` / `limExecV.measurable` appear below, after
-- `execN_mono` is in scope.)

/-! ## `execN` / `limExec` metatheory — ported from Rocq `theories/prob/markov.v`.

We do not port the `markov` structure itself. Rocq's `step_or_final`, `pexec n`
and `exec n` all collapse to our `execN` because `mstate_ret = Cfg`. See
`notes/plan-markov.md` for the full port plan. -/

/-- `∑'` and `⨆` commute for monotone ℕ-indexed ENNReal sequences. -/
theorem ENNReal.tsum_iSup_of_monotone [Countable rT] [MeasurableSingletonClass rT]
    {f : ℕ → Cfg rT → ENNReal} (hf : ∀ a, Monotone (f · a)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ => Measurable.of_discrete) (fun _ _ hmn a => hf a hmn)

/-- Apply an `iSup` of measures at a singleton of a discrete space (specialized
to `Cfg`). Mathlib does not provide a `Measure.iSup_apply` for general sets;
this is the specialized form we need. -/
theorem Discrete.iSup_measure_apply [Countable rT] [MeasurableSingletonClass rT]
    {f : ℕ → Measure (Cfg rT)} {c : Cfg rT} :
    (⨆ i, f i) {c} = ⨆ i, f i {c} := by
  apply le_antisymm
  · let w : Cfg rT → ENNReal := fun a => ⨆ i, f i {a}
    let μ : Measure (Cfg rT) := Measure.sum (fun (a : Cfg rT) => w a • Measure.dirac a)
    have hval : μ {c} = w c := by
      simp only [μ, Measure.sum_apply _ MeasurableSet.of_discrete,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
      simp only [mul_ite, mul_one, mul_zero]
      rw [tsum_eq_single c (by intro b hb; simp [hb])]
      simp
    have hub : ∀ i, f i ≤ μ := by
      intro i
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.sum_apply _ hs]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs,
        Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
      rw [← Measure.sum_smul_dirac (f i)]
      rw [Measure.sum_apply _ hs]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs,
        Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
      apply ENNReal.tsum_le_tsum
      intro a
      split
      · exact le_iSup (fun i => f i {a}) i
      · exact le_refl _
    have := Measure.le_iff'.mp (iSup_le hub) ({c} : Set (Cfg rT))
    simp only [hval] at this
    exact this
  · exact iSup_le (fun i => by gcongr; exact le_iSup f i)

/-- `Measure.bind` is monotone in its kernel argument (discrete case). -/
theorem Measure.bind_mono_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    (μ : Measure α) (f g : α → Measure β)
    (h : ∀ a, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  intro S
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  exact lintegral_mono (fun a => h a S)

/-- Helper: `execN n ≤ execN (n+1)`. -/
private theorem execN_succ_le [Countable rT] [MeasurableSingletonClass rT]
    (n : ℕ) (ρ : Cfg rT) : execN n ρ ≤ execN (n + 1) ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ k ih =>
    simp only [execN]
    split
    · exact le_refl _
    · exact Measure.bind_mono_right _ _ _ (fun a => ih a)

/-! ### Primitive unfoldings -/

-- Rocq: (boundary; no direct analogue — `stepN_O` / `exec 0` cases)
@[simp] theorem execN_zero (ρ : Cfg rT) : execN 0 ρ = 0 := rfl

-- Rocq: Lemma exec_is_final — applied to the successor case
@[simp] theorem execN_succ_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = dirac ρ := by
  simp [execN, hv]

-- Rocq: Lemma exec_Sn_not_final
theorem execN_succ_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = (primStep ρ).bind (execN n) := by
  simp [execN, hv]

/-- "Step-or-final": the one-step transition that absorbs at values.
Corresponds to Rocq `step_or_final`. Note that our `execN` does **not**
iterate this directly — `execN 0 = 0` (no fuel), while iterating
`stepOrFinal` starting from `dirac ρ` would give `dirac ρ` at the zero-step
mark. The two agree modulo a shift: `execN (n+1) ρ` is the subdistribution
after running `stepOrFinal` up to `n` times, provided we only count those
that have reached a value. -/
def stepOrFinal (ρ : Cfg rT) : Measure (Cfg rT) :=
  if ρ.expr.isValue then dirac ρ else primStep ρ

theorem stepOrFinal_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) :
    stepOrFinal ρ = dirac ρ := by
  simp [stepOrFinal, hv]

theorem stepOrFinal_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) :
    stepOrFinal ρ = primStep ρ := by
  simp [stepOrFinal, hv]

/-- `stepOrFinal : Cfg rT → Measure (Cfg rT)` is measurable.

`stepOrFinal ρ = if ρ.expr.isValue then dirac ρ else primStep ρ`. Use
`Measurable.ite` with predicate `isValue` (measurable via `isValueR.measurable`),
`measurable_dirac` for the true branch, and the (stubbed) `primStep.measurable`
for the false branch. -/
theorem stepOrFinal.measurable [Inhabited rT] :
    Measurable (stepOrFinal : Cfg rT → Measure (Cfg rT)) := by
  have hpred : MeasurableSet {ρ : Cfg rT | ρ.expr.isValue} := by
    have : {ρ : Cfg rT | ρ.expr.isValue} = {ρ : Cfg rT | ρ.expr.isValueR} := by
      ext ρ; exact Exp.isValue_iff_isValueR
    rw [this]
    exact (Exp.isValueR.measurable.comp Cfg.measurable_expr).setOf
  exact Measurable.ite hpred measurable_dirac primStep.measurable

/-! ### Monotonicity (ported from `SampCert/SLang.lean`) -/

-- Rocq: exec_mono / exec_mono'
theorem execN_mono [Countable rT] [MeasurableSingletonClass rT] :
    ∀ {n m : ℕ} (_ : n ≤ m) (ρ : Cfg rT), execN n ρ ≤ execN m ρ := by
  intro n m h ρ
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (execN_succ_le _ ρ)

-- Corollary: pointwise monotonicity at singletons
theorem execN_mono_singleton [Countable rT] [MeasurableSingletonClass rT]
    {n m : ℕ} (h : n ≤ m) (ρ : Cfg rT) (c : Cfg rT) :
    execN n ρ {c} ≤ execN m ρ {c} :=
  execN_mono h ρ {c}

/-- `limExec : Cfg rT → Measure (Cfg rT)` is measurable.

`limExec ρ = ⨆ n, execN n ρ`. Apply the keystone
`Measure.measurable_iSup_countable` with each `execN n` measurable and the
family monotone in `n` (`execN_mono`). The discreteness hypotheses come from
`execN_mono`'s dependence on `Measure.bind_mono_right`. -/
theorem limExec.measurable [Inhabited rT] [Countable rT] [MeasurableSingletonClass rT] :
    Measurable (limExec : Cfg rT → Measure (Cfg rT)) :=
  Measure.measurable_iSup_countable (fun n => execN.measurable n)
    (fun ρ _ _ h => execN_mono h ρ)

/-- `limExecV : Cfg rT → Measure (Exp rT)` is measurable, given `limExec.measurable`. -/
theorem limExecV.measurable [Inhabited rT] [Countable rT] [MeasurableSingletonClass rT] :
    Measurable (limExecV : Cfg rT → Measure (Exp rT)) :=
  asExpr.measurable.comp limExec.measurable

/-! ### Sub-probability -/

/-- `execN` is a sub-probability measure: total mass is at most 1.
Follows from `primStep_univ_le_one` by induction on the fuel. -/
theorem execN_univ_le_one [Countable rT] [MeasurableSingletonClass rT]
    (n : Nat) (ρ : Cfg rT) : (execN n ρ) Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ k ih =>
    unfold execN
    by_cases hv : ρ.expr.isValue
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      calc ∫⁻ a, (execN k a) Set.univ ∂(primStep ρ)
          ≤ ∫⁻ _, 1 ∂(primStep ρ) := lintegral_mono fun a => ih a
        _ = (primStep ρ) Set.univ := by simp
        _ ≤ 1 := primStep_univ_le_one ρ

/-! ### Algebraic laws

We do **not** port Rocq's `exec_plus` / `stepN_plus` directly: our `execN`
collapses Rocq's `pexec` (whose `iterM 0 = dret`) and `exec` (whose
`exec 0 non-final = dzero`) into a single function with `execN 0 = 0`.
Because of the 0-fuel boundary, the clean Rocq identity
`exec (n + m) = pexec n ≫= exec m` has no clean analogue in our port.
Instead, we work with `stepOrFinal` iterates when we need factoring, and
with `execN` directly otherwise. -/

/-! ### `limExec` basics (ported from `SampCert/SLang.lean`) -/

-- Rocq: lim_exec_final (value case)
theorem limExec_of_isVal {e : Exp rT} {σ : State rT} (Hv : IsVal e) :
    limExec ⟨e, σ⟩ = dirac ⟨e, σ⟩ := by
  unfold limExec
  have hv : e.isValue := ⟨Hv⟩
  apply le_antisymm
  · apply iSup_le; intro n; cases n with
    | zero => exact bot_le
    | succ n => simp [execN, hv]
  · exact le_iSup_of_le 1 (by simp [execN, hv])

-- Rocq: lim_exec_not_final
theorem limExec_not_final [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} (Hnv : ¬ e.isValue) :
    limExec ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind limExec := by
  unfold limExec
  have hmono : Monotone (fun n => execN n ⟨e, σ⟩) := fun _ _ h => execN_mono h _
  rw [← hmono.iSup_nat_add 1]
  simp_rw [show ∀ n, execN (n + 1) ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind (execN n)
    from fun n => by simp [execN, Hnv]]
  apply Measure.ext_of_singleton; intro c
  simp_rw [Discrete.iSup_measure_apply]
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  simp_rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  rw [← lintegral_iSup (fun n => Measurable.of_discrete)
      (fun n m hnm => fun a => execN_mono hnm a {c})]
  congr 1; ext a; exact Discrete.iSup_measure_apply.symm

-- Rocq: lim_exec_step
theorem limExec_step [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) :
    limExec ρ = (if ρ.expr.isValue then dirac ρ else primStep ρ).bind limExec := by
  obtain ⟨e, σ⟩ := ρ
  by_cases hv : e.isValue
  · simp only [hv, ↑reduceIte]
    rw [Measure.dirac_bind Measurable.of_discrete]
  · simp only [hv, ↑reduceIte]
    exact limExec_not_final hv

/-- `limExec_step` written in terms of `stepOrFinal`. -/
theorem limExec_step' [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) : limExec ρ = (stepOrFinal ρ).bind limExec := by
  rw [limExec_step]; rfl

/-! ### `pexecN` — iterated `stepOrFinal`

Corresponds directly to Rocq `pexec n a = iterM n step_or_final a`. Unlike
`execN`, this is the iterate of `stepOrFinal` starting from `dirac ρ`, so
`pexecN 0 ρ = dirac ρ` (identity), and `pexecN (n+1) ρ` takes one more
`stepOrFinal`. This is the Lean analogue of Rocq `pexec`; our `execN` is
the Lean analogue of Rocq `exec` (shifted by 1, and keeping mstate_ret = Cfg).

The two functions are not the same up to indexing — `execN` filters out
non-values at the final layer, while `pexecN` does not. They relate via
`execN (n+1) ρ = (pexecN n ρ).bind (fun ρ' => if isValue ρ' then dirac ρ' else 0)`. -/
def pexecN (n : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match n with
  | 0 => dirac ρ
  | n + 1 => (stepOrFinal ρ).bind (pexecN n)

@[measurability]
def pexecN_measurable [Countable rT] [MeasurableSingletonClass rT]
    {n : Nat} : Measurable (pexecN (rT := rT) n) := Measurable.of_discrete


@[simp] theorem pexecN_zero (ρ : Cfg rT) : pexecN 0 ρ = dirac ρ := rfl

theorem pexecN_succ (n : Nat) (ρ : Cfg rT) :
    pexecN (n + 1) ρ = (stepOrFinal ρ).bind (pexecN n) := rfl

-- Rocq: pexec_1 / stepN_1
theorem pexecN_one (ρ : Cfg rT) : pexecN 1 ρ = stepOrFinal ρ := by
  show (stepOrFinal ρ).bind (pexecN 0) = stepOrFinal ρ
  show (stepOrFinal ρ).bind dirac = stepOrFinal ρ
  exact Measure.bind_dirac

-- Rocq: pexec_plus / stepN_plus
theorem pexecN_plus [Countable rT] [MeasurableSingletonClass rT]
    (n m : Nat) (ρ : Cfg rT) :
    pexecN (n + m) ρ = (pexecN n ρ).bind (pexecN m) := by
  induction n generalizing ρ with
  | zero =>
    rw [pexecN_zero, Nat.zero_add, Measure.dirac_bind Measurable.of_discrete]
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by ring, pexecN_succ, pexecN_succ]
    rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
    congr 1
    funext ρ'
    exact ih ρ'

theorem pexecN_det_trans [Countable rT] [MeasurableSingletonClass rT]
    {n m : Nat} {ρ ρ' ρ'' : Cfg rT} (Hn : pexecN n ρ = dirac ρ')
    (Hm : pexecN m ρ' = dirac ρ'') : pexecN (n + m) ρ = dirac ρ'' := by
  rw [pexecN_plus, Hn, dirac_bind pexecN_measurable, Hm]

-- Rocq: lim_exec_pexec
-- `limExec` factors through any finite iterate of `stepOrFinal`.
theorem limExec_pexecN [Countable rT] [MeasurableSingletonClass rT]
    (n : Nat) (ρ : Cfg rT) :
    limExec ρ = (pexecN n ρ).bind limExec := by
  induction n generalizing ρ with
  | zero =>
    rw [pexecN_zero, Measure.dirac_bind Measurable.of_discrete]
  | succ k ih =>
    rw [pexecN_succ]
    conv_lhs => rw [limExec_step']
    rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
    congr 1
    funext ρ'
    exact ih ρ'

/-! ### `limExec` application and mass -/

-- Apply `limExec` at a singleton — sup of finite unrollings
theorem Discrete.limExec_apply [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) (c : Cfg rT) :
    limExec ρ {c} = ⨆ n, (execN n ρ) {c} :=
  Discrete.iSup_measure_apply

-- Rocq: lim_exec_Sup_seq
theorem limExec_univ [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) :
    (limExec ρ) Set.univ = ⨆ n, (execN n ρ) Set.univ := by
  have hdecomp : ∀ μ : Measure (Cfg rT), μ Set.univ = ∑' c : Cfg rT, μ {c} := by
    intro μ
    rw [show (Set.univ : Set (Cfg rT)) = ⋃ c : Cfg rT, ({c} : Set (Cfg rT)) from by ext; simp]
    rw [measure_iUnion
        (fun i j hij => by simp only [Set.disjoint_singleton]; exact hij)
        (fun _ => .of_discrete)]
  rw [hdecomp (limExec ρ)]
  simp_rw [hdecomp (execN _ ρ), Discrete.limExec_apply]
  exact ENNReal.tsum_iSup_of_monotone (fun c _ _ h => execN_mono_singleton h _ _)

/-! ### Pointwise and mass bounds -/

-- Rocq: lim_exec_leq
theorem Discrete.limExec_leq_pointwise [Countable rT] [MeasurableSingletonClass rT]
    {ρ : Cfg rT} {c : Cfg rT} {r : ENNReal}
    (H : ∀ n, (execN n ρ) {c} ≤ r) : (limExec ρ) {c} ≤ r := by
  rw [Discrete.limExec_apply]; exact iSup_le H

-- Rocq: lim_exec_leq_mass
theorem limExec_leq_mass [Countable rT] [MeasurableSingletonClass rT]
    {ρ : Cfg rT} {r : ENNReal}
    (H : ∀ n, (execN n ρ) Set.univ ≤ r) : (limExec ρ) Set.univ ≤ r := by
  rw [limExec_univ]; exact iSup_le H

-- Rocq: lim_exec_term
-- If at some fuel level `n` the execN mass is 1 (total termination), limExec collapses to it.
theorem limExec_term [Countable rT] [MeasurableSingletonClass rT]
    {ρ : Cfg rT} {n : Nat}
    (Hv : (execN n ρ) Set.univ = 1) : limExec ρ = execN n ρ := by
  -- For k ≥ n we have (execN n ρ) ≤ (execN k ρ) as measures; their univ masses both
  -- sit between 1 (the n-level) and 1 (sub-probability bound), so they match. Hence
  -- execN k ρ = execN n ρ for all k ≥ n. Thus ⨆ k, execN k ρ = execN n ρ.
  -- We use `Measure.eq_of_le_of_measure_univ_eq` at each such k.
  have hfin_n : IsFiniteMeasure (execN n ρ) :=
    ⟨by rw [Hv]; exact ENNReal.one_lt_top⟩
  have hk_eq : ∀ k, n ≤ k → execN k ρ = execN n ρ := by
    intro k hk
    have hk_univ : (execN k ρ) Set.univ = 1 := by
      refine le_antisymm (execN_univ_le_one k ρ) ?_
      calc (1 : ENNReal) = (execN n ρ) Set.univ := Hv.symm
        _ ≤ (execN k ρ) Set.univ := (execN_mono hk ρ) _
    exact (Measure.eq_of_le_of_measure_univ_eq (execN_mono hk ρ) (Hv.trans hk_univ.symm)).symm
  refine Measure.ext_of_singleton fun c => ?_
  rw [Discrete.limExec_apply]
  apply le_antisymm
  · apply iSup_le; intro k
    by_cases hkn : k ≤ n
    · exact execN_mono_singleton hkn ρ c
    · rw [hk_eq k (Nat.le_of_not_le hkn)]
  · exact le_iSup_of_le n (le_refl _)

/-! ### Deterministic trace -/

-- Rocq: lim_exec_det_final (specialized: our return type is Cfg, so we phrase it at a value-Cfg)
theorem Discrete.limExec_det_final [Countable rT] [MeasurableSingletonClass rT]
    {ρ ρ' : Cfg rT} {n : Nat}
    (_hv : ρ'.expr.isValue) (H : (execN n ρ) {ρ'} = 1) :
    limExec ρ = dirac ρ' := by
  -- execN n ρ has singleton mass 1 at ρ'. Sub-probability (total ≤ 1) then forces
  -- the whole measure to concentrate at ρ'. Combine with limExec_term.
  have htot : (execN n ρ) Set.univ = 1 := by
    refine le_antisymm (execN_univ_le_one n ρ) ?_
    calc (1 : ENNReal) = (execN n ρ) {ρ'} := H.symm
      _ ≤ (execN n ρ) Set.univ := measure_mono (Set.subset_univ _)
  have hother : ∀ c ≠ ρ', (execN n ρ) {c} = 0 := by
    intro c hc
    have h_disj : Disjoint ({ρ'} : Set (Cfg rT)) {c} :=
      Set.disjoint_singleton.mpr (Ne.symm hc)
    have hunion : (execN n ρ) ({ρ'} ∪ {c}) = (execN n ρ) {ρ'} + (execN n ρ) {c} :=
      measure_union (μ := execN n ρ) h_disj (MeasurableSet.singleton c)
    have hsub : (execN n ρ) ({ρ'} ∪ {c}) ≤ (execN n ρ) Set.univ :=
      measure_mono (Set.subset_univ _)
    rw [htot, hunion, H] at hsub
    -- hsub : 1 + (execN n ρ) {c} ≤ 1
    have h1 : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    have hzero : (execN n ρ) {c} ≤ 0 := by
      have hle : 1 + (execN n ρ) {c} ≤ 1 + 0 := by simpa using hsub
      exact (ENNReal.add_le_add_iff_left h1).mp hle
    exact le_antisymm hzero bot_le
  rw [limExec_term htot]
  refine Measure.ext_of_singleton fun c => ?_
  by_cases hcρ' : c = ρ'
  · subst hcρ'; rw [H]; simp
  · rw [hother c hcρ']
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, hcρ']

/-! ### lintegral against limExec -/

/-- `lintegral` commutes with monotone `⨆` of measures on `Cfg`. -/
theorem lintegral_limExec [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) (f : Cfg rT → ENNReal) :
    ∫⁻ x, f x ∂(limExec ρ) = ⨆ n, ∫⁻ x, f x ∂(execN n ρ) := by
  simp_rw [lintegral_countable' f, Discrete.limExec_apply, ENNReal.mul_iSup]
  refine ENNReal.tsum_iSup_of_monotone (fun c i j hij => ?_)
  exact mul_le_mul' (le_refl _) (execN_mono_singleton hij _ _)

/-! ### Additive coupling lift (Approxis glue) -/

-- Rocq: lim_exec_ARcoupl, specialized to additive form.
-- If every finite unrolling is AddCoupl-related to μ₂ at slack ε, so is limExec.
theorem limExec_AddCoupl [Countable rT] [MeasurableSingletonClass rT]
    {β : Type*} [MeasurableSpace β] {ε : ENNReal}
    {Φ : Set (Cfg rT × β)} {ρ : Cfg rT} {μ₂ : Measure β}
    (H : ∀ n, AddCoupl ε Φ (execN n ρ) μ₂) :
    AddCoupl ε Φ (limExec ρ) μ₂ := by
  intro ⟨f, hf, hfb⟩ ⟨g, hg, hgb⟩ hfg
  rw [lintegral_limExec ρ f]
  refine iSup_le fun n => ?_
  exact H n ⟨f, hf, hfb⟩ ⟨g, hg, hgb⟩ hfg

end ProbLang
end


/- ## Lim Exec -/

-- Section markov_mixin.
--   Context `{Countable mstate, Countable mstate_ret}.
--   Context (step : mstate → distr mstate).
--   Context (to_final : mstate → option mstate_ret).
--
--   Record MarkovMixin := {
--     mixin_to_final_is_final a :
--       is_Some (to_final a) → ∀ a', step a a' = 0;
--   }.
-- End markov_mixin.
--
-- Structure markov := Markov {
--   mstate : Type;
--   mstate_ret : Type;
--
--   mstate_eqdec : EqDecision mstate;
--   mstate_count : Countable mstate;
--   mstate_ret_eqdec : EqDecision mstate_ret;
--   mstate_ret_count : Countable mstate_ret;
--
--   step     : mstate → distr mstate;
--   to_final : mstate → option mstate_ret;
--
--   markov_mixin : MarkovMixin step to_final;
-- }.
-- #[global] Arguments Markov {_ _ _ _ _ _} _ _ _.
-- #[global] Arguments step {_}.
-- #[global] Arguments to_final {_}.
--
-- #[global] Existing Instance mstate_eqdec.
-- #[global] Existing Instance mstate_count.
-- #[global] Existing Instance mstate_ret_eqdec.
-- #[global] Existing Instance mstate_ret_count.
--
-- Definition markov_mdp_mixin (m : markov):
--   MdpMixin (λ (x:()) s, m.(step) s) (m.(to_final)).
-- Proof.
--   constructor.
--   intros.
--   by apply markov_mixin.
-- Qed.
--
-- Canonical Structure markov_mdp (m : markov) := Mdp _ _ (markov_mdp_mixin m).
--
-- Section is_final.
--   Context {δ : markov}.
--   Implicit Types a : mstate δ.
--   Implicit Types b : mstate_ret δ.
--
--   Lemma to_final_is_final a :
--     is_Some (to_final a) → ∀ a', step a a' = 0.
--   Proof. apply markov_mixin. Qed.
--
--   Definition is_final a := is_Some (to_final a).
--
--   Lemma to_final_None a : ¬ is_final a ↔ to_final a = None.
--   Proof. rewrite eq_None_not_Some //. Qed.
--
--   Lemma to_final_None_1 a : ¬ is_final a → to_final a = None.
--   Proof. apply to_final_None. Qed.
--
--   Lemma to_final_None_2 a : to_final a = None → ¬ is_final a.
--   Proof. apply to_final_None. Qed.
--
--   Lemma to_final_Some a : is_final a ↔ ∃ b, to_final a = Some b.
--   Proof. done. Qed.
--
--   Lemma to_final_Some_1 a : is_final a → ∃ b, to_final a = Some b.
--   Proof. done. Qed.
--
--   Lemma to_final_Some_2 a b : to_final a = Some b → is_final a.
--   Proof. intros. by eexists. Qed.
--
--   Lemma is_final_dzero a : is_final a → step a = dzero.
--   Proof.
--     intros Hf.
--     apply distr_ext=> a'.
--     rewrite to_final_is_final //.
--   Qed.
--
--   #[global] Instance is_final_dec a : Decision (is_final a).
--   Proof. rewrite /is_final. apply _. Qed.
--
-- End is_final.
--
-- #[global] Hint Immediate to_final_Some_2 to_final_None_2 to_final_None_1: core.
--
-- Section reducible.
--   Context {δ : markov}.
--   Implicit Types a : mstate δ.
--
--   Definition reducible a := ∃ a', step a a' > 0.
--   Definition irreducible a := ∀ a', step a a' = 0.
--   Definition stuck a := ¬ is_final a ∧ irreducible a.
--   Definition not_stuck a := is_final a ∨ reducible a.
--
--   Lemma not_reducible a  : ¬ reducible a ↔ irreducible a.
--   Proof.
--     unfold reducible, irreducible. split.
--     - move=> /not_exists_forall_not Hneg ρ.
--       specialize (Hneg ρ). apply Rnot_gt_ge in Hneg.
--       pose proof (pmf_pos (step a) ρ). lra.
--     - intros Hall [ρ ?]. specialize (Hall ρ). lra.
--   Qed.
--
--   Lemma reducible_not_final a :
--     reducible a → ¬ is_final a.
--   Proof. move => [] a' /[swap] /is_final_dzero -> ?. inv_distr. Qed.
--
--   Lemma is_final_irreducible a : is_final a → irreducible a.
--   Proof. intros ??. rewrite is_final_dzero //. Qed.
--
--   Lemma not_not_stuck a : ¬ not_stuck a ↔ stuck a.
--   Proof.
--     rewrite /stuck /not_stuck -not_reducible.
--     destruct (decide (is_final a)); naive_solver.
--   Qed.
--
--   Lemma irreducible_dzero a :
--     irreducible a → step a = dzero.
--   Proof.
--     intros Hirr%not_reducible. apply dzero_ext=> a'.
--     destruct (decide (step a a' = 0)); [done|].
--     exfalso. eapply Hirr.
--     exists a'.
--     pose proof (pmf_le_1 (step a) a').
--     pose proof (pmf_pos (step a) a').
--     lra.
--   Qed.
--
--   Lemma reducible_not_stuck a :
--     reducible a → not_stuck a.
--   Proof. intros. by right. Qed.
--
--   Lemma mass_pos_reducible a :
--     SeriesC (step a) > 0 → reducible a.
--   Proof. by intros ?%SeriesC_gtz_ex. Qed.
--
--   Lemma reducible_mass_pos a :
--     reducible a → SeriesC (step a) > 0.
--   Proof.
--     intros [a' Ha].
--     eapply Rlt_le_trans; [done|].
--     apply pmf_le_SeriesC.
--   Qed.
--
-- End reducible.
--
-- Section markov.
--   Context {δ : markov}.
--   Implicit Types a : mstate δ.
--   Implicit Types b : mstate_ret δ.
--
--   (** * Strict partial evaluation  *)
--   Definition stepN (n : nat) a : distr (mstate δ) := iterM n step a.
--
--   Lemma stepN_O :
--     stepN 0 = dret.
--   Proof. done. Qed.
--
--   Lemma stepN_Sn a n :
--     stepN (S n) a = step a ≫= stepN n.
--   Proof. done. Qed.
--
--   Lemma stepN_1 a :
--     stepN 1 a = step a.
--   Proof. rewrite stepN_Sn stepN_O dret_id_right //. Qed.
--
--   Lemma stepN_plus a (n m : nat) :
--     stepN (n + m) a = stepN n a ≫= stepN m.
--   Proof. apply iterM_plus. Qed.
--
--   Lemma stepN_Sn_inv n a0 a2 :
--     stepN (S n) a0 a2 > 0 →
--     ∃ a1, step a0 a1 > 0 ∧ stepN n a1 a2 > 0.
--   Proof. intros (?&?&?)%dbind_pos. eauto. Qed.
--
--   Lemma stepN_det_steps n m a1 a2 :
--     stepN n a1 a2 = 1 →
--     stepN n a1 ≫= stepN m = stepN m a2.
--   Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.
--
--   Lemma stepN_det_trans n m a1 a2 a3 :
--     stepN n a1 a2 = 1 →
--     stepN m a2 a3 = 1 →
--     stepN (n + m) a1 a3 = 1.
--   Proof.
--     rewrite stepN_plus.
--     intros ->%pmf_1_eq_dret.
--     replace (dret a2 ≫= _)
--       with (stepN m a2); [|by rewrite dret_id_left].
--     intros ->%pmf_1_eq_dret.
--     by apply dret_1.
--   Qed.
--
--   (** * Non-strict partial evaluation *)
--   Definition step_or_final a : distr (mstate δ) :=
--     match to_final a with
--     | Some _ => dret a
--     | None => step a
--     end.
--
--   Lemma step_or_final_no_final a :
--     ¬ is_final a → step_or_final a = step a.
--   Proof. rewrite /step_or_final /is_final /= -eq_None_not_Some. by intros ->. Qed.
--
--   Lemma step_or_final_is_final a :
--     is_final a → step_or_final a = dret a.
--   Proof. rewrite /step_or_final /=. by intros [? ->]. Qed.
--
--   Definition pexec (n : nat) a : distr (mstate δ) := iterM n step_or_final a.
--
--   Lemma pexec_O a :
--     pexec 0 a = dret a.
--   Proof. done. Qed.
--
--   Lemma pexec_Sn a n :
--     pexec (S n) a = step_or_final a ≫= pexec n.
--   Proof. done. Qed.
--
--   Lemma pexec_plus ρ n m :
--     pexec (n + m) ρ = pexec n ρ ≫= pexec m.
--   Proof. rewrite /pexec iterM_plus //.  Qed.
--
--   Lemma pexec_1 :
--     pexec 1 = step_or_final.
--   Proof.
--     extensionality a.
--     rewrite pexec_Sn /pexec /= dret_id_right //.
--   Qed.
--
--   Lemma pexec_Sn_r a n :
--     pexec (S n) a = pexec n a ≫= step_or_final.
--   Proof.
--     assert (S n = n + 1)%nat as -> by lia.
--     rewrite pexec_plus pexec_1 //.
--   Qed.
--
--   Lemma pexec_is_final n a :
--     is_final a → pexec n a = dret a.
--   Proof.
--     intros ?.
--     induction n.
--     - rewrite pexec_O //.
--     - rewrite pexec_Sn step_or_final_is_final //.
--       rewrite dret_id_left -IHn //.
--   Qed.
--
--   Lemma pexec_no_final a n :
--     ¬ is_final a →
--     pexec (S n) a = step a ≫= pexec n.
--   Proof. intros. rewrite pexec_Sn step_or_final_no_final //. Qed.
--
--   Lemma pexec_det_step n a1 a2 a0 :
--     step a1 a2 = 1 →
--     pexec n a0 a1 = 1 →
--     pexec (S n) a0 a2 = 1.
--   Proof.
--     rewrite pexec_Sn_r.
--     intros Hs ->%pmf_1_eq_dret.
--     rewrite dret_id_left /=.
--     case_match; [|done].
--     assert (step a1 a2 = 0) as Hns; [by eapply to_final_is_final|].
--     lra.
--   Qed.
--
--   Lemma pexec_det_steps n m a1 a2 :
--     pexec n a1 a2 = 1 →
--     pexec n a1 ≫= pexec m = pexec m a2.
--   Proof. intros ->%pmf_1_eq_dret. rewrite dret_id_left //. Qed.
--
--   Lemma stepN_pexec_det n x y:
--     stepN n x y = 1 → pexec n x y = 1.
--   Proof.
--     rewrite /stepN /pexec.
--     intros H.
--     apply Rle_antisym; [done|].
--     rewrite -H.
--     apply iterM_mono => a a'.
--     destruct (decide (is_final a)).
--     - rewrite to_final_is_final //.
--     - rewrite step_or_final_no_final //.
--   Qed.
--
--   (** * Stratified evaluation to a final state *)
--   Fixpoint exec (n : nat) (a : mstate δ) {struct n} : distr (mstate_ret δ) :=
--     match to_final a, n with
--       | Some b, _ => dret b
--       | None, 0 => dzero
--       | None, S n => step a ≫= exec n
--     end.
--
--   Lemma exec_unfold (n : nat) :
--     exec n = λ a,
--       match to_final a, n with
--       | Some b, _ => dret b
--       | None, 0 => dzero
--       | None, S n => step a ≫= exec n
--       end.
--   Proof. by destruct n. Qed.
--
--   Lemma exec_is_final a b n :
--     to_final a = Some b → exec n a = dret b.
--   Proof. destruct n; simpl; by intros ->. Qed.
--
--   Lemma exec_Sn a n :
--     exec (S n) a = step_or_final a ≫= exec n.
--   Proof.
--     rewrite /step_or_final /=.
--     case_match; [|done].
--     rewrite dret_id_left -/exec.
--     by erewrite exec_is_final.
--   Qed.
--
--   Lemma exec_plus a n1 n2 :
--     exec (n1 + n2) a = pexec n1 a ≫= exec n2.
--   Proof.
--     revert a. induction n1.
--     - intro a. rewrite pexec_O dret_id_left //.
--     - intro a. replace ((S n1 + n2)%nat) with ((S (n1 + n2))); auto.
--       rewrite exec_Sn pexec_Sn.
--       apply distr_ext.
--       intro.
--       rewrite -dbind_assoc.
--       rewrite /pmf/=/dbind_pmf.
--       by setoid_rewrite IHn1.
--   Qed.
--
--   Lemma exec_pexec_relate a n:
--     exec n a = pexec n a ≫=
--                  (λ e, match to_final e with
--                              | Some b => dret b
--                              | _ => dzero
--                        end).
--   Proof.
--     revert a.
--     induction n; intros a.
--     - simpl. rewrite pexec_O.
--       rewrite dret_id_left'.
--       done.
--     - simpl. rewrite pexec_Sn.
--       rewrite -dbind_assoc'.
--       case_match eqn:H.
--       + rewrite step_or_final_is_final; last by eapply to_final_Some_2.
--         rewrite dret_id_left'.
--         rewrite pexec_is_final; last by eapply to_final_Some_2.
--         rewrite dret_id_left'. rewrite H. done.
--       + rewrite step_or_final_no_final; last by eapply to_final_None_2.
--         apply dbind_ext_right. done.
--   Qed.
--
--   Lemma exec_mono a n v :
--     exec n a v <= exec (S n) a v.
--   Proof.
--     apply refRcoupl_eq_elim.
--     move : a.
--     induction n.
--     - intros.
--       apply refRcoupl_from_leq.
--       intros b. rewrite /distr_le /=.
--       by case_match.
--     - intros; do 2 rewrite exec_Sn.
--       eapply refRcoupl_dbind; [|apply refRcoupl_eq_refl].
--       by intros ? ? ->.
--   Qed.
--
--   Lemma exec_mono' ρ n m v :
--     n ≤ m → exec n ρ v <= exec m ρ v.
--   Proof.
--     eapply (mon_succ_to_mon (λ x, exec x ρ v)).
--     intro. apply exec_mono.
--   Qed.
--
--   Lemma exec_mono_term a b n m :
--     SeriesC (exec n a) = 1 →
--     n ≤ m →
--     exec m a b = exec n a b.
--   Proof.
--     intros Hv Hleq.
--     apply Rle_antisym; [ |by apply exec_mono'].
--     destruct (decide (exec m a b <= exec n a b))
--       as [|?%Rnot_le_lt]; [done|].
--     exfalso.
--     assert (1 < SeriesC (exec m a)); last first.
--     - assert (SeriesC (exec m a) <= 1); [done|]. lra.
--     - rewrite -Hv.
--       apply SeriesC_lt; eauto.
--       intros b'. by split; [|apply exec_mono'].
--   Qed.
--
--   Lemma exec_O_not_final a :
--     ¬ is_final a →
--     exec 0 a = dzero.
--   Proof. intros ?%to_final_None_1 =>/=; by case_match. Qed.
--
--   Lemma exec_Sn_not_final a n :
--     ¬ is_final a →
--     exec (S n) a = step a ≫= exec n.
--   Proof. intros ?. rewrite exec_Sn step_or_final_no_final //. Qed.
--
--   Lemma pexec_exec_le_final n a a' b :
--     to_final a' = Some b →
--     pexec n a a' <= exec n a b.
--   Proof.
--     intros Hb.
--     revert a. induction n; intros a.
--     - rewrite pexec_O.
--       destruct (decide (a = a')) as [->|].
--       + erewrite exec_is_final; [|done].
--         rewrite !dret_1_1 //.
--       + rewrite dret_0 //.
--     - rewrite exec_Sn pexec_Sn.
--       destruct (decide (is_final a)).
--       + rewrite step_or_final_is_final //.
--         rewrite 2!dret_id_left -/exec.
--         apply IHn.
--       + rewrite step_or_final_no_final //.
--         rewrite /pmf /= /dbind_pmf.
--         eapply SeriesC_le.
--         * intros a''. split; [by apply Rmult_le_pos|].
--           by apply Rmult_le_compat.
--         * eapply pmf_ex_seriesC_mult_fn.
--           exists 1. by intros ρ.
--   Qed.
--
--   Lemma pexec_exec_det n a a' b :
--     to_final a' = Some b →
--     pexec n a a' = 1 → exec n a b = 1.
--   Proof.
--     intros Hf.
--     pose proof (pexec_exec_le_final n a a' b Hf).
--     pose proof (pmf_le_1 (exec n a) b).
--     lra.
--   Qed.
--
--   Lemma exec_pexec_val_neq_le n m a a' b b' :
--     to_final a' = Some b' →
--     b ≠ b' → exec m a b + pexec n a a' <= 1.
--   Proof.
--     intros Hf Hneq.
--     etrans; [by apply Rplus_le_compat_l, pexec_exec_le_final|].
--     etrans; [apply Rplus_le_compat_l, (exec_mono' _ n (n `max` m)), Nat.le_max_l|].
--     etrans; [apply Rplus_le_compat_r, (exec_mono' _ m (n `max` m)), Nat.le_max_r|].
--     etrans; [|apply (pmf_SeriesC (exec (n `max` m) a))].
--     by apply pmf_plus_neq_SeriesC.
--   Qed.
--
--   Lemma pexec_exec_det_neg n m a a' b b' :
--     to_final a' = Some b' →
--     pexec n a a' = 1 →
--     b ≠ b' →
--     exec m a b = 0.
--   Proof.
--     intros Hf Hexec Hv.
--     pose proof (exec_pexec_val_neq_le n m a a' b b' Hf Hv) as Hle.
--     rewrite Hexec in Hle.
--     pose proof (pmf_pos (exec m a) b).
--     lra.
--   Qed.
--
--   Lemma is_finite_Sup_seq_exec a b :
--     is_finite (Sup_seq (λ n, exec n a b)).
--   Proof.
--     apply (Rbar_le_sandwich 0 1).
--     - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--     - by apply upper_bound_ge_sup=>/=.
--   Qed.
--
--   Lemma is_finite_Sup_seq_SeriesC_exec a :
--     is_finite (Sup_seq (λ n, SeriesC (exec n a))).
--   Proof.
--     apply (Rbar_le_sandwich 0 1).
--     - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--     - by apply upper_bound_ge_sup=>/=.
--   Qed.
--
--
--   (** * Full evaluation (limit of stratification) *)
--   Definition lim_exec (a : mstate δ) : distr (mstate_ret δ) := lim_distr (λ n, exec n a) (exec_mono a).
--
--   Lemma lim_exec_unfold a b :
--     lim_exec a b = Sup_seq (λ n, (exec n a) b).
--   Proof. apply lim_distr_pmf. Qed.
--
--   Lemma lim_exec_Sup_seq a :
--     SeriesC (lim_exec a) = Sup_seq (λ n, SeriesC (exec n a)).
--   Proof.
--     erewrite SeriesC_ext; last first.
--     { intros ?. rewrite lim_exec_unfold //. }
--     erewrite MCT_seriesC; eauto.
--     - intros. apply exec_mono.
--     - intros. by eapply SeriesC_correct.
--     - rewrite (Rbar_le_sandwich 0 1).
--       + apply Sup_seq_correct.
--       + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--       + by apply upper_bound_ge_sup=>/=.
--   Qed.
--
--   Lemma lim_exec_step a :
--     lim_exec a = step_or_final a ≫= lim_exec.
--   Proof.
--    apply distr_ext.
--    intro b.
--    rewrite {2}/pmf /= /dbind_pmf.
--    rewrite lim_exec_unfold.
--    setoid_rewrite lim_exec_unfold.
--    assert
--      (SeriesC (λ a', step_or_final a a' * Sup_seq (λ n, exec n a' b)) =
--       SeriesC (λ a', Sup_seq (λ n, step_or_final a a' * exec n a' b))) as ->.
--    { apply SeriesC_ext; intro b'.
--      apply eq_rbar_finite.
--      rewrite rmult_finite.
--      rewrite (rbar_finite_real_eq).
--      - rewrite -Sup_seq_scal_l //.
--      - apply (Rbar_le_sandwich 0 1).
--        + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--        + by apply upper_bound_ge_sup=>/=. }
--    rewrite (MCT_seriesC _ (λ n, exec (S n) a b) (lim_exec a b)) //.
--    - intros. by apply Rmult_le_pos.
--    - intros.
--      apply Rmult_le_compat; [done|done|done|].
--      apply exec_mono.
--    - intros a'.
--      exists (step_or_final a a').
--      intros n.
--      rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
--    - intro n.
--      rewrite exec_Sn.
--      rewrite {3}/pmf/=/dbind_pmf.
--      apply SeriesC_correct.
--      apply (ex_seriesC_le _ (step_or_final a)); [|done].
--      intros a'. split.
--      + by apply Rmult_le_pos.
--      + rewrite <- Rmult_1_r. by apply Rmult_le_compat_l.
--    - rewrite lim_exec_unfold.
--      rewrite mon_sup_succ.
--      + rewrite (Rbar_le_sandwich 0 1).
--        * apply Sup_seq_correct.
--        * by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--        * by apply upper_bound_ge_sup=>/=.
--      + intro; apply exec_mono.
--   Qed.
--
--   Lemma lim_exec_pexec n a :
--     lim_exec a = pexec n a ≫= lim_exec.
--   Proof.
--     move : a.
--     induction n; intro a.
--     - rewrite pexec_O dret_id_left //.
--     - rewrite pexec_Sn -dbind_assoc/=.
--       rewrite lim_exec_step.
--       apply dbind_eq; [|done].
--       intros ??. apply IHn.
--   Qed.
--
--   Lemma lim_exec_det_final n a a' b :
--     to_final a' = Some b →
--     pexec n a a' = 1 →
--     lim_exec a = dret b.
--   Proof.
--     intros Hb Hpe.
--     apply distr_ext.
--     intro b'.
--     rewrite lim_exec_unfold.
--     rewrite {2}/pmf /= /dret_pmf.
--     case_bool_decide; simplify_eq.
--     - apply Rle_antisym.
--       + apply finite_rbar_le; [eapply is_finite_Sup_seq_exec|].
--         by apply upper_bound_ge_sup=>/=.
--       + apply rbar_le_finite; [eapply is_finite_Sup_seq_exec|].
--         apply (Sup_seq_minor_le _ _ n)=>/=.
--         by erewrite pexec_exec_det.
--     - rewrite -(sup_seq_const 0).
--       f_equal. apply Sup_seq_ext=> m.
--       f_equal. by eapply pexec_exec_det_neg.
--   Qed.
--
--   Lemma lim_exec_final a b :
--     to_final a = Some b →
--     lim_exec a = dret b.
--   Proof.
--     intros. erewrite (lim_exec_det_final 0%nat); [done|done|].
--     rewrite pexec_O. by apply dret_1_1.
--   Qed.
--
--   Lemma lim_exec_not_final a :
--     ¬ is_final a →
--     lim_exec a = step a ≫= lim_exec.
--   Proof.
--     intros Hn. rewrite lim_exec_step step_or_final_no_final //.
--   Qed.
--
--   Lemma lim_exec_leq a b (r : R) :
--     (∀ n, exec n a b <= r) →
--     lim_exec a b <= r.
--   Proof.
--     intro Hexec.
--     rewrite lim_exec_unfold.
--     apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
--     by apply upper_bound_ge_sup=>/=.
--   Qed.
--
--   Lemma lim_exec_leq_mass  a r :
--     (∀ n, SeriesC (exec n a) <= r) →
--     SeriesC (lim_exec a) <= r.
--   Proof.
--     intro Hm.
--     erewrite SeriesC_ext; last first.
--     { intros. rewrite lim_exec_unfold //. }
--     erewrite (MCT_seriesC _ (λ n, SeriesC (exec n a)) (Sup_seq (λ n, SeriesC (exec n a)))); eauto.
--     - apply finite_rbar_le; [apply is_finite_Sup_seq_SeriesC_exec|].
--       by apply upper_bound_ge_sup.
--     - apply exec_mono.
--     - intros. by apply SeriesC_correct.
--     - rewrite (Rbar_le_sandwich 0 1).
--       + apply (Sup_seq_correct (λ n, SeriesC (exec n a))).
--       + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
--       + by apply upper_bound_ge_sup=>/=.
--   Qed.
--
--   Lemma lim_exec_term n a :
--     SeriesC (exec n a) = 1 →
--     lim_exec a = exec n a.
--   Proof.
--     intro Hv.
--     apply distr_ext=> b.
--     rewrite lim_exec_unfold.
--     apply Rle_antisym.
--     - apply finite_rbar_le; [apply is_finite_Sup_seq_exec|].
--       rewrite -/pmf.
--       apply upper_bound_ge_sup.
--       intros n'.
--       destruct (decide (n <= n')) as [|?%Rnot_le_lt].
--       + right. apply exec_mono_term; [done|]. by apply INR_le.
--       + apply exec_mono'. apply INR_le. by left.
--     - apply rbar_le_finite; [apply is_finite_Sup_seq_exec|].
--       apply (sup_is_upper_bound (λ m, exec m a b) n).
--   Qed.
--
--   Lemma lim_exec_pos a b :
--     lim_exec a b > 0 → ∃ n, exec n a b > 0.
--   Proof.
--     intros.
--     apply Classical_Pred_Type.not_all_not_ex.
--     intros H'.
--     assert (lim_exec a b <= 0); [|lra].
--     apply lim_exec_leq => n.
--     by apply Rnot_gt_le.
--   Qed.
--
--   Lemma lim_exec_continuous_prob a ϕ r :
--     (∀ n, prob (exec n a) ϕ <= r) →
--     prob (lim_exec a) ϕ <= r.
--   Proof.
--     intro Hm.
--     rewrite /prob.
--     erewrite SeriesC_ext; last first.
--     { intro; rewrite lim_exec_unfold; auto. }
--     assert
--       (forall v, (if ϕ v then real (Sup_seq (λ n0 : nat, exec n0 a v)) else 0) =
--                  (real (Sup_seq (λ n0 : nat, if ϕ v then exec n0 a v else 0)))) as Haux.
--     { intro v.
--       destruct (ϕ v); auto.
--       rewrite sup_seq_const //.
--     }
--     assert
--       (is_finite (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0)))) as Hfin.
--     {
--       apply (Rbar_le_sandwich 0 1).
--       + apply (Sup_seq_minor_le _ _ 0%nat); simpl.
--         apply SeriesC_ge_0'.
--         intro v; destruct (ϕ v); auto.
--         lra.
--       + apply upper_bound_ge_sup; intro; simpl; auto.
--         apply (Rle_trans _ (SeriesC (exec n a))); auto.
--         apply (SeriesC_le _ (exec n a)); auto.
--         intro v; destruct (ϕ v); real_solver.
--     }
--     erewrite SeriesC_ext; last first.
--     {
--       intro; rewrite Haux //.
--     }
--     erewrite (MCT_seriesC _ (λ n, SeriesC (λ v, if ϕ v then exec n a v else 0))
--                 (Sup_seq (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))));
--       auto.
--     - apply finite_rbar_le; auto.
--       apply upper_bound_ge_sup; auto.
--     - intros n v.
--       destruct (ϕ v); auto.
--       lra.
--     - intros n v.
--       destruct (ϕ v); [ apply exec_mono | lra].
--     - intro v; destruct (ϕ v); exists 1; intro; auto; lra.
--     - intros n.
--       apply SeriesC_correct; auto.
--       apply (ex_seriesC_le _ (exec n a)); auto.
--       intro v; destruct (ϕ v); real_solver.
--     - rewrite (Rbar_le_sandwich 0 1); auto.
--       + apply (Sup_seq_correct (λ n0 : nat, SeriesC (λ v, if ϕ v then exec n0 a v else 0))).
--       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
--         apply SeriesC_ge_0'.
--         intro v; destruct (ϕ v); real_solver.
--       + apply upper_bound_ge_sup; intro; simpl; auto.
--         apply (Rle_trans _ (SeriesC (exec n a))); auto.
--         apply (SeriesC_le _ (exec n a)); auto.
--         intro v; destruct (ϕ v); real_solver.
--   Qed.
--
-- End markov.
--
-- #[global] Arguments pexec {_} _ _ : simpl never.
