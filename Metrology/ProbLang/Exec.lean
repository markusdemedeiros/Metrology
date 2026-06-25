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

@[fun_prop]
theorem execN_measurable (n : Nat) : Measurable (execN (rT := rT) n) := by
  induction n
  · simp [execN]
  · exact Measurable.ite (by measurability) (by measurability) (by measurability)

/-- execN conditioned on terminating in exactly N steps -/
def execExactN (N : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match N with
  | 0 => if ρ.expr.isValue then dirac ρ else 0
  | N + 1 => if ρ.expr.isValue then 0 else (primStep ρ).bind (execExactN N)

@[fun_prop]
theorem execExactN_measurable (n : Nat) : Measurable (execExactN (rT := rT) n) := by
  induction n
  · simp only [execExactN]
    exact Measurable.ite (by measurability) (by measurability) (by measurability)
  · simp only [execExactN]
    exact Measurable.ite (by measurability) (by measurability) (by measurability)

-- -- TODO: Do you exist?
-- theorem Measurable.congr [MeasurableSpace α] [MeasurableSpace β] {f g : α → β}
--     (H1 : Measurable f) (H2 : f = g) : Measurable g := H2 ▸ H1
--
-- theorem execExactN_eval_measurable (n : Nat) (HS : MeasurableSet S) :
--     Measurable fun a ↦ (execExactN (rT := rT) n a) S :=
--   (measurable_coe HS).comp (execExactN_measurable _)

-- execExactN_sum_continuous
theorem execExactN_sum_continuous {n : Nat} {ρ : Cfg rT} {S} (HS : MeasurableSet S) :
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
      rw [bind_apply HS (by measurability)]
      simp_rw [ih]
      rw [lintegral_tsum (fun k => ?G3)]
      case G3 =>
        refine Measurable.aemeasurable ?_
        refine Measurable.ite (by measurability) ?_ (by measurability)
        exact (measurable_coe HS).comp (execExactN_measurable _)
      congr 1; ext k
      by_cases hk : k < n
      · have hk' : ∀ k, k + 1 < n + 1 ↔ k < n  := by omega
        simp only [hk, hk', ↑reduceIte]
        rw [← bind_apply HS ?G5]
        case G5 =>
          refine Measurable.aemeasurable ?_
          measurability
        simp only [execExactN, hv, ↑reduceIte]
      · simp [hk]

-- execExactN_mono_continuous
theorem execExactN_mono_continuous {n : Nat} {ρ : Cfg rT} {S} (HS : MeasurableSet S) :
    execExactN n ρ S ≤ execN (n + 1) ρ S := by
  have Hunfold : execExactN n ρ S = (if n < n + 1 then execExactN n ρ S else 0) := by simp
  rw [execExactN_sum_continuous HS, Hunfold]
  exact ENNReal.le_tsum n

/-- A value terminates in exactly zero steps. -/
theorem execExactN_of_isValue {e : Exp rT} {σ : State rT} (hv : e.isValue) (j : Nat) :
    execExactN j ⟨e, σ⟩ = if j = 0 then dirac ⟨e, σ⟩ else 0 := by
  cases j <;> simp [execExactN, hv]

theorem Discrete.tsum_dirac_mul [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) (f : Cfg rT → ENNReal) : ∑' ρ', dirac ρ {ρ'} * f ρ' = f ρ := by
  rw [tsum_eq_single ρ fun ρ' hρ' => by simp [hρ'.symm]]
  simp

-- Probably not going to generalize this unless I need it for SampCert

/-- Limiting distribution of an execution, over configurations -/
def limExec (ρ : Cfg rT) : Measure (Cfg rT) := ⨆ (i : ℕ), execN i ρ

/-- Extract an expression measure from a Cfg measure -/
def asExpr (μ : Measure (Cfg rT)) : Measure (Exp rT) := μ.map (·.expr)

/-- Limiting distribution of an execution, over return values -/
def limExecV (ρ : Cfg rT) : Measure (Exp rT) := asExpr <| limExec ρ

/-! ### Measurability for arbitrary measurable `rT`. -/

-- TODO: Move me
theorem asExpr.measurable :
    Measurable (asExpr : Measure (Cfg rT) → Measure (Exp rT)) :=
  Measure.measurable_map _ Cfg.measurable_expr

theorem ENNReal.tsum_iSup_of_monotone_cts {f : ℕ → Cfg rT → ENNReal}
    (hf : ∀ a, Monotone (f · a)) (hm : ∀ x, Measurable (f x)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ => hm _) (fun _ _ hmn a => hf a hmn)

theorem iSup_measure_apply {f : ℕ → Measure (Cfg rT)} (hf : Monotone f)
    {S : Set (Cfg rT)} (HS : MeasurableSet S) :
    (⨆ i, f i) S = ⨆ i, f i S :=
  Measure.iSup_apply_of_monotone f hf HS

theorem Measure.bind_mono_right' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f g : α → Measure β) (Hf : Measurable f) (Hg : Measurable g)
    (h : ∀ a, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  refine le_intro fun S HS HNE => ?_
  rw [bind_apply HS Hf.aemeasurable, bind_apply HS Hg.aemeasurable]
  exact lintegral_mono (fun a => h a S)

theorem execN_succ_le' (n : ℕ) (ρ : Cfg rT) : execN n ρ ≤ execN (n + 1) ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ k ih =>
    rw (occs := [2]) [execN]
    rw (occs := [1]) [execN]
    split
    · exact le_refl _
    · apply Measure.bind_mono_right'
      · measurability
      · measurability
      · exact ih

/-! ### Primitive unfoldings -/

@[simp] theorem execN_zero (ρ : Cfg rT) : execN 0 ρ = 0 := rfl

@[simp] theorem execN_succ_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = dirac ρ := by
  simp [execN, hv]

theorem execN_succ_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = (primStep ρ).bind (execN n) := by
  simp [execN, hv]

def stepOrFinal (ρ : Cfg rT) : Measure (Cfg rT) :=
  if ρ.expr.isValue then dirac ρ else primStep ρ

theorem stepOrFinal_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) :
    stepOrFinal ρ = dirac ρ := by
  simp [stepOrFinal, hv]

theorem stepOrFinal_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) :
    stepOrFinal ρ = primStep ρ := by
  simp [stepOrFinal, hv]

@[fun_prop]
theorem stepOrFinal.measurable [Inhabited rT] :
    Measurable (stepOrFinal : Cfg rT → Measure (Cfg rT)) := by
  have hpred : MeasurableSet {ρ : Cfg rT | ρ.expr.isValue} := by
    -- `isValue` now also requires local closedness; `{isValue} = {isValueR} ∩ {lcb 0 = true}`.
    have : {ρ : Cfg rT | ρ.expr.isValue}
        = (fun ρ : Cfg rT => ρ.expr) ⁻¹' ({e | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) := by
      ext ρ; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff, Set.mem_preimage]
    rw [this]
    exact Cfg.measurable_expr ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet)
  exact Measurable.ite hpred measurable_dirac primStep.measurable

/-! ### Monotonicity (ported from `SampCert/SLang.lean`) -/

theorem execN_mono : ∀ {n m : ℕ} (_ : n ≤ m) (ρ : Cfg rT), execN n ρ ≤ execN m ρ := by
  intro n m h ρ
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (execN_succ_le' _ ρ)

theorem execN_monotone : Monotone fun i ↦ execN (rT := rT) i ρ := fun _ _ h => execN_mono h _

theorem execN_mono_singleton [MeasurableSingletonClass rT]
    {n m : ℕ} (h : n ≤ m) (ρ : Cfg rT) (c : Cfg rT) :
    execN n ρ {c} ≤ execN m ρ {c} :=
  execN_mono h ρ {c}

@[fun_prop]
theorem limExec.measurable : Measurable (limExec : Cfg rT → Measure (Cfg rT)) :=
  Measure.measurable_iSup_countable (fun n => execN_measurable n)
    (fun ρ _ _ h => execN_mono h ρ)

@[fun_prop]
theorem limExecV.measurable : Measurable (limExecV : Cfg rT → Measure (Exp rT)) :=
  asExpr.measurable.comp limExec.measurable


/-! ### Sub-probability -/

theorem execN_univ_le_one
    (n : Nat) (ρ : Cfg rT) : (execN n ρ) Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ k ih =>
    unfold execN
    by_cases hv : ρ.expr.isValue
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rw [bind_apply (by measurability) (Measurable.aemeasurable (by measurability))]
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

theorem limExec_not_final -- [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} (Hnv : ¬ e.isValue) :
    limExec ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind limExec := by
  have hmono : Monotone (fun n => execN n ⟨e, σ⟩) := fun _ _ h => execN_mono h _
  have hstep : Monotone fun n => (primStep ⟨e, σ⟩).bind (execN n) := fun n m h =>
    Measure.bind_mono_right' _ _ _ (execN_measurable n) (execN_measurable m) fun a => execN_mono h a
  rw [limExec, ← hmono.iSup_nat_add 1]
  simp_rw [execN_succ_not_isValue (ρ := ⟨e, σ⟩) Hnv]
  refine Measure.ext fun S HS => ?_
  rw [iSup_measure_apply hstep HS, Measure.bind_apply HS limExec.measurable.aemeasurable]
  calc ⨆ n, ((primStep ⟨e, σ⟩).bind (execN n)) S
      = ⨆ n, ∫⁻ a, execN n a S ∂primStep ⟨e, σ⟩ :=
        iSup_congr fun n => Measure.bind_apply HS (execN_measurable n).aemeasurable
    _ = ∫⁻ a, ⨆ n, execN n a S ∂primStep ⟨e, σ⟩ :=
        (lintegral_iSup (fun n => (measurable_coe HS).comp (execN_measurable n))
          fun n m h a => execN_mono h a S).symm
    _ = ∫⁻ a, limExec a S ∂primStep ⟨e, σ⟩ :=
        lintegral_congr fun a => (iSup_measure_apply (fun _ _ h => execN_mono h a) HS).symm

theorem limExec_step
    (ρ : Cfg rT) :
    limExec ρ = (if ρ.expr.isValue then dirac ρ else primStep ρ).bind limExec := by
  obtain ⟨e, σ⟩ := ρ
  by_cases hv : e.isValue
  · simp only [hv, ↑reduceIte]
    rw [Measure.dirac_bind (by measurability)]
  · simp only [hv, ↑reduceIte]
    exact limExec_not_final hv

/-- `limExec_step` written in terms of `stepOrFinal`. -/
theorem limExec_step'  (ρ : Cfg rT) : limExec ρ = (stepOrFinal ρ).bind limExec := by
  rw [limExec_step]; rfl

/-! ### `pexecN` — iterated `stepOrFinal` -/
def pexecN (n : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match n with
  | 0 => dirac ρ
  | n + 1 => (stepOrFinal ρ).bind (pexecN n)

@[fun_prop]
def pexecN_measurable {n : Nat} : Measurable (pexecN (rT := rT) n) := by
  induction n
  · simp [pexecN]
    measurability
  · simp [pexecN]
    measurability

@[simp] theorem pexecN_zero (ρ : Cfg rT) : pexecN 0 ρ = dirac ρ := rfl

theorem pexecN_succ (n : Nat) (ρ : Cfg rT) :
    pexecN (n + 1) ρ = (stepOrFinal ρ).bind (pexecN n) := rfl

theorem pexecN_one (ρ : Cfg rT) : pexecN 1 ρ = stepOrFinal ρ := by
  show (stepOrFinal ρ).bind (pexecN 0) = stepOrFinal ρ
  show (stepOrFinal ρ).bind dirac = stepOrFinal ρ
  exact Measure.bind_dirac

theorem pexecN_plus (n m : Nat) (ρ : Cfg rT) : pexecN (n + m) ρ = (pexecN n ρ).bind (pexecN m) := by
  induction n generalizing ρ with
  | zero =>
    simp
    rw [Measure.dirac_bind (by measurability)]
  | succ k ih =>
    rw [show (k + 1 + m) = (k + m) + 1 by linarith]
    simp [pexecN]
    rw [MeasureTheory.Measure.bind_bind]
    · congr 1
      grind
    · refine Measurable.aemeasurable ?_
      measurability
    · refine Measurable.aemeasurable ?_
      measurability

theorem pexecN_det_trans {n m : Nat} {ρ ρ' ρ'' : Cfg rT} (Hn : pexecN n ρ = dirac ρ')
    (Hm : pexecN m ρ' = dirac ρ'') : pexecN (n + m) ρ = dirac ρ'' := by
  rw [pexecN_plus, Hn, dirac_bind pexecN_measurable, Hm]

theorem limExec_pexecN (n : Nat) (ρ : Cfg rT) : limExec ρ = (pexecN n ρ).bind limExec := by
  induction n generalizing ρ with
  | zero =>
    rw [pexecN_zero, Measure.dirac_bind]
    measurability
  | succ k ih =>
    rw [pexecN_succ]
    conv_lhs => rw [limExec_step']
    rw [Measure.bind_bind]
    · congr 1
      funext ρ'
      exact ih ρ'
    · refine Measurable.aemeasurable ?_
      measurability
    · refine Measurable.aemeasurable ?_
      measurability

/-! ### `limExec` application and mass -/

theorem limExec_apply (ρ : Cfg rT) (HS : MeasurableSet S) :
    limExec ρ S = ⨆ n, (execN n ρ) S :=
  iSup_measure_apply execN_monotone  HS

theorem limExec_univ' (ρ : Cfg rT) : (limExec ρ) .univ = ⨆ n, (execN n ρ) .univ :=
  limExec_apply _ .univ

/-! ### Pointwise and mass bounds -/

theorem limExec_leq_setwise {ρ : Cfg rT} {S : Set (Cfg rT)} {r : ENNReal} (HS : MeasurableSet S)
    (H : ∀ n, (execN n ρ) S ≤ r) : (limExec ρ) S ≤ r := by
  rw [limExec_apply _ HS]
  exact iSup_le H

-- Rocq: lim_exec_leq
theorem limExec_leq_mass  {ρ : Cfg rT} {r : ENNReal}
    (H : ∀ n, (execN n ρ) Set.univ ≤ r) : (limExec ρ) Set.univ ≤ r := by
  rw [limExec_univ']; exact iSup_le H

theorem limExec_term  {ρ : Cfg rT} {n : Nat} (Hv : (execN n ρ) Set.univ = 1) :
    limExec ρ = execN n ρ := by
  have hfin_n : IsFiniteMeasure (execN n ρ) :=
    ⟨by rw [Hv]; exact ENNReal.one_lt_top⟩
  have hk_eq : ∀ k, n ≤ k → execN k ρ = execN n ρ := by
    intro k hk
    have hk_univ : (execN k ρ) Set.univ = 1 := by
      refine le_antisymm (execN_univ_le_one k ρ) ?_
      calc (1 : ENNReal) = (execN n ρ) Set.univ := Hv.symm
        _ ≤ (execN k ρ) Set.univ := (execN_mono hk ρ) _
    exact (Measure.eq_of_le_of_measure_univ_eq (execN_mono hk ρ) (Hv.trans hk_univ.symm)).symm
  ext
  rename_i S HS
  rw [limExec_apply _ HS]
  apply le_antisymm
  · apply iSup_le; intro k
    by_cases hkn : k ≤ n
    · have X := execN_mono hkn ρ
      exact measure_mono_both (execN_mono hkn ρ) (fun ⦃a⦄ => id)
    · rw [hk_eq k (Nat.le_of_not_le hkn)]
  · exact le_iSup_of_le n (le_refl _)

/-! ### Deterministic trace -/

-- Ah... this one is this way because long-running executions becomes zeroed out
theorem limExec_det_final {ρ ρ' : Cfg rT} {n : Nat} (H : (execN n ρ) = dirac ρ') :
    limExec ρ = dirac ρ' := by
  have htot : (execN n ρ) Set.univ = 1 := H ▸ dirac_apply_of_mem trivial
  rw [limExec_term htot]
  ext
  rename_i S _
  exact DFunLike.congr_fun H S

/-! ### lintegral against limExec -/

-- Good exercise
theorem lintegral_limExec'
    (ρ : Cfg rT) (f : Cfg rT → ENNReal) :
    ∫⁻ x, f x ∂(limExec ρ) = ⨆ n, ∫⁻ x, f x ∂(execN n ρ) := by
  unfold limExec
  apply le_antisymm
  · rw [lintegral_def]
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hstep : g.lintegral (⨆ i, execN i ρ) = ⨆ n, g.lintegral (execN n ρ) := by
      have hms : ∀ x, MeasurableSet (⇑g ⁻¹' {x}) := fun x => g.measurableSet_preimage _
      simp_rw [MeasureTheory.SimpleFunc.lintegral,
        show ∀ x, (⨆ i, execN i ρ) (⇑g ⁻¹' {x}) = ⨆ n, (execN n ρ) (⇑g ⁻¹' {x})
          from fun x => iSup_measure_apply execN_monotone (hms x),
        ENNReal.mul_iSup]
      exact ENNReal.finsetSum_iSup_of_monotone
        (fun x _ _ h => mul_le_mul' le_rfl ((execN_mono h ρ) _))
    rw [hstep]
    refine iSup_mono fun n => ?_
    rw [lintegral_def]
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · exact iSup_le fun n => lintegral_mono' (le_iSup (fun i => execN i ρ) n) le_rfl

/-! ### Additive coupling lift (Approxis glue) -/

-- Rocq: lim_exec_ARcoupl, specialized to additive form.
-- If every finite unrolling is AddCoupl-related to μ₂ at slack ε, so is limExec.
theorem limExec_AddCoupl [Countable rT] [MeasurableSingletonClass rT]
    {β : Type*} [MeasurableSpace β] {ε : ENNReal}
    {Φ : Set (Cfg rT × β)} {ρ : Cfg rT} {μ₂ : Measure β}
    (H : ∀ n, AddCoupl ε Φ (execN n ρ) μ₂) :
    AddCoupl ε Φ (limExec ρ) μ₂ := by
  intro ⟨f, hf, hfb⟩ ⟨g, hg, hgb⟩ hfg
  rw [lintegral_limExec' ρ f]
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
