import Metrology.ProbLang.Syntax
import Metrology.ProbLang.Opsem
import Metrology.ProbLang.DetStep
import SampCert.SLang
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform


noncomputable section

/-## Experiment: Translation validation from SLang to ProbLang. -/
namespace EmbedSLang

open SLang ProbLang Classical MeasureTheory ProbabilityTheory Measure PMF Measurable


class abbrev SLangType (T : Type) := Countable T, MeasurableSpace T, MeasurableSingletonClass T

class ProbLangEmbeddable (T : Type _) where
  as_expr : T → Exp
  as_expr_isVal : ∀ t, IsVal (as_expr t)
export ProbLangEmbeddable (as_expr as_expr_isVal)

/-! ## Discrete measure theory helpers -/

theorem SLang.count_bind_probBind [SLangType T] [SLangType U] {s1 : SLang T} {s2 : T → SLang U} :
    (count <| s2 ·) ∘ₘ (count s1) = count (s1.probBind s2) := by
  refine ext_of_singleton fun u => ?_
  simp [bind_apply .of_discrete of_discrete.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ of_discrete.aemeasurable of_discrete.aemeasurable,
    lintegral_count, probBind]

/-! ## SLang embedding -/

/-- Convert a SLang term into a distribution over ProbLang states. -/
def SLang.spec [SLangType T] [ProbLangEmbeddable T] (s : SLang T) (σ : State) : Measure Cfg :=
  count s |>.map as_expr |>.map (⟨·, σ⟩)

/-- A SLang program is the denotation of a ProbLang program -/
def IsEmbedding [SLangType T] [ProbLangEmbeddable T] (s : SLang T) (e : Exp) : Prop :=
  ∀ (σ : State), limExec ⟨e, σ⟩ = SLang.spec s σ

-- NOTE: Some of these theorems may need additional hypotheses.

-- fillItem version of primStep_fill
-- #check primStep_fill

-- Admitted: (⨆ i, f i) {c} = ⨆ i, f i {c} for measures on a discrete space
theorem iSup_measure_apply {f : ℕ → Measure Cfg} {c : Cfg} :
    (⨆ i, f i) {c} = ⨆ i, f i {c} := by
  apply le_antisymm
  · -- ≤ direction: construct an upper bound measure with the right singleton values
    -- Using sum of weighted Dirac measures on the discrete space
    let w : Cfg → ENNReal := fun a => ⨆ i, f i {a}
    let μ : Measure Cfg := Measure.sum (fun (a : Cfg) => w a • Measure.dirac a)
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
    have := Measure.le_iff'.mp (iSup_le hub) ({c} : Set Cfg)
    simp only [hval] at this
    exact this
  · exact iSup_le (fun i => by gcongr; exact le_iSup f i)

-- Admitted: ⨆ over monotone ENNReal can merge two indices
-- (⨆ i, f i) * (⨆ j, g j) = ⨆ n, f n * g n  when both monotone
theorem iSup_mul_iSup_of_monotone {f g : ℕ → ENNReal} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ n, f n * g n := by
  apply le_antisymm
  · -- LHS = ⨆ i, ⨆ j, f i * g j
    rw [ENNReal.iSup_mul]
    apply iSup_le; intro i
    rw [ENNReal.mul_iSup]
    apply iSup_le; intro j
    -- f i * g j ≤ f (max i j) * g (max i j) ≤ ⨆ n, f n * g n
    apply le_trans (mul_le_mul' (hf (le_max_left i j)) (hg (le_max_right i j)))
    exact le_iSup (fun n => f n * g n) (max i j)
  · -- ⨆ n, f n * g n ≤ (⨆ i, f i) * (⨆ j, g j)
    exact ENNReal.iSup_mul_le

-- Admitted: ∑' and ⨆ commute for monotone ENNReal sequences
theorem ENNReal.tsum_iSup_of_monotone {f : ℕ → Cfg → ENNReal} (hf : ∀ a, Monotone (f · a)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun n => Measurable.of_discrete) (fun m n hmn a => hf a hmn)

-- Helper: Measure.bind is monotone in the kernel argument (discrete case)
private theorem Measure.bind_mono_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    (μ : Measure α) (f g : α → Measure β)
    (h : ∀ a, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  intro S
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  exact lintegral_mono (fun a => h a S)

-- Helper: execN n ≤ execN (n+1)
private theorem execN_succ_le (n : ℕ) (ρ : Cfg) : execN n ρ ≤ execN (n + 1) ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ k ih =>
    simp only [execN]
    split
    · exact le_refl _
    · exact Measure.bind_mono_right _ _ _ (fun a => ih a)

-- execN is monotone (as measures)
theorem execN_mono : ∀ {n m : ℕ} (_ : n ≤ m) (ρ : Cfg), execN n ρ ≤ execN m ρ := by
  intro n m h ρ
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (execN_succ_le _ ρ)

-- Corollary: pointwise monotonicity at singletons
theorem execN_mono_singleton {n m : ℕ} (h : n ≤ m) (ρ : Cfg) (c : Cfg) :
    execN n ρ {c} ≤ execN m ρ {c} :=
  execN_mono h ρ {c}

-- Rocq: lim_exec_final
theorem limExec_of_isVal {e : Exp} {σ : State} (Hv : IsVal e) :
    limExec ⟨e, σ⟩ = dirac ⟨e, σ⟩ := by
  unfold limExec
  have hv : e.isValue := ⟨Hv⟩
  apply le_antisymm
  · apply iSup_le; intro n; cases n with
    | zero => exact bot_le
    | succ n => simp [execN, hv]
  · exact le_iSup_of_le 1 (by simp [execN, hv])

-- Rocq: lim_exec_not_final
theorem limExec_not_final {e : Exp} {σ : State} (Hnv : ¬ e.isValue) :
    limExec ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind limExec := by
  unfold limExec
  -- Step 1: shift index: ⨆ n, execN n = ⨆ n, execN (n+1) since execN is monotone
  have hmono : Monotone (fun n => execN n ⟨e, σ⟩) := fun _ _ h => execN_mono h _
  rw [← hmono.iSup_nat_add 1]
  -- Step 2: unfold execN (n+1) using ¬isValue
  simp_rw [show ∀ n, execN (n + 1) ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind (execN n)
    from fun n => by simp [execN, Hnv]]
  -- Step 3: push ⨆ through bind (MCT)
  apply Measure.ext_of_singleton; intro c
  simp_rw [iSup_measure_apply]
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  -- LHS: ⨆ i, (execN i ∘ₘ primStep ...) {c}
  -- Expand each term via bind_apply
  simp_rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  -- Now both sides are lintegrals; apply MCT (reversed)
  rw [← lintegral_iSup (fun n => Measurable.of_discrete)
      (fun n m hnm => fun a => execN_mono hnm a {c})]
  congr 1; ext a; exact iSup_measure_apply.symm

-- Rocq: lim_exec_step
-- lim_exec a = step_or_final a ≫= lim_exec
-- In our setting, step_or_final is: if value then dirac else primStep
theorem limExec_step (ρ : Cfg) :
    limExec ρ = (if ρ.expr.isValue then dirac ρ else primStep ρ).bind limExec := by
  obtain ⟨e, σ⟩ := ρ
  by_cases hv : e.isValue
  · simp only [hv, ↑reduceIte]
    rw [Measure.dirac_bind Measurable.of_discrete]
  · simp only [hv, ↑reduceIte]
    exact limExec_not_final hv

-- Split: n steps of Ki[e] can be bounded by splitting through intermediate configs
theorem execN_fill_item_le (Ki : EctxItem) (n : Nat) {e : Exp} {σ : State} {c : Cfg} :
    execN n (Ki.fillItemCfg ⟨e, σ⟩) {c} ≤
      ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} := by
  rw [execN_fill_item_eq]
  rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum; intro a
  -- RHS per a: expand execN n {a} via execExactN_sum, distribute
  rw [mul_comm, execExactN_sum]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum; intro j
  by_cases hj : j < n
  · simp only [hj, ↑reduceIte]
    exact mul_le_mul' le_rfl (execN_mono_singleton (Nat.sub_le n j) _ c)
  · have : n - j = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hj)
    simp [this, execN, hj]

-- Combine: j steps for e to reach a, then i steps for Ki[a] to reach c, takes i+j steps total
theorem execN_fill_item_ge (Ki : EctxItem) (i j : Nat) {e : Exp} {σ : State} {c : Cfg} :
    ∑' a, execN i (Ki.fillItemCfg a) {c} * execN j ⟨e, σ⟩ {a} ≤
      execN (i + j) (Ki.fillItemCfg ⟨e, σ⟩) {c} := by
  rw [execN_fill_item_eq]
  -- RHS = ∑' k a, execExactN k ... {a} * execN ((i+j)-k) ... {c}
  -- Bound: restrict to k < j terms, and use (i+j)-k ≥ i for k < j
  rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum; intro a
  rw [show execN i (Ki.fillItemCfg a) {c} * execN j ⟨e, σ⟩ {a} =
      execN j ⟨e, σ⟩ {a} * execN i (Ki.fillItemCfg a) {c} from mul_comm _ _]
  -- LHS: execN j {a} * execN i {c}
  -- = (∑' k, if k < j then execExactN k {a} else 0) * execN i {c}   (execExactN_sum)
  rw [execExactN_sum]
  -- LHS: (∑' k, if k < j then execExactN k {a} else 0) * execN i {c}
  -- Distribute: ∑' k, (if k < j then execExactN k {a} else 0) * execN i {c}
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum; intro k
  by_cases hk : k < j
  · simp only [hk, ↑reduceIte]
    exact mul_le_mul' le_rfl (execN_mono_singleton (by omega : i ≤ i + j - k) _ c)
  · simp [hk]

theorem limExec_fill_item (Ki : EctxItem) {e : Exp} {σ : State} :
    limExec ⟨Ki.fillItem e, σ⟩ =
      (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) := by
  -- Convert the measure bind to an explicit sum
  refine Measure.ext_of_singleton fun c => ?_
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  rw [lintegral_countable']
  unfold limExec
  -- Goal: (⨆ i, execN i ⟨Ki.fillItem e, σ⟩) {c} =
  --   ∑' a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩) {c} * (⨆ i, execN i ⟨e, σ⟩) {a}
  simp only [iSup_measure_apply]
  -- Goal: ⨆ i, execN i ... {c} = ∑' a, (⨆ i, execN i ... {c}) * (⨆ i, execN i ... {a})
  apply le_antisymm
  · -- ≤: use execN_fill_item_le + monotonicity
    apply iSup_le; intro n
    calc execN n ⟨Ki.fillItem e, σ⟩ {c}
        ≤ ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} :=
          execN_fill_item_le Ki n
      _ ≤ ∑' a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩ {c}) * (⨆ i, execN i ⟨e, σ⟩ {a}) := by
          apply ENNReal.tsum_le_tsum; intro a
          exact mul_le_mul'
            (le_iSup (fun i => (execN i ⟨Ki.fillItem a.expr, a.state⟩) {c}) n)
            (le_iSup (fun i => (execN i ⟨e, σ⟩) {a}) n)
  · -- ≥: combine two ⨆ into one, commute ∑' and ⨆, use execN_fill_item_ge
    have merge : ∀ a, (⨆ i, execN i ⟨Ki.fillItem a.expr, a.state⟩ {c}) *
        (⨆ i, execN i ⟨e, σ⟩ {a}) =
        ⨆ n, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a} :=
      fun a => iSup_mul_iSup_of_monotone
        (fun i j hij => execN_mono_singleton hij _ c)
        (fun i j hij => execN_mono_singleton hij _ a)
    simp_rw [merge]
    have commute := ENNReal.tsum_iSup_of_monotone
      (f := fun n a => execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a})
      (fun a n m hnm => mul_le_mul' (execN_mono_singleton hnm _ c)
                                     (execN_mono_singleton hnm _ a))
    rw [commute]
    apply iSup_le; intro n
    calc ∑' a, execN n ⟨Ki.fillItem a.expr, a.state⟩ {c} * execN n ⟨e, σ⟩ {a}
        ≤ execN (n + n) ⟨Ki.fillItem e, σ⟩ {c} := execN_fill_item_ge Ki n n
      _ ≤ ⨆ i, execN i ⟨Ki.fillItem e, σ⟩ {c} :=
          le_iSup (fun i => execN i ⟨Ki.fillItem e, σ⟩ {c}) (n + n)

-- Corollary: decompose app through argument evaluation.
-- Follows from limExec_fill_item with Ki = .appR ef.
theorem limExec_app {ef e : Exp} {σ : State} :
    limExec ⟨.app ef e, σ⟩ = (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨.app ef c.expr, c.state⟩) :=
  limExec_fill_item (.appR ef)

theorem limExec_beta {x : Binder} {body v : Exp} {σ : State} (hv : IsVal v) :
    limExec ⟨.app (.letrec .anon x body) v, σ⟩ = limExec ⟨Exp.subst x v body, σ⟩ := by
  have hnv : ¬ (Exp.app (.letrec .anon x body) v).isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨.app (.letrec .anon x body) v, σ⟩ {ρ} := by
    refine ⟨⟨Exp.subst x v body, σ⟩, ?_⟩; simp [headStep, Exp.isValM_some' hv, Exp.subst]
  rw [primStep_eq_headStep hred]
  simp [headStep, Exp.isValM_some' hv, Exp.subst, Measure.dirac_bind Measurable.of_discrete]

/-! ## ProbLang combinators -/

-- Values and literals
def probLangPure [ProbLangEmbeddable T] (t : T) : Exp := as_expr t
def probLangInt (z : Int) : Exp := .lit (.int z)
def probLangBool (b : Bool) : Exp := .lit (.bool b)
def probLangUnit : Exp := .lit .unit

-- Pairs
def probLangPair (e1 e2 : Exp) : Exp := .pair e1 e2
def probLangFst (e : Exp) : Exp := .fst e
def probLangSnd (e : Exp) : Exp := .snd e

-- Arithmetic
def probLangAdd (e1 e2 : Exp) : Exp := .binop .plus e1 e2
def probLangSub (e1 e2 : Exp) : Exp := .binop .minus e1 e2
def probLangMul (e1 e2 : Exp) : Exp := .binop .mult e1 e2
def probLangNegInt (e : Exp) : Exp := .unop .minus e

-- Comparisons and booleans
-- NOTE: ProbLang lacks native < and div. We postulate encodings.
-- TODO: Add BinOp.lt and BinOp.div to ProbLang, or encode them.
def probLangLt (e1 e2 : Exp) : Exp := sorry
def probLangDiv (e1 e2 : Exp) : Exp := sorry
def probLangMod (e1 e2 : Exp) : Exp := sorry
def probLangEq (e1 e2 : Exp) : Exp := .binop .eq e1 e2
def probLangNot (e : Exp) : Exp := .unop .neg e
def probLangAnd (e1 e2 : Exp) : Exp := .binop .and e1 e2

-- Control flow
def probLangCond (ec et ef : Exp) : Exp := .cond ec et ef
def probLangApp (ef ea : Exp) : Exp := .app ef ea
def probLangLam (x : String) (body : Exp) : Exp := .letrec .anon (.named x) body

theorem probLangPure_isEmbedding [SLangType T] [ProbLangEmbeddable T] {t : T} :
    IsEmbedding (probPure t) (probLangPure t) := by
  refine fun σ => ?_
  rw [probLangPure, limExec_of_isVal (as_expr_isVal t)]
  apply Measure.ext_of_singleton
  intro ⟨e', σ'⟩
  rw [SLang.spec, Measure.map_apply ?M1 ?M2, Measure.map_apply ?M3 ?M4]
  case M1 => exact measurable_id'
  case M2 => apply measurableSet_singleton
  case M3 => exact .of_discrete
  case M4 => exact .preimage trivial (fun _ => id)
  rw [withDensity_apply _ MeasurableSet.of_discrete]
  simp only [dirac_apply, Set.indicator, probPure, Set.mem_singleton_iff, Cfg.mk.injEq,
    Pi.one_apply, Set.preimage, Cfg.mk.injEq]
  by_cases hσ : σ = σ'
  · subst hσ; simp only [and_true]
    by_cases he : as_expr t = e'
    · subst he
      simp only [↓reduceIte, ← lintegral_indicator .of_discrete, lintegral_count,
        Set.indicator, Set.mem_setOf_eq]
      have : ∀ a, (if as_expr a = as_expr t then if a = t then 1 else 0 else (0 : ENNReal)) =
          if a = t then 1 else 0 := by intro a; split_ifs <;> simp_all
      simp_rw [this, tsum_ite_eq]
    · simp [he, ← lintegral_indicator .of_discrete, lintegral_count, Set.indicator, Set.mem_setOf_eq]
      symm; simp only [ENNReal.tsum_eq_zero]
      intro a; split_ifs <;> simp_all
  · simp [hσ]

def probLangBind (x : Binder) (e1 e2 : Exp) : Exp :=
  .app (.letrec .anon x e2) e1

theorem probLangBind_isEmbedding [SLangType T] [ProbLangEmbeddable T] [SLangType U]
    [ProbLangEmbeddable U] {s1 : SLang T} {s2 : T → SLang U} {e1 body : Exp} {x : String}
    (h1 : IsEmbedding s1 e1) (h2 : ∀ t, IsEmbedding (s2 t) (Exp.subst (.named x) (as_expr t) body))
    -- TODO: Does freshness matter? I mean it must, right?
    (_hfresh : Fresh x e1) :
    IsEmbedding (probBind s1 s2) (probLangBind (.named x) e1 body) := by
  intro σ
  rw [probLangBind, limExec_app, h1 σ]
  unfold SLang.spec
  rw [Measure.bind_map .of_discrete .of_discrete, Measure.bind_map .of_discrete .of_discrete]
  -- Rewrite the kernel: limExec_beta + h2
  conv_lhs =>
    arg 2; ext t; simp only [Function.comp]
    rw [limExec_beta (as_expr_isVal t), h2 t σ]
  unfold SLang.spec
  have fuse : ∀ (μ : Measure U),
      (μ.map as_expr).map (fun e => (⟨e, σ⟩ : Cfg)) =
      (fun u => dirac (⟨as_expr u, σ⟩ : Cfg)) ∘ₘ μ := by
    intro μ
    rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete, Measure.bind_map .of_discrete .of_discrete]; rfl
  simp_rw [fuse]
  rw [← SLang.count_bind_probBind,
      Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]

/-! ## Uniform byte embedding -/

instance : Countable UInt8 := ⟨⟨fun u => u.toNat, fun a b h => by ext; exact h⟩⟩
instance : MeasurableSpace UInt8 := ⊤
instance : MeasurableSingletonClass UInt8 := ⟨fun _ => trivial⟩

instance : ProbLangEmbeddable UInt8 where
  as_expr u := .lit (.int u.toNat)
  as_expr_isVal _ := .lit

-- ProbLang expression: rand 255 ()
-- Cfg.uniform 255 σ samples uniformly from Finset.Icc 0 255 = {0,...,255}
def probLangUniformByte : Exp := .rand (.lit (.int 255)) (.lit .unit)

theorem probLangUniformByte_isEmbedding :
    IsEmbedding probUniformByte probLangUniformByte := by
  intro σ
  have hnv : ¬ probLangUniformByte.isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨probLangUniformByte, σ⟩ {ρ} := by
    rw [show probLangUniformByte = Exp.rand (.lit (.int 255)) (.lit .unit) from rfl]
    simp only [headStep]
    exact ⟨_, Cfg.uniform_singleton_pos_of_mem (v := 0) (by norm_num) (by norm_num) (by norm_num)⟩
  rw [primStep_eq_headStep hred]
  show (headStep ⟨probLangUniformByte, σ⟩).bind limExec = _
  have hhead : headStep ⟨probLangUniformByte, σ⟩ = Cfg.uniform 255 σ := by
    simp [probLangUniformByte, headStep]
  rw [hhead]
  -- limExec ∘ₘ Cfg.uniform 255 σ = Cfg.uniform 255 σ
  -- because Cfg.uniform only produces value configs
  have bind_dirac : limExec ∘ₘ Cfg.uniform 255 σ = Cfg.uniform 255 σ := by
    -- Cfg.uniform 255 σ = PMF.toMeasure(...).map (⟨.lit (.int ·), σ⟩)
    -- These are all value configs, so limExec = dirac on each.
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp only [show (0 : Int) < 255 from by norm_num, dite_true]
    rw [Measure.bind_map .of_discrete .of_discrete]
    -- Goal: (limExec ∘ f) ∘ₘ μ = μ.map f where f v = ⟨.lit (.int v), σ⟩
    -- Since limExec ⟨.lit (.int v), σ⟩ = dirac ⟨.lit (.int v), σ⟩, we get (dirac ∘ f) ∘ₘ μ = μ.map f
    show (limExec ∘ fun v => (⟨.lit (.int v), σ⟩ : Cfg)) ∘ₘ _ = _
    conv_lhs => arg 2; ext v; rw [Function.comp, limExec_of_isVal (.lit (b := .int v))]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [bind_dirac]
  -- Cfg.uniform 255 σ = SLang.spec probUniformByte σ
  unfold SLang.spec
  apply Measure.ext_of_singleton; intro ⟨e', σ'⟩
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      withDensity_apply _ MeasurableSet.of_discrete]
  simp only [Set.preimage, Set.mem_singleton_iff, Cfg.mk.injEq, Set.mem_setOf_eq]
  by_cases hσ : σ = σ'
  · subst hσ; simp only [and_true]
    -- LHS: Cfg.uniform 255 σ {⟨e', σ⟩}
    -- Unfold Cfg.uniform: PMF.uniformOfFinset(.Icc 0 255).toMeasure.map (⟨.lit (.int ·), σ⟩)
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp only [show (0 : Int) < 255 from by norm_num, dite_true]
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    -- LHS: uniformOfFinset(.Icc 0 255).toMeasure {v | ⟨.lit (.int v), σ⟩ = ⟨e', σ⟩}
    --     = uniformOfFinset(.Icc 0 255).toMeasure {v | .lit (.int v) = e'}
    simp only [Set.preimage]
    simp only [Set.mem_singleton_iff, Cfg.mk.injEq, and_true]
    rw [PMF.toMeasure_apply]
    swap; exact MeasurableSet.of_discrete
    conv_rhs => rw [← lintegral_indicator (f := probUniformByte) MeasurableSet.of_discrete, lintegral_count]
    simp only [Set.indicator, Set.mem_setOf_eq, as_expr, SLang.probUniformByte, PMF.uniformOfFinset_apply, Finset.mem_Icc]
    by_cases he : ∃ (v : ℤ), Exp.lit (BaseLit.int v) = e' ∧ 0 ≤ v ∧ v ≤ 255
    · -- e' = .lit (.int v) for some v ∈ [0, 255]
      obtain ⟨v, rfl, hv0, hv255⟩ := he
      simp only [Exp.lit.injEq, BaseLit.int.injEq]
      -- LHS: ∑' x : ℤ, if x = v then ... else 0
      rw [tsum_ite_eq]
      simp only [hv0, hv255, and_self, ↓reduceIte]
      -- RHS: ∑' a : UInt8, if a.toNat = v then 1/256 else 0
      have hu : ∃ (u : UInt8), (↑u.toNat : ℤ) = v :=
        ⟨⟨v.toNat, by omega⟩, by simp; omega⟩
      obtain ⟨u, hu⟩ := hu
      simp_rw [show ∀ a : UInt8, ((↑a.toNat : ℤ) = v) = (a = u) from fun a => by
        rw [← hu]; exact propext ⟨fun h => UInt8.ext (Nat.cast_inj.mp h), fun h => by rw [h]⟩]
      rw [tsum_ite_eq]
      simp [UInt8.size]
    · -- e' doesn't match any valid UInt8 literal
      push_neg at he
      -- LHS = 0
      have lhs_zero : ∀ x : ℤ, (if Exp.lit (BaseLit.int x) = e' then
          if 0 ≤ x ∧ x ≤ 255 then (↑(Finset.Icc (0 : ℤ) 255).card)⁻¹ else 0 else 0) =
          (0 : ENNReal) := by
        intro x; split_ifs with h1 h2
        · exact absurd h2.2 (not_le.mpr (he x h1 h2.1))
        · rfl
        · rfl
      simp_rw [lhs_zero, tsum_zero]
      -- RHS = 0
      symm; simp only [ENNReal.tsum_eq_zero]
      intro a; split_ifs with h
      · have : (↑a.toNat : ℤ) ≤ 255 := by
          have := a.toNat_lt; omega
        exact absurd this (not_le.mpr (he _ h (Int.natCast_nonneg _)))
      · rfl
  · have : {x : UInt8 | as_expr x = e' ∧ σ = σ'} = ∅ := by ext; simp [hσ]
    simp only [this, Measure.restrict_empty, lintegral_zero_measure]
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
          Set.preimage, Cfg.mk.injEq, hσ]

/-! ## While loop embedding -/

/--
  Translation of `probWhile cond body init`:
    (letrec f x = if (condE x) then (let v := bodyE x; f v) else x) initE

  where `condE`, `bodyE`, `initE` are ProbLang embeddings of `cond`, `body`, `init`.
-/
def probLangWhile (f x v : String) (condE bodyE initE : Exp) : Exp :=
  .app
    (.letrec (.named f) (.named x)
      (.cond condE  -- condition on x
        (probLangBind (.named v) (.app bodyE (.var x)) (.app (.var f) (.var v)))
        (.var x)))
    initE

-- probWhile cond body init : SLang T
-- cond : T → Bool, body : T → SLang T, init : T
-- We need:
--   condE : Exp such that ∀ t, limExec ⟨app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩
--   bodyE : Exp such that ∀ t, IsEmbedding (body t) (app bodyE (as_expr t))
--   initE : Exp such that IsEmbedding (probPure init) initE
--
-- Then: IsEmbedding (probWhile cond body init) (probLangWhile f x v condE bodyE initE)
-- under appropriate freshness conditions on f, x, v.

theorem probLangWhile_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T} {init : T}
    {condE bodyE : Exp} {f x v : String}
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t)))
    (_hfresh : True)  -- TODO: freshness conditions on f, x, v
    :
    IsEmbedding (probWhile cond body init) (probLangWhile f x v condE bodyE (as_expr init)) := by
  sorry

/-! ## Proof of concept: closed equivalence example -/

/-- SLang program: sample two random bytes, compare for equality, return the Bool result. -/
def twoByteEq : SLang Bool := do
  let a ← probUniformByte
  let b ← probUniformByte
  return (a == b)

-- Bool instances for embedding
instance : Countable Bool := inferInstance
instance : MeasurableSpace Bool := ⊤
instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

instance : ProbLangEmbeddable Bool where
  as_expr b := .lit (.bool b)
  as_expr_isVal _ := .lit

/-- ProbLang translation: let a := rand 255 (); let b := rand 255 (); a = b -/
def plTwoByteEq : Exp :=
  probLangBind (.named "a") probLangUniformByte $
    probLangBind (.named "b") probLangUniformByte $
      probLangEq (.var "a") (.var "b")

-- The ProbLang equality operator on embedded UInt8 values computes the same Bool.
-- After substitution, probLangEq (as_expr a) (as_expr b) = .binop .eq (.lit (.int a.toNat)) (.lit (.int b.toNat))
-- which steps to .lit (.bool (decide (a.toNat = b.toNat))), i.e. .lit (.bool (a == b)) = as_expr (a == b).

theorem probLangEq_uint8_isEmbedding (a b : UInt8) :
    IsEmbedding (probPure (a == b)) (probLangEq (as_expr a) (as_expr b)) := by
  intro σ
  show limExec ⟨.binop .eq (.lit (.int a.toNat)) (.lit (.int b.toNat)), σ⟩ = _
  have hnv : ¬ (Exp.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat))).isValue := by
    intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  set result := Exp.lit (.bool (decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat))) with result_def
  have heval : BinOp.eval .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)) = some result := by
    simp [BinOp.eval, result]
  have hred : ∃ ρ, 0 < headStep ⟨.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)), σ⟩ {ρ} :=
    ⟨⟨result, σ⟩, (DetHeadStep.binop .lit .lit heval σ).pos⟩
  rw [primStep_eq_headStep hred]
  show (headStep ⟨.binop .eq (.lit (.int ↑a.toNat)) (.lit (.int ↑b.toNat)), σ⟩).bind limExec = _
  simp only [headStep, Exp.isValM_some' IsVal.lit, heval, Option.unwrapM,
    Measure.dirac_bind Measurable.of_discrete]
  have beq_eq : decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat) = (a == b) := by
    simp only [BaseLit.int.injEq, Nat.cast_inj]
    congr 1; exact propext ⟨UInt8.ext, congrArg _⟩
  show limExec ⟨.lit (.bool (decide (BaseLit.int ↑a.toNat = BaseLit.int ↑b.toNat))), σ⟩ = _
  rw [beq_eq]
  refine Eq.trans ?_ (probLangPure_isEmbedding σ)
  congr

/-- Main theorem: plTwoByteEq is an embedding of twoByteEq. -/
theorem twoByteEq_isEmbedding : IsEmbedding twoByteEq plTwoByteEq := by
  -- twoByteEq = probBind probUniformByte (fun a => probBind probUniformByte (fun b => probPure (a == b)))
  -- plTwoByteEq = probLangBind "a" probLangUniformByte (probLangBind "b" probLangUniformByte (probLangEq (var "a") (var "b")))
  -- Step 1: outer bind — probLangBind_isEmbedding with s1 = probUniformByte, e1 = probLangUniformByte
  unfold twoByteEq plTwoByteEq
  show IsEmbedding (probBind probUniformByte fun a => probBind probUniformByte fun b => probPure (a == b)) _
  apply probLangBind_isEmbedding
  -- h1: IsEmbedding probUniformByte probLangUniformByte
  · exact probLangUniformByte_isEmbedding
  -- h2: ∀ a, IsEmbedding (fun b => probBind probUniformByte (fun b' => probPure (a == b')))
  --                       (subst "a" (as_expr a) (probLangBind "b" probLangUniformByte (probLangEq (var "a") (var "b"))))
  · intro a
    -- After substituting as_expr a for "a":
    --   probLangBind "b" probLangUniformByte (probLangEq (as_expr a) (var "b"))
    -- (since "a" doesn't appear in probLangUniformByte, and substitution in the eq replaces var "a")
    simp [probLangBind, probLangEq, probLangUniformByte, Exp.subst, Exp.subst', Binder.binds]
    -- Goal: IsEmbedding (probBind probUniformByte (fun b => probPure (a == b)))
    --         (.app (.letrec .anon (.named "b") (.binop .eq (as_expr a) (.var "b"))) (.rand (.lit (.int 255)) (.lit .unit)))
    -- This is probLangBind "b" probLangUniformByte (probLangEq (as_expr a) (.var "b"))
    apply probLangBind_isEmbedding
    · exact probLangUniformByte_isEmbedding
    · intro b
      simp [Exp.subst, Exp.subst']
      exact probLangEq_uint8_isEmbedding a b
    · unfold Fresh; exact ⟨trivial, trivial⟩
  -- hfresh: Fresh "a" probLangUniformByte
  · unfold probLangUniformByte Fresh
    exact ⟨trivial, trivial⟩

end EmbedSLang
end
