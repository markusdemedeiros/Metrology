import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.LocallyClosed
import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.DetStep
import Metrology.ProbLang.Exec
import SampCert.SLang
import SampCert.Foundations.While
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
  as_expr_lc : ∀ t, Exp.IsLocallyClosed (as_expr t)
export ProbLangEmbeddable (as_expr as_expr_isVal as_expr_lc)

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
    simp [this, hj]

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
  rw [Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
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

theorem limExec_beta {body v : Exp} {σ : State} (hv : IsVal v) :
    limExec ⟨.app (.lam body) v, σ⟩ = limExec ⟨Exp.open' body v, σ⟩ := by
  have hnv : ¬ (Exp.app (.lam body) v).isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨.app (.lam body) v, σ⟩ {ρ} := by
    refine ⟨⟨Exp.open' body v, σ⟩, ?_⟩; simp [headStep, Exp.isValM_some' hv]
  rw [primStep_eq_headStep hred]
  simp [headStep, Exp.isValM_some' hv, Measure.dirac_bind Measurable.of_discrete]

/-- Generic one-step unfolding for `limExec` at a deterministic head redex. -/
theorem limExec_detHeadStep {ρ ρ' : Cfg} (hnv : ¬ ρ.expr.isValue)
    (h : DetHeadStep ρ ρ') : limExec ρ = limExec ρ' := by
  rw [limExec_not_final hnv, primStep_eq_headStep ⟨ρ', h.pos⟩]
  -- `headStep ρ = dirac ρ'`: mass 1 at ρ', total mass ≤ 1 ⇒ rest vanishes.
  have hother : ∀ c ≠ ρ', (headStep ρ) {c} = 0 := by
    intro c hc
    have hdisj : Disjoint ({ρ'} : Set Cfg) {c} :=
      Set.disjoint_singleton.mpr (Ne.symm hc)
    have hunion : (headStep ρ) ({ρ'} ∪ {c}) = (headStep ρ) {ρ'} + (headStep ρ) {c} :=
      measure_union hdisj (MeasurableSet.singleton c)
    have hsub : (headStep ρ) ({ρ'} ∪ {c}) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans (headStep_univ_le_one ρ)
    rw [hunion, h.det] at hsub
    have : 1 + (headStep ρ) {c} ≤ 1 + 0 := by simpa using hsub
    have hfin : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    exact le_antisymm (ENNReal.le_of_add_le_add_left hfin this) (zero_le _)
  have hdirac : headStep ρ = dirac ρ' := by
    refine Measure.ext_of_singleton fun c => ?_
    by_cases hc : c = ρ'
    · subst hc; rw [h.det]; simp
    · rw [hother c hc]; simp [dirac_apply', hc]
  rw [hdirac, Measure.dirac_bind Measurable.of_discrete]

/-- Generic unfolding of a recursive closure at a value argument.

Given `F = .fix (close (.lam (close body x)) f)` where `body` is LC and free in `f`, `x`,
and a value `u` such that `f ∉ u.fv` and `x ≠ f`, reducing `.app F u` yields
`.app F u  ↪*  subst (subst body x u) f F`. This is the single-iteration unfolding
of any fix-lam-close/close form, and it's the LN-canonical presentation: the caller
supplies the open body (using atoms `f` and `x`) and an LC value, and this lemma
does the two `open_close_subst_lc_gen` commutations implicit in the two beta steps. -/
theorem limExec_app_fix_lam_close {f x : Var}
    {body u : Exp} (hbody : Exp.IsLocallyClosed body)
    (hu : Exp.IsLocallyClosed u) (hu_val : IsVal u) (hfu : f ∉ u.fv)
    {σ : State} :
    let F := .fix (Exp.close (.lam (Exp.close body x)) f)
    limExec ⟨.app F u, σ⟩ =
      limExec ⟨Exp.subst (Exp.subst body x u) f F, σ⟩ := by
  intro F
  -- loop = inner .lam; F = .fix (close loop f).  Both LC:
  have hloop_lc : Exp.IsLocallyClosed (.lam (Exp.close body x)) := by
    refine Exp.IsLocallyClosed.lam (insert x body.fv) _ (fun y hy => ?_)
    have hyx : y ≠ x := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc x y body hbody]
    exact Exp.subst_lc hbody (.fvar _)
  have hF_lc : Exp.IsLocallyClosed F := by
    refine Exp.IsLocallyClosed.fix (insert f (Exp.lam (Exp.close body x)).fv) _ (fun g hg => ?_)
    have hgf : g ≠ f := fun h => hg (by simp [h])
    rw [Exp.open_close_subst_lc f g _ hloop_lc]
    exact Exp.subst_lc hloop_lc (.fvar _)
  -- Step A: app-fix.
  have hnv₁ : ¬ (Exp.app F u).isValue := by intro ⟨h⟩; cases h
  have hstep₁ : DetHeadStep ⟨.app F u, σ⟩
      ⟨.app (Exp.open' (Exp.close (.lam (Exp.close body x)) f) F) u, σ⟩ :=
    DetHeadStep.app_fix hu_val σ
  rw [limExec_detHeadStep hnv₁ hstep₁]
  -- open' (close loop f) F = subst loop f F (both LC).
  rw [Exp.open_close_subst_lc_gen f (.lam (Exp.close body x)) F hloop_lc hF_lc]
  -- Push subst into .lam.
  show limExec ⟨.app (.lam (Exp.subst (Exp.close body x) f F)) u, σ⟩ = _
  -- Step B: app-lam.
  have hnv₂ : ¬ (Exp.app (.lam (Exp.subst (Exp.close body x) f F)) u).isValue := by
    intro ⟨h⟩; cases h
  have hstep₂ : DetHeadStep
      ⟨.app (.lam (Exp.subst (Exp.close body x) f F)) u, σ⟩
      ⟨Exp.open' (Exp.subst (Exp.close body x) f F) u, σ⟩ :=
    DetHeadStep.app_lam hu_val σ
  rw [limExec_detHeadStep hnv₂ hstep₂]
  -- open' (subst (close body x) f F) u
  --   = subst (open' (close body x) u) f F   [since f ∉ u.fv, F LC]
  --   = subst (subst body x u) f F           [by open_close_subst_lc_gen]
  have hu_no_f : Exp.subst u f F = u := Exp.subst_fresh f u F hfu
  rw [show Exp.open' (Exp.subst (Exp.close body x) f F) u =
        Exp.subst (Exp.open' (Exp.close body x) u) f F from by
      rw [Exp.subst_open f F u _ hF_lc, hu_no_f]]
  rw [Exp.open_close_subst_lc_gen x body u hbody hu]

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
def probLangLt (e1 e2 : Exp) : Exp := .binop .lt e1 e2
def probLangDiv (e1 e2 : Exp) : Exp := .binop .div e1 e2
def probLangMod (e1 e2 : Exp) : Exp := .binop .mod e1 e2
def probLangEq (e1 e2 : Exp) : Exp := .binop .eq e1 e2
def probLangNot (e : Exp) : Exp := .unop .neg e
def probLangAnd (e1 e2 : Exp) : Exp := .binop .and e1 e2

-- Control flow
def probLangCond (ec et ef : Exp) : Exp := .cond ec et ef
def probLangApp (ef ea : Exp) : Exp := .app ef ea
/-- Build a lambda from an atom-indexed body: user passes `body` using `fvar x`,
    we close over the atom to produce `lam (close body x)`. -/
def probLangLam (x : Var) (body : Exp) : Exp := .lam (Exp.close body x)

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

/-- LN bind: `let x := e1; body` desugars to `app (lam (close body x)) e1`.
    Caller passes the body open at atom `x`; we close it. -/
def probLangBind (x : Var) (e1 body : Exp) : Exp :=
  .app (.lam (Exp.close body x)) e1

theorem probLangBind_isEmbedding [SLangType T] [ProbLangEmbeddable T] [SLangType U]
    [ProbLangEmbeddable U] {s1 : SLang T} {s2 : T → SLang U} {e1 body : Exp} {x : Var}
    (hbody : Exp.IsLocallyClosed body)
    (h1 : IsEmbedding s1 e1)
    (h2 : ∀ t, IsEmbedding (s2 t) (Exp.subst body x (as_expr t))) :
    IsEmbedding (probBind s1 s2) (probLangBind x e1 body) := by
  intro σ
  rw [probLangBind, limExec_app, h1 σ]
  unfold SLang.spec
  rw [Measure.bind_map .of_discrete .of_discrete, Measure.bind_map .of_discrete .of_discrete]
  -- Rewrite the kernel: limExec_beta puts us at `open' (close body x) (as_expr t)`,
  -- which equals `subst body x (as_expr t)` by `open_close_subst_lc_gen`.
  conv_lhs =>
    arg 2; ext t; simp only [Function.comp]
    rw [limExec_beta (as_expr_isVal t),
        Exp.open_close_subst_lc_gen x body (as_expr t) hbody (as_expr_lc t),
        h2 t σ]
  unfold SLang.spec
  have fuse : ∀ (μ : Measure U),
      (μ.map as_expr).map (fun e => (⟨e, σ⟩ : Cfg)) =
      (fun u => dirac (⟨as_expr u, σ⟩ : Cfg)) ∘ₘ μ := by
    intro μ
    rw [← Measure.bind_dirac_eq_map _ Measurable.of_discrete,
        Measure.bind_map .of_discrete .of_discrete]; rfl
  simp_rw [fuse]
  rw [← SLang.count_bind_probBind,
      Measure.bind_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]

/-! ## Uniform byte embedding -/

instance : Countable UInt8 := ⟨⟨fun u => u.toNat, fun a b h => by ext; exact h⟩⟩
instance : MeasurableSpace UInt8 := ⊤
instance : MeasurableSingletonClass UInt8 := ⟨fun _ => trivial⟩

instance : ProbLangEmbeddable UInt8 where
  as_expr u := .lit (.int u.toNat)
  as_expr_isVal _ := .lit
  as_expr_lc _ := .lit _

-- ProbLang expression: rand 255 ()
-- Cfg.uniform 256 σ samples uniformly from Finset.Ico 0 256 = {0,...,255}
-- (matches UInt8's 256-outcome uniform distribution).
def probLangUniformByte : Exp := .rand (.lit (.int 256)) (.lit .unit)

theorem probLangUniformByte_isEmbedding :
    IsEmbedding probUniformByte probLangUniformByte := by
  intro σ
  have hnv : ¬ probLangUniformByte.isValue := by intro ⟨h⟩; cases h
  rw [limExec_not_final hnv]
  have hred : ∃ ρ, 0 < headStep ⟨probLangUniformByte, σ⟩ {ρ} := by
    rw [show probLangUniformByte = Exp.rand (.lit (.int 256)) (.lit .unit) from rfl]
    simp only [headStep]
    exact ⟨_, Cfg.uniform_singleton_pos_of_mem (v := 0) (by norm_num) (by norm_num) (by norm_num)⟩
  rw [primStep_eq_headStep hred]
  show (headStep ⟨probLangUniformByte, σ⟩).bind limExec = _
  have hhead : headStep ⟨probLangUniformByte, σ⟩ = Cfg.uniform 256 σ := by
    simp [probLangUniformByte, headStep]
  rw [hhead]
  -- limExec ∘ₘ Cfg.uniform 256 σ = Cfg.uniform 256 σ
  -- because Cfg.uniform only produces value configs
  have bind_dirac : limExec ∘ₘ Cfg.uniform 256 σ = Cfg.uniform 256 σ := by
    -- Cfg.uniform 256 σ = PMF.toMeasure(...).map (⟨.lit (.int ·), σ⟩)
    -- These are all value configs, so limExec = dirac on each.
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp only [show (0 : Int) < 256 from by norm_num, dite_true]
    rw [Measure.bind_map .of_discrete .of_discrete]
    -- Goal: (limExec ∘ f) ∘ₘ μ = μ.map f where f v = ⟨.lit (.int v), σ⟩
    -- Since limExec ⟨.lit (.int v), σ⟩ = dirac ⟨.lit (.int v), σ⟩, we get (dirac ∘ f) ∘ₘ μ = μ.map f
    show (limExec ∘ fun v => (⟨.lit (.int v), σ⟩ : Cfg)) ∘ₘ _ = _
    conv_lhs => arg 2; ext v; rw [Function.comp, limExec_of_isVal (.lit (b := .int v))]
    rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [bind_dirac]
  -- Cfg.uniform 256 σ = SLang.spec probUniformByte σ
  unfold SLang.spec
  apply Measure.ext_of_singleton; intro ⟨e', σ'⟩
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      withDensity_apply _ MeasurableSet.of_discrete]
  simp only [Set.preimage, Set.mem_singleton_iff, Cfg.mk.injEq, Set.mem_setOf_eq]
  by_cases hσ : σ = σ'
  · subst hσ; simp only [and_true]
    -- LHS: Cfg.uniform 256 σ {⟨e', σ⟩}
    -- Unfold Cfg.uniform: PMF.uniformOfFinset(.Ico 0 256).toMeasure.map (⟨.lit (.int ·), σ⟩)
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp only [show (0 : Int) < 256 from by norm_num, dite_true]
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    -- LHS: uniformOfFinset(.Ico 0 256).toMeasure {v | ⟨.lit (.int v), σ⟩ = ⟨e', σ⟩}
    --     = uniformOfFinset(.Ico 0 256).toMeasure {v | .lit (.int v) = e'}
    simp only [Set.preimage]
    simp only [Set.mem_singleton_iff, Cfg.mk.injEq, and_true]
    rw [PMF.toMeasure_apply]
    swap; exact MeasurableSet.of_discrete
    conv_rhs => rw [← lintegral_indicator (f := probUniformByte) MeasurableSet.of_discrete, lintegral_count]
    simp only [Set.indicator, Set.mem_setOf_eq, as_expr, SLang.probUniformByte, PMF.uniformOfFinset_apply, Finset.mem_Ico]
    by_cases he : ∃ (v : ℤ), Exp.lit (BaseLit.int v) = e' ∧ 0 ≤ v ∧ v < 256
    · -- e' = .lit (.int v) for some v ∈ [0, 256)
      obtain ⟨v, rfl, hv0, hv256⟩ := he
      simp only [Exp.lit.injEq, BaseLit.int.injEq]
      -- LHS: ∑' x : ℤ, if x = v then ... else 0
      rw [tsum_ite_eq]
      simp only [hv0, hv256, and_self, ↓reduceIte]
      -- RHS: ∑' a : UInt8, if a.toNat = v then 1/256 else 0
      have hu : ∃ (u : UInt8), (↑u.toNat : ℤ) = v :=
        ⟨⟨v.toNat, by omega⟩, by simp; omega⟩
      obtain ⟨u, hu⟩ := hu
      simp_rw [show ∀ a : UInt8, ((↑a.toNat : ℤ) = v) = (a = u) from fun a => by
        rw [← hu]; exact propext ⟨fun h => UInt8.ext (Nat.cast_inj.mp h), fun h => by rw [h]⟩]
      rw [tsum_ite_eq]
      simp [UInt8.size]
    · -- e' doesn't match any valid UInt8 literal
      push Not at he
      -- LHS = 0
      have lhs_zero : ∀ x : ℤ, (if Exp.lit (BaseLit.int x) = e' then
          if 0 ≤ x ∧ x < 256 then (↑(Finset.Ico (0 : ℤ) 256).card)⁻¹ else 0 else 0) =
          (0 : ENNReal) := by
        intro x; split_ifs with h1 h2
        · exact absurd h2.2 (not_lt.mpr (he x h1 h2.1))
        · rfl
        · rfl
      simp_rw [lhs_zero, tsum_zero]
      -- RHS = 0
      symm; simp only [ENNReal.tsum_eq_zero]
      intro a; split_ifs with h
      · have : (↑a.toNat : ℤ) < 256 := by
          have := a.toNat_lt; omega
        exact absurd this (not_lt.mpr (he _ h (Int.natCast_nonneg _)))
      · rfl
  · have : {x : UInt8 | as_expr x = e' ∧ σ = σ'} = ∅ := by ext; simp [hσ]
    simp only [this, Measure.restrict_empty, lintegral_zero_measure]
    unfold Cfg.uniform Int.isPos Option.unwrapM
    simp [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
          Set.preimage, Cfg.mk.injEq, hσ]

/-! ## While loop embedding -/

/--
  LN translation of `probWhile cond body init`:
    `(rec f x = if condE x then let v := bodyE x; f v else x) initE`

  Atoms `f`, `x`, `v` are passed in as `Var`s; the body is built in terms of
  `fvar f / fvar x / fvar v` and then closed at the appropriate boundaries.

  Both `condE` and `bodyE` are function expressions, applied to the loop
  state `fvar x` inside the body. -/
def probLangWhile (f x v : Var) (condE bodyE initE : Exp) : Exp :=
  -- Inner body: if condE x then let v := bodyE x; f v else x
  let body : Exp :=
    .cond (.app condE (.fvar x))
      (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
      (.fvar x)
  -- Wrap in `fix f. lam x. body`: close body over x then over f.
  .app (.fix (Exp.close (.lam (Exp.close body x)) f)) initE

/-- The expression `probLangWhile` unfolds to after one beta-fix + beta-lam, with
    `u` (intended: `as_expr t`) substituted for the loop variable. The recursive
    call still points at the original closed fixpoint `F`. -/
def probLangWhile_unfolded (v : Var) (condE bodyE F u : Exp) : Exp :=
  .cond (.app condE u)
        (.app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE u))
        u

/-- Concrete double-subst simplification on the `probLangWhile` inner body.

    This is the `subst (subst innerBody x u) f F` computation that the generic
    `limExec_app_fix_lam_close` lemma sets up. It's purely symbolic: no limExec,
    no measure theory — just `Exp.subst` reducing through `.cond / .app / .lam /
    close / fvar`. -/
theorem probLangWhile_subst_reduces
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE u F : Exp}
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hfu : f ∉ u.fv) (hvu : v ∉ u.fv)
    (hvF : v ∉ F.fv) :
    Exp.subst
      (Exp.subst
        (.cond (.app condE (.fvar x))
          (.app (.lam (Exp.close (.app (.fvar f) (.fvar v)) v)) (.app bodyE (.fvar x)))
          (.fvar x))
        x u)
      f F
    =
    .cond (.app condE u)
          (.app (.lam (Exp.close (.app F (.fvar v)) v)) (.app bodyE u))
          u := by
  -- Outer .cond: subst pushes in; each subexpression reduces independently.
  show Exp.cond _ _ _ = Exp.cond _ _ _
  congr 1
  · -- Cond discriminant: .app condE (.fvar x)
    show Exp.app _ _ = Exp.app _ _
    congr 1
    · -- condE branch: x ∉ condE.fv and f ∉ condE.fv leave condE untouched.
      show Exp.subst (Exp.subst condE x u) f F = condE
      rw [Exp.subst_fresh x condE u hxcondE, Exp.subst_fresh f condE F hfcondE]
    · -- (fvar x → u) then subst f F = u  (since f ∉ u.fv)
      show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
      simp only [Exp.subst]
      exact Exp.subst_fresh f u F hfu
  · -- Inner .lam (close (.app (fvar f) (fvar v)) v) ... after subst x u then f F:
    -- subst at x: fvar f ≠ x, fvar v ≠ x, so .app (fvar f) (fvar v) unchanged.
    --   But close is at v, so we're doing subst (closeRec 0 v (.app (fvar f) (fvar v))) x u
    --   = closeRec 0 v (subst (.app (fvar f) (fvar v)) x u)  [subst_closeRec, x ≠ v, v ∉ u.fv]
    --   = closeRec 0 v (.app (fvar f) (fvar v))  [since x ≠ f, x ≠ v]
    -- Then subst at f: push inside close; fvar f → F.
    --   subst (closeRec 0 v (.app (fvar f) (fvar v))) f F
    --   = closeRec 0 v (subst (.app (fvar f) (fvar v)) f F)  [subst_closeRec, f ≠ v, v ∉ F.fv]
    --   = closeRec 0 v (.app F (fvar v))
    show Exp.app _ _ = Exp.app _ _
    congr 1
    · -- the .lam (close (.app (fvar f) (fvar v)) v) under subst x u then subst f F
      show Exp.lam _ = Exp.lam _
      congr 1
      show Exp.subst (Exp.subst (Exp.close _ v) x u) f F = Exp.close _ v
      simp only [Exp.close]
      rw [Exp.subst_closeRec x v u 0 _ hxv hvu]
      rw [Exp.subst_closeRec f v F 0 _ hfv hvF]
      congr 1
      simp [Exp.subst, Ne.symm hfx, hxv, hfv]
    · -- .app bodyE (.fvar x)
      show Exp.app _ _ = Exp.app _ _
      congr 1
      · show Exp.subst (Exp.subst bodyE x u) f F = bodyE
        rw [Exp.subst_fresh x bodyE u hxbodyE, Exp.subst_fresh f bodyE F hfbodyE]
      · show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
        simp only [Exp.subst]
        exact Exp.subst_fresh f u F hfu
  · -- "fvar x → u" on the else-branch of the cond
    show Exp.subst (Exp.subst (Exp.fvar x) x u) f F = u
    simp only [Exp.subst]
    exact Exp.subst_fresh f u F hfu

/-- One-iteration unfolding of `probLangWhile` at `as_expr t`.

    Combines the generic `limExec_app_fix_lam_close` with the concrete
    `probLangWhile_subst_reduces` simplification to turn the closed loop
    expression into its opened form with `as_expr t` substituted. -/
theorem limExec_probLangWhile_app [SLangType T] [ProbLangEmbeddable T]
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (_hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (t : T) {σ : State} :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    limExec ⟨.app F (as_expr t), σ⟩
      = limExec ⟨probLangWhile_unfolded v condE bodyE F (as_expr t), σ⟩ := by
  intro F
  -- innerBody: the open body at atoms f, x, v.
  set innerBody : Exp :=
    .cond (.app condE (.fvar x))
          (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
          (.fvar x) with hinner_def
  -- Local-closure of innerBody.
  have hfv_v : (Exp.app (.fvar f) (.fvar v) : Exp).IsLocallyClosed :=
    .app (.fvar _) (.fvar _)
  have hinner_lc : Exp.IsLocallyClosed innerBody := by
    refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
    -- probLangBind v e1 body = .app (.lam (close body v)) e1
    refine .app ?_ (.app hbodyE_lc (.fvar _))
    refine Exp.IsLocallyClosed.lam (insert v (Exp.app (.fvar f) (.fvar v)).fv) _ (fun y hy => ?_)
    have hyv : y ≠ v := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc v y _ hfv_v]
    exact Exp.subst_lc hfv_v (.fvar _)
  -- v ∉ innerBody.fv: the probLangBind closes v off, and v ∉ condE.fv ∪ bodyE.fv,
  -- v ≠ f, v ≠ x are direct hypotheses.
  have hv_inner : v ∉ innerBody.fv := by
    show v ∉ _
    simp only [hinner_def, probLangBind, Exp.fv, Finset.mem_union, Finset.mem_singleton,
      not_or]
    refine ⟨⟨⟨hvcondE, fun h => hxv h.symm⟩, ?_, hvbodyE, fun h => hxv h.symm⟩, fun h => hxv h.symm⟩
    -- v ∉ (close (.app (fvar f) (fvar v)) v).fv by close_var_not_fvar.
    exact Exp.close_var_not_fvar_rec v 0 _
  -- v ∉ F.fv via close_preserve_not_fvar.
  have hvF : v ∉ F.fv := by
    -- F = .fix (close (.lam (close innerBody x)) f)
    -- (.fix e).fv = e.fv; (.lam e).fv = e.fv
    show v ∉ Exp.fv _
    have h1 : v ∉ (Exp.close innerBody x).fv :=
      Exp.close_preserve_not_fvar _ hv_inner
    -- .lam has same fv as body
    have h2 : v ∉ (Exp.lam (Exp.close innerBody x)).fv := by
      simp only [Exp.fv]; exact h1
    exact Exp.close_preserve_not_fvar _ h2
  -- Apply generic fix-unfolding.
  rw [limExec_app_fix_lam_close (f := f) (x := x) hinner_lc
        (as_expr_lc t) (as_expr_isVal t) (hfas t)]
  -- Now the double subst simplifies via probLangWhile_subst_reduces.
  have hsubst : Exp.subst (Exp.subst innerBody x (as_expr t)) f F =
      probLangWhile_unfolded v condE bodyE F (as_expr t) := by
    rw [hinner_def]
    simp only [probLangBind, probLangWhile_unfolded]
    exact probLangWhile_subst_reduces hfx hfv hxv
      hfcondE hfbodyE hxcondE hxbodyE (hfas t) (hvas t) hvF
  rw [hsubst]

/-- Recurrence for `limExec ⟨.app F (as_expr t), σ⟩`: mirrors `probWhileFunctional`.

    Uses the value-indexed form `(count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)`
    which is better-behaved than `(SLang.spec …).bind …` because every sampled value is
    already in `as_expr`-form (no need for beta-lam reduction pointwise).

    On `cond t = false`, terminates immediately at `as_expr t`.
    On `cond t = true`, binds through one iteration of `body t`, then recurses. -/
theorem limExec_probLangWhile_recurrence [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T}
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t)))
    (t : T) {σ : State} :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    limExec ⟨.app F (as_expr t), σ⟩ =
      (if cond t then
        (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
       else dirac ⟨as_expr t, σ⟩) := by
  intro F
  -- Upfront: LC of innerBody, loopLam, and F (needed twice: in
  -- limExec_app_fix_lam_close's preamble, and again for the beta-lam in the true-branch).
  set innerBody : Exp :=
    .cond (.app condE (.fvar x))
          (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
          (.fvar x) with hinner_def
  have hfv_v : (Exp.app (.fvar f) (.fvar v) : Exp).IsLocallyClosed :=
    .app (.fvar _) (.fvar _)
  have hinner_lc : Exp.IsLocallyClosed innerBody := by
    refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
    refine .app ?_ (.app hbodyE_lc (.fvar _))
    refine Exp.IsLocallyClosed.lam (insert v (Exp.app (.fvar f) (.fvar v)).fv) _ (fun y hy => ?_)
    have hyv : y ≠ v := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc v y _ hfv_v]
    exact Exp.subst_lc hfv_v (.fvar _)
  have hloopLam_lc : Exp.IsLocallyClosed (.lam (Exp.close innerBody x)) := by
    refine Exp.IsLocallyClosed.lam (insert x innerBody.fv) _ (fun y hy => ?_)
    have hyx : y ≠ x := fun h => hy (by simp [h])
    rw [Exp.open_close_subst_lc x y innerBody hinner_lc]
    exact Exp.subst_lc hinner_lc (.fvar _)
  have hF_lc : Exp.IsLocallyClosed F := by
    refine Exp.IsLocallyClosed.fix (insert f (Exp.lam (Exp.close innerBody x)).fv) _ (fun g hg => ?_)
    have hgf : g ≠ f := fun h => hg (by simp [h])
    rw [Exp.open_close_subst_lc f g _ hloopLam_lc]
    exact Exp.subst_lc hloopLam_lc (.fvar _)
  have hv_inner : v ∉ innerBody.fv := by
    show v ∉ _
    simp only [hinner_def, probLangBind, Exp.fv, Finset.mem_union, Finset.mem_singleton,
      not_or]
    refine ⟨⟨⟨hvcondE, fun h => hxv h.symm⟩, ?_, hvbodyE, fun h => hxv h.symm⟩, fun h => hxv h.symm⟩
    exact Exp.close_var_not_fvar_rec v 0 _
  have hvF : v ∉ F.fv := by
    show v ∉ Exp.fv _
    have h1 : v ∉ (Exp.close innerBody x).fv :=
      Exp.close_preserve_not_fvar _ hv_inner
    have h2 : v ∉ (Exp.lam (Exp.close innerBody x)).fv := by
      simp only [Exp.fv]; exact h1
    exact Exp.close_preserve_not_fvar _ h2
  -- Step 1: use one-iteration unfolding.
  rw [limExec_probLangWhile_app hfx hfv hxv hcondE_lc hbodyE_lc
        hfcondE hfbodyE hxcondE hxbodyE hvcondE hvbodyE hfas hxas hvas t]
  simp only [probLangWhile_unfolded]
  -- Step 2: evaluate the cond discriminant via limExec_fill_item with Ki = .condC.
  rw [show (Exp.cond (Exp.app condE (as_expr t))
              (Exp.app (Exp.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
              (as_expr t) : Exp)
        = EctxItem.fillItem (.condC _ _) (Exp.app condE (as_expr t)) from rfl,
      limExec_fill_item, hcond t σ, Measure.dirac_bind Measurable.of_discrete]
  simp only [EctxItem.fillItem]
  -- Step 3: split on cond t and apply DetHeadStep.cond_{true,false}.
  by_cases hct : cond t = true
  · rw [hct]
    simp only [if_true]
    have hnv : ¬ (Exp.cond (.lit (.bool true))
        (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
        (as_expr t)).isValue := by intro ⟨h⟩; cases h
    rw [limExec_detHeadStep hnv (DetHeadStep.cond_true _ _ σ)]
    -- Step 4: evaluate .app bodyE (as_expr t) via limExec_fill_item with Ki = .appR.
    rw [show (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)) : Exp)
          = EctxItem.fillItem (.appR _) (Exp.app bodyE (as_expr t)) from rfl,
        limExec_fill_item]
    simp only [EctxItem.fillItem]
    rw [hbody t σ]
    -- Step 5: unfold SLang.spec as (count (body t)).map as_expr |>.map (⟨·, σ⟩) and push
    -- the bind through both maps.
    unfold SLang.spec
    rw [Measure.bind_map Measurable.of_discrete Measurable.of_discrete]
    rw [Measure.bind_map Measurable.of_discrete Measurable.of_discrete]
    -- Now: (count (body t)).bind (fun t' => limExec ⟨.app (.lam (close (.app F (fvar v)) v)) (as_expr t'), σ⟩)
    -- which should equal: (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
    congr 1
    funext t'
    -- Goal: limExec ⟨.app (.lam (close (.app F (fvar v)) v)) (as_expr t'), σ⟩
    --     = limExec ⟨.app F (as_expr t'), σ⟩
    simp only [Function.comp]
    rw [limExec_beta (as_expr_isVal t')]
    congr 1
    -- Goal: open' (close (.app F (fvar v)) v) (as_expr t') = .app F (as_expr t')
    rw [Exp.open_close_subst_lc_gen v _ (as_expr t') (.app hF_lc (.fvar _)) (as_expr_lc t')]
    -- subst (.app F (fvar v)) v (as_expr t') = .app (subst F v (as_expr t')) (as_expr t')
    -- subst F v (as_expr t') = F since v ∉ F.fv.
    simp only [Exp.subst]
    rw [Exp.subst_fresh v F (as_expr t') hvF]
    simp
  · have hct' : cond t = false := by
      cases hc : cond t with
      | true => exact absurd hc hct
      | false => rfl
    simp only [hct']
    have hnv : ¬ (Exp.cond (.lit (.bool false))
        (Exp.app (.lam (Exp.close (Exp.app F (.fvar v)) v)) (Exp.app bodyE (as_expr t)))
        (as_expr t)).isValue := by intro ⟨h⟩; cases h
    rw [limExec_detHeadStep hnv (DetHeadStep.cond_false _ _ σ)]
    exact limExec_of_isVal (as_expr_isVal t)

/-- Forward direction: finite unrollings of `probWhile` are dominated pointwise
    by `limExec` of the closed form. -/
theorem SLang_spec_probWhileCut_le [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T}
    {f x v : Var} (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    {condE bodyE : Exp}
    (hcondE_lc : Exp.IsLocallyClosed condE) (hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (hfcondE : f ∉ condE.fv) (hfbodyE : f ∉ bodyE.fv)
    (hxcondE : x ∉ condE.fv) (hxbodyE : x ∉ bodyE.fv)
    (hvcondE : v ∉ condE.fv) (hvbodyE : v ∉ bodyE.fv)
    (hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t)))
    (k : Nat) (t : T) (σ : State) :
    let F : Exp := .fix (Exp.close (.lam (Exp.close
      (.cond (.app condE (.fvar x))
        (probLangBind v (.app bodyE (.fvar x)) (.app (.fvar f) (.fvar v)))
        (.fvar x)) x)) f)
    SLang.spec (probWhileCut cond body k t) σ ≤ limExec ⟨.app F (as_expr t), σ⟩ := by
  intro F
  induction k generalizing t with
  | zero =>
    -- probWhileCut 0 = probZero = (fun _ => 0), so SLang.spec is 0.
    have hzero : (probWhileCut cond body 0 t : SLang T) = (fun _ => 0) := rfl
    show SLang.spec (probWhileCut cond body 0 t) σ ≤ _
    rw [hzero]
    have : SLang.spec (fun _ : T => (0 : ENNReal)) σ = (0 : Measure Cfg) := by
      unfold SLang.spec _root_.count
      simp
    rw [this]
    exact bot_le
  | succ k ih =>
    -- probWhileCut (k+1) = probWhileFunctional body (probWhileCut k).
    show SLang.spec (probWhileFunctional cond body (probWhileCut cond body k) t) σ ≤ _
    rw [limExec_probLangWhile_recurrence hfx hfv hxv hcondE_lc hbodyE_lc
          hfcondE hfbodyE hxcondE hxbodyE hvcondE hvbodyE hfas hxas hvas
          hcond hbody t]
    unfold probWhileFunctional
    by_cases hct : cond t = true
    · rw [hct]; simp only [if_true]
      show SLang.spec (probBind (body t) (probWhileCut cond body k)) σ ≤ _
      -- Rewrite LHS: SLang.spec s = (count s).map as_expr .map (⟨·, σ⟩)
      -- count (body t >>= wh) = (count ∘ wh) ∘ₘ (count (body t))   [SLang.count_bind_probBind]
      unfold SLang.spec
      rw [← SLang.count_bind_probBind]
      -- Now ((count (body t) >>= ...).map as_expr .map (⟨·, σ⟩)).
      -- Push .map into bind twice using Measure.bind_map_comm.
      rw [Measure.bind_map_comm, Measure.bind_map_comm]
      -- Goal: (count (body t)).bind (fun t' => count (probWhileCut cond body k t') |>.map as_expr |>.map (⟨·, σ⟩))
      --       ≤ (count (body t)).bind (fun t' => limExec ⟨.app F (as_expr t'), σ⟩)
      -- This is bind monotonicity in the kernel, applied pointwise via IH.
      exact Measure.bind_mono_right _ _ _ (fun t' => ih t')
    · have hct' : cond t = false := by
        cases hc : cond t with
        | true => exact absurd hc hct
        | false => rfl
      simp only [hct']
      -- LHS: SLang.spec (probPure t) σ = dirac ⟨as_expr t, σ⟩. RHS: dirac ⟨as_expr t, σ⟩.
      refine le_of_eq ?_
      show SLang.spec (SLang.probPure t) σ = _
      unfold SLang.spec
      -- count (probPure t) = dirac t
      have hc_eq : _root_.count (SLang.probPure t) = (dirac t : Measure T) := by
        refine Measure.ext_of_singleton fun u => ?_
        rw [_root_.count_singleton]
        unfold SLang.probPure
        rw [dirac_apply' _ (MeasurableSet.singleton u)]
        by_cases hut : u = t
        · subst hut; simp
        · simp only [Set.indicator_apply, Set.mem_singleton_iff,
                     show t ≠ u from fun h => hut h.symm, ↑reduceIte]
          simp [hut]
      simp only [show (false = true) = False from by simp, if_false]
      rw [hc_eq]
      rw [map_dirac' Measurable.of_discrete, map_dirac' Measurable.of_discrete]

/-- Top-level embedding of `probWhile`.

    Strategy: combine the forward direction (`SLang_spec_probWhileCut_le`) with a
    backward direction via fuel induction:
    - **Forward (≥)**: `SLang.spec (probWhileCut k init) σ ≤ limExec ⟨.app F (as_expr init), σ⟩`
      for each `k`. Taking iSup_k gives `SLang.spec (probWhile init) ≤ limExec ⟨.app F (as_expr init), σ⟩`.
      Needs: iSup pushes through `(count _).map as_expr .map (⟨·, σ⟩)`.
    - **Backward (≤)**: `execN n ⟨.app F (as_expr init), σ⟩ ≤ SLang.spec (probWhile init) σ`
      pointwise. Taking iSup_n gives `limExec ≤ SLang.spec (probWhile init)`.
      Hard part: relate `n` primSteps to some finite number of `probWhileCut` iterations.

    Current state: forward direction sub-lemma proven; backward direction is the gap. -/
theorem probLangWhile_isEmbedding [SLangType T] [ProbLangEmbeddable T]
    {cond : T → Bool} {body : T → SLang T} {init : T}
    {condE bodyE : Exp} {f x v : Var}
    (_hfx : f ≠ x) (_hfv : f ≠ v) (_hxv : x ≠ v)
    (_hcondE_lc : Exp.IsLocallyClosed condE) (_hbodyE_lc : Exp.IsLocallyClosed bodyE)
    (_hfcondE : f ∉ condE.fv) (_hfbodyE : f ∉ bodyE.fv)
    (_hxcondE : x ∉ condE.fv) (_hxbodyE : x ∉ bodyE.fv)
    (_hvcondE : v ∉ condE.fv) (_hvbodyE : v ∉ bodyE.fv)
    (_hfas : ∀ (t : T), f ∉ (as_expr t).fv)
    (_hxas : ∀ (t : T), x ∉ (as_expr t).fv)
    (_hvas : ∀ (t : T), v ∉ (as_expr t).fv)
    (_hcond : ∀ t σ, limExec ⟨.app condE (as_expr t), σ⟩ = dirac ⟨.lit (.bool (cond t)), σ⟩)
    (_hbody : ∀ t, IsEmbedding (body t) (.app bodyE (as_expr t))) :
    IsEmbedding (probWhile cond body init) (probLangWhile f x v condE bodyE (as_expr init)) := by
  -- The forward direction (≥) is very close — see the attempted proof below (commented
  -- out). It reduces to a tsum/iSup swap for ENNReal-valued monotone sequences, which
  -- is supplied by `lintegral_iSup` via the `lintegral_count` identity. The names
  -- `Set.indicator_of_notMem` (camelCase) and `ENNReal.tsum_iSup` (or its variant via
  -- `lintegral_iSup`) need to be located/adapted. The backward direction (≤) requires
  -- fuel-induction on `execN n`.
  --
  -- Commented-out forward-direction attempt (compiles under the assumption of a
  -- working `ENNReal.tsum_iSup` / `lintegral_iSup`-based monotone-convergence swap):
  --
  -- intro σ
  -- refine le_antisymm ?_ ?_
  -- · -- BACKWARD
  --   sorry
  -- · -- FORWARD
  --   intro S
  --   have h_le_iSup : ((count (probWhile cond body init)).map as_expr).map (⟨·, σ⟩) S
  --       ≤ ⨆ k, ((count (probWhileCut cond body k init)).map as_expr).map (⟨·, σ⟩) S := by
  --     have expand : ∀ (s : SLang T),
  --         ((count s).map as_expr).map (⟨·, σ⟩) S =
  --         ∑' x, s x * (S.indicator 1 ⟨as_expr x, σ⟩) := by
  --       intro s
  --       rw [Measure.map_apply Measurable.of_discrete .of_discrete,
  --           Measure.map_apply Measurable.of_discrete .of_discrete,
  --           show (_root_.count s) = Measure.count.withDensity s from rfl,
  --           withDensity_apply _ .of_discrete,
  --           ← lintegral_indicator .of_discrete, lintegral_count]
  --       congr 1; funext x
  --       by_cases hx : ⟨as_expr x, σ⟩ ∈ S
  --       · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one,
  --                    Set.indicator_of_mem, Set.mem_preimage, hx]
  --       · simp only [Set.indicator_of_notMem hx, mul_zero,
  --                    Set.indicator_of_notMem, Set.mem_preimage, hx]
  --     rw [expand (probWhile cond body init)]
  --     have rhs_eq : (⨆ k, ((count (probWhileCut cond body k init)).map as_expr).map (⟨·, σ⟩) S) =
  --         ⨆ k, ∑' x, probWhileCut cond body k init x * S.indicator 1 ⟨as_expr x, σ⟩ := by
  --       congr 1; funext k; exact expand (probWhileCut cond body k init)
  --     rw [rhs_eq]
  --     show ∑' x, probWhile cond body init x * S.indicator 1 ⟨as_expr x, σ⟩ ≤ _
  --     have probWhile_iSup : ∀ x, probWhile cond body init x = ⨆ k, probWhileCut cond body k init x :=
  --       fun _ => rfl
  --     simp_rw [probWhile_iSup, ENNReal.iSup_mul]
  --     have hmono : ∀ x, Monotone (fun k => probWhileCut cond body k init x *
  --         S.indicator 1 ⟨as_expr x, σ⟩) := fun x m n hmn =>
  --       mul_le_mul' (SLang.probWhileCut_monotonic cond body init x hmn) le_rfl
  --     rw [ENNReal.tsum_iSup (fun k _ l hkl => hmono _ hkl)]  -- needs correct lemma name
  --   refine h_le_iSup.trans ?_
  --   refine iSup_le (fun k => ?_)
  --   exact SLang_spec_probWhileCut_le _hfx _hfv _hxv _hcondE_lc _hbodyE_lc
  --     _hfcondE _hfbodyE _hxcondE _hxbodyE _hvcondE _hvbodyE _hfas _hxas _hvas _hcond _hbody
  --     k init σ S
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
  as_expr_lc _ := .lit _

/-- ProbLang translation: `let a := rand 255 (); let b := rand 255 (); a = b`. -/
def plTwoByteEq : Exp :=
  probLangBind "a" probLangUniformByte $
    probLangBind "b" probLangUniformByte $
      probLangEq (.fvar "a") (.fvar "b")

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
  unfold twoByteEq plTwoByteEq
  show IsEmbedding (probBind probUniformByte fun a => probBind probUniformByte fun b => probPure (a == b)) _
  -- Outer bind: `let a := byte; <body>`
  apply probLangBind_isEmbedding
  · -- hbody : LC of the outer body = `probLangBind 1 byte (eq (fvar 0) (fvar 1))`
    -- This is `app (lam (close (eq (fvar 0) (fvar 1)) 1)) byte`. All literals + binops + lam → LC.
    unfold probLangBind probLangUniformByte probLangEq
    refine .app (.lam ∅ _ (fun _ _ => ?_)) (.rand (.lit _) (.lit _))
    -- After opening the lam at fresh y: open' (close (eq (fvar 0) (fvar 1)) 1) (fvar y)
    -- = subst (eq (fvar 0) (fvar 1)) 1 (fvar y) by open_close_subst_lc.
    -- = eq (fvar 0) (fvar y). Both args are fvar → LC.
    rw [Exp.open_close_subst_lc]
    · exact .binop _ (.fvar _) (.fvar _)
    · exact .binop _ (.fvar _) (.fvar _)
  · -- h1 : IsEmbedding probUniformByte probLangUniformByte
    exact probLangUniformByte_isEmbedding
  · -- h2 : ∀ a, IsEmbedding (...) (subst <body> "a" (as_expr a))
    intro a
    have hgoal : Exp.subst (probLangBind "b" probLangUniformByte
                              (probLangEq (.fvar "a") (.fvar "b"))) "a" (as_expr a)
        = probLangBind "b" probLangUniformByte (probLangEq (as_expr a) (.fvar "b")) := by
      unfold probLangBind probLangUniformByte probLangEq
      simp only [Exp.subst, Exp.close, Exp.closeRec]
      rfl
    rw [hgoal]
    apply probLangBind_isEmbedding
    · exact .binop _ (as_expr_lc a) (.fvar _)
    · exact probLangUniformByte_isEmbedding
    · intro b
      have ha_subst : Exp.subst (as_expr a) "b" (as_expr b) = as_expr a := by
        apply Exp.subst_fresh
        intro h; simp [Exp.fv] at h
      have hgoal2 : Exp.subst (probLangEq (as_expr a) (.fvar "b")) "b" (as_expr b)
          = probLangEq (as_expr a) (as_expr b) := by
        unfold probLangEq
        simp only [Exp.subst]
        rfl
      rw [hgoal2]
      exact probLangEq_uint8_isEmbedding a b

end EmbedSLang
end
