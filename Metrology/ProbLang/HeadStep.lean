module

public import Metrology.ProbLang.CoreMeasures
public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Discrete
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

noncomputable section

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

variable {rT : Type _} [ProbLangℝ rT]

def Option.unwrapM {α : Type _} [MeasurableSpace β] (f : α → Measure β) : Option α → Measure β
| some v => f v
| none => 0

@[simp]
def Exp.asValM [MeasurableSpace T] (e : Exp rT) (f : Val rT → Measure T) : Measure T :=
  match e.toVal? with | none => 0 | some v => f v

def Exp.isValM [MeasurableSpace T] (e : Exp rT) (m : Measure T) : Measure T :=
  if e.isValue then m else 0

@[simp] theorem Exp.isValM_some [MeasurableSpace T] {e : Exp α} {m : Measure T} (He : e.isValue) :
    e.isValM m = m := if_pos He

theorem Exp.isValM_some' [MeasurableSpace T] {e : Exp α} {m : Measure T} (w : IsVal e) :
    e.isValM m = m := isValM_some w.toIsValue

@[simp] theorem Exp.isValM_none [MeasurableSpace T] {e : Exp α} {m : Measure T} (He : ¬ e.isValue) :
    e.isValM m = 0 := if_neg He

def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none


/-- Uniform distribution over `⟨.lit (.int n), σ⟩` for `n ∈ {0, 1, …, z−1}` when `0 < z`.
Constant sentinel value -1 when `z ≤ 0` -/
def Cfg.uniform (z : Int) (σ : State rT) : Measure (Cfg rT) :=
  match z.isPos with
  | some ⟨z, Hz⟩ =>
    PMF.uniformOfFinset (.Ico 0 z) (Finset.nonempty_Ico.mpr Hz)
      |>.toMeasure.map (⟨.lit <| .int ·, σ⟩)
  | none => dirac ⟨.lit (.int (-1)), σ⟩

/-- Continuous uniform distribution over `⟨.lit (.real r), σ⟩` for `r` drawn from the
unit interval `[0,1]` (the `ProbLangℝ.unifUnit` probability measure on `rT`). -/
def Cfg.uniformReal (σ : State rT) : Measure (Cfg rT) :=
  (ProbLangℝ.unifUnit (T := rT)).map (⟨.lit <| .real ·, σ⟩)

-- TODO: Do we need these value checks? Finding the redex, and enforcing evalutation
-- order, should be governed by the reduction context.
def headStep : Cfg rT → Measure (Cfg rT)
| ⟨.app (.lam e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨Exp.open' e1 e2, σ⟩
| ⟨.app (.fix e1) e2, σ⟩ =>
  e2.isValM <|
  dirac ⟨Exp.app (Exp.open' e1 (.fix e1)) e2, σ⟩
| ⟨.unop op e, σ⟩ =>
  e.isValM <|
  (op.eval e).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.binop op e1 e2, σ⟩ =>
  e1.isValM <|
  e2.isValM <|
  (op.eval e1 e2).unwrapM <|
  (dirac ⟨·, σ⟩)
| ⟨.cond (.lit (.bool true)) et _, σ⟩ => dirac ⟨et, σ⟩
| ⟨.cond (.lit (.bool false)) _ ef, σ⟩ => dirac ⟨ef, σ⟩
| ⟨.fst (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e1, σ⟩)
| ⟨.snd (.pair e1 e2), σ⟩ => e1.isValM <| e2.isValM <| (dirac ⟨e2, σ⟩)
| ⟨.case (.inl e) el _, σ⟩ => e.isValM <| (dirac ⟨el.app e, σ⟩)
| ⟨.case (.inr e) _ er, σ⟩ => e.isValM <| (dirac ⟨er.app e, σ⟩)
| ⟨.alloc ed, σ⟩ =>
  ed.asValM fun vd =>
  let ℓ := σ.heap.fresh
  dirac ⟨.lit <| .loc ℓ, σ.update_heap fun t => t.insert ℓ vd⟩
| ⟨.load (.lit (.loc ℓ)), σ⟩ =>
  match σ.heap[ℓ]? with | none => 0 | some v => (dirac ⟨.ofVal v, σ⟩)
| ⟨.store (.lit (.loc ℓ)) e, σ⟩ =>
  e.asValM fun v =>
  match σ.heap[ℓ]? with | none => 0 | some _ => dirac ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
| ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ => Cfg.uniform z σ
| ⟨.tape (.lit (.int z)), σ⟩ =>
  let α := σ.tapes.fresh
  dirac ⟨.lit <| .lbl α, σ.update_tapes fun t => t.insert α (.empty z)⟩
| ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ =>
  match σ.tapes[α]? with
  | none => 0
  | some ⟨M, ns⟩ =>
    if M = z
      then
        match ns with
        | [] => Cfg.uniform z σ
        | n :: ns => dirac ⟨.lit <| .int n, σ.update_tapes fun t => t.insert α ⟨M, ns⟩⟩
      else Cfg.uniform z σ
| ⟨.scrut e p, σ⟩ =>
  e.isValM <|
  match Pat.tryMatch p e with
  | some bindings => dirac ⟨.inl bindings, σ⟩
  | none => dirac ⟨.inr (.lit .unit), σ⟩
| ⟨.urand, σ⟩ => Cfg.uniformReal σ
| _ => 0

elab "rename_goal" name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.setUserName name.getId

/-- Split the headStep cases, but with informative goal names. -/
macro "head_case_names" : tactic =>
  `(tactic| (
    unfold headStep
    split
    on_goal 1  => rename_goal beta.lam
    on_goal 2  => rename_goal beta.fix
    on_goal 3  => rename_goal unop
    on_goal 4  => rename_goal binop
    on_goal 5  => rename_goal cond.true
    on_goal 6  => rename_goal cond.false
    on_goal 7  => rename_goal fst
    on_goal 8  => rename_goal snd
    on_goal 9  => rename_goal case.left
    on_goal 10 => rename_goal case.right
    on_goal 11 => rename_goal alloc
    on_goal 12 => rename_goal load
    on_goal 13 => rename_goal store
    on_goal 14 => rename_goal rand.plain
    on_goal 15 => rename_goal tape
    on_goal 16 => rename_goal rand.tape
    on_goal 17 => rename_goal scrut
    on_goal 18 => rename_goal urand
    on_goal 19 => rename_goal default
  ))

/-- Decompose the Cfg equality hypothesis left by `split` on `headStep`, then substitute. -/
macro "head_subst" : tactic =>
  `(tactic| (rename_i h_eq
             have ⟨Heq1, Heq2⟩ := (Cfg.mk.injEq ..) ▸ h_eq
             subst_eqs))

/-- Unfold `isValM`, split into redex/no_redex, and name goals.
    Goal order after `split` on `if`: goal 1 = true (redex), goal 2 = false (no_redex). -/
macro "head_split_isValM" redex:ident no_redex:ident : tactic =>
  `(tactic| (unfold Exp.isValM; split
             on_goal 2 => rename_goal $no_redex
             on_goal 1 => rename_goal $redex))

/-- Unfold `asValM`, split into no_redex/redex, and name goals.
    Goal order after `split` on `match toVal?`: goal 1 = none (no_redex), goal 2 = some (redex). -/
macro "head_split_asValM" no_redex:ident redex:ident : tactic =>
  `(tactic| (unfold Exp.asValM; split
             on_goal 1 => rename_goal $no_redex
             on_goal 2 => rename_goal $redex))

/-- Split a binary match (e.g. heap lookup) and name the two goals. -/
macro "head_split2" goal1:ident goal2:ident : tactic =>
  `(tactic| (split
             on_goal 1 => rename_goal $goal1
             on_goal 2 => rename_goal $goal2))

macro "head_case" : tactic =>
  `(tactic| (
    head_case_names
    case' rand.tape =>
      head_subst
      head_split2 rand.tape.unalloc rand_tape_alloc
      case' rand_tape_alloc =>
        split
        on_goal 2 => rename_goal rand.tape.mismatch
        on_goal 1 =>
          subst_eqs
          head_split2 rand.tape.empty rand.tape.deterministic
    case' tape       => head_subst
    case' rand.plain => head_subst
    case' store =>
      head_subst
      unfold Exp.asValM; split
      on_goal 1 => rename_goal store.no_redex
      on_goal 2 => head_split2 store.segfault store.redex
    case' load =>
      head_subst
      head_split2 load.segfault load.redex
    case' alloc =>
      head_subst
      head_split_asValM alloc.no_redex alloc.redex
    case' case.right =>
      head_subst
      head_split_isValM case.right.redex case.right.no_redex
    case' case.left =>
      head_subst
      head_split_isValM case.left.redex case.left.no_redex
    case' snd =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal snd.no_redex_1
      on_goal 1 => head_split2 snd.redex snd.no_redex_2
    case' fst =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal fst.no_redex_1
      on_goal 1 => head_split2 fst.redex fst.no_redex_2
    case' cond.false => head_subst
    case' cond.true  => head_subst
    case' binop =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal binop.no_redex_1
      on_goal 1 => head_split2 binop.redex binop.no_redex_2
    case' unop =>
      head_subst
      head_split_isValM unop.redex unop.no_redex
    case' scrut =>
      head_subst
      unfold Exp.isValM; split
      on_goal 2 => rename_goal scrut_no_redex
      on_goal 1 =>
        head_split2 scrut_success scrut_failure
    case' beta.lam =>
      head_subst
      head_split_isValM beta.lam.redex beta.lam.no_redex
    case' beta.fix =>
      head_subst
      head_split_isValM beta.fix.redex beta.fix.no_redex
  ))


abbrev HeadReducible [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  headStep ⟨e, σ⟩ ≠ 0

/-! ### Measurability for arbitrary measurable `rT`.

These stubs replace the discrete-`rT` `.of_discrete` shortcuts above with genuine
measurability statements that hold for any `[ProbLangℝ rT]`. -/

/-- `Option.unwrapM f` is measurable in its `Option α` argument when `f` is
measurable. -/
theorem Option.unwrapM.measurable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → Measure β} (hf : Measurable f) :
    Measurable (Option.unwrapM f) := by
  -- Direct preimage argument: for any measurable `S ⊆ Measure β`,
  -- (unwrapM f) ⁻¹' S = (if 0 ∈ S then {none} else ∅) ∪ (some '' (f ⁻¹' S)).
  intro S hS
  have hpre : (Option.unwrapM f : Option α → Measure β) ⁻¹' S =
      (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) else ∅)
      ∪ (some '' (f ⁻¹' S)) := by
    ext o; cases o with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [Option.unwrapM, h0]
    | some v => simp [Option.unwrapM]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none
    · exact MeasurableSet.empty
  · exact MeasurableSet.image_some (hf hS)

/-- **Per-callsite joint `Option.unwrapM`**.

Given measurable `o : γ → Option α` and measurable `g : γ × α → Measure β`,
`(c : γ) ↦ Option.unwrapM (fun a => g (c, a)) (o c)` is measurable.

Stamping pattern for branches of `headStep` that do
`(BinOp.eval op e1 e2).unwrapM (fun e' => dirac ⟨e', σ⟩)` etc. -/
theorem Option.unwrapM.measurable_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {o : γ → Option α} (ho : Measurable o)
    {g : γ × α → Measure β} (hg : Measurable g) :
    Measurable (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c)) := by
  -- Factor through `(c, o c) ↦ ...`:
  --   `(c : γ) ↦ (o c, c) ↦ match o' with | none => 0 | some a => g (c, a)`.
  -- Step 1: lift through `(c ↦ (o c, c))`.
  suffices h : Measurable (fun q : Option α × γ =>
      match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) by
    have hrw : (fun c : γ => Option.unwrapM (fun a => g (c, a)) (o c))
        = (fun q : Option α × γ =>
            match q.1 with | none => (0 : Measure β) | some a => g (q.2, a))
          ∘ (fun c : γ => (o c, c)) := by
      funext c
      show Option.unwrapM (fun a => g (c, a)) (o c) =
            match o c with | none => 0 | some a => g (c, a)
      unfold Option.unwrapM
      cases o c <;> rfl
    rw [hrw]
    exact h.comp (ho.prodMk measurable_id)
  -- Direct preimage on the joint option/param form.
  intro S hS
  have hpre : (fun q : Option α × γ =>
        match q.1 with | none => (0 : Measure β) | some a => g (q.2, a)) ⁻¹' S
      = (if (0 : Measure β) ∈ S then ({none} : Set (Option α)) ×ˢ Set.univ else ∅)
        ∪ (Prod.map some id) '' ((fun p : α × γ => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o', c⟩; cases o' with
    | none => by_cases h0 : (0 : Measure β) ∈ S <;> simp [h0]
    | some a => simp [Set.mem_preimage, Set.mem_image, Prod.map]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none.prod MeasurableSet.univ
    · exact MeasurableSet.empty
  · exact (MeasurableEmbedding.some_mk.prodMap .id).measurableSet_image'
      (hg.comp (measurable_snd.prodMk measurable_fst) hS)

/-- `Exp.isValM` is measurable jointly in `(e, m)`. -/
theorem Exp.isValM.measurable {T : Type _} [MeasurableSpace T] :
    Measurable (fun (p : Exp rT × Measure T) => p.1.isValM p.2) := by
  -- `isValM e m = if e.isValue then m else 0`. The predicate set is measurable
  -- (since `isValue ↔ isValueR` and `isValueR.measurable` is proved).
  have hpred : MeasurableSet {p : Exp rT × Measure T | p.1.isValue} := by
    have : {p : Exp rT × Measure T | p.1.isValue} =
           ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) ×ˢ (Set.univ : Set (Measure T)) := by
      ext ⟨e, m⟩; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
    rw [this]
    exact ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet).prod MeasurableSet.univ
  refine Measurable.ite hpred ?_ ?_
  · -- True branch: `fun p => p.2`. Measurable as `measurable_snd`.
    exact measurable_snd
  · -- False branch: constant `0`.
    exact measurable_const

/-- `fun a : Cfg rT => a.expr.isValue` is measurable: it is `isValueR ∘ expr`,
both measurable (`isValueR` via the structural recursion, `expr` via
`Cfg.measurable_expr`). -/
@[fun_prop]
theorem Cfg.isValue_measurable : Measurable (fun a : Cfg rT => a.expr.isValue) := by
  rw [← measurableSet_setOf]
  have h : {a : Cfg rT | a.expr.isValue} =
      Cfg.expr ⁻¹' ({e : Exp rT | e.isValueR} ∩ {e | Exp.lcb 0 e = true}) := by
    ext a; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
  rw [h]
  exact Cfg.measurable_expr ((Exp.isValueR.measurable.setOf).inter Exp.lcb_zero.measurableSet)

/-- The set of value configurations is measurable. This is the form consumed by
`Measurable.ite` (e.g. in `execN`/`execExactN` measurability). -/
@[measurability]
theorem Cfg.isValue_measurableSet : MeasurableSet {a : Cfg rT | a.expr.isValue} :=
  Cfg.isValue_measurable.setOf

/-- **Per-callsite joint `Exp.isValM`**.

Stamping convenience: given measurable extractors `he : γ → Exp rT` and
`hm : γ → Measure T`, `c ↦ (he c).isValM (hm c)` is measurable. Direct
composition with `Exp.isValM.measurable`. -/
theorem Exp.isValM.measurable_param {T γ : Type _} [MeasurableSpace T] [MeasurableSpace γ]
    {he : γ → Exp rT} (hhe : Measurable he)
    {hm : γ → Measure T} (hhm : Measurable hm) :
    Measurable (fun c : γ => (he c).isValM (hm c)) :=
  Exp.isValM.measurable.comp (hhe.prodMk hhm)

/-- Stamping helper for `dirac ∘ Cfg.mk` leaves. Replaces the recurring
`refine measurable_dirac.comp ?_; rw [Cfg.measurable_iff]; refine ⟨he, hs⟩`
recipe with a single direct lemma. -/
theorem Cfg.measurable_dirac_mk {γ : Type _} [MeasurableSpace γ]
    {fe : γ → Exp rT} (he : Measurable fe)
    {fs : γ → State rT} (hs : Measurable fs) :
    Measurable (fun q : γ => (dirac (Cfg.mk (fe q) (fs q)) : Measure (Cfg rT))) :=
  measurable_dirac.comp (Cfg.measurable_iff.mpr ⟨he, hs⟩)

/-- Per-callsite measurability for `Exp.asValM`.

Joint measurability of the function-space form `(e, f) ↦ e.asValM f` is not
available with the standard Pi σ-algebra on `Val rT → Measure T` — the joint
evaluation map `(v, f) ↦ f v` is not measurable in general. Instead we give the
form actually used in `headStep`: a measurable `γ`-parameterized family
`g : γ × Val rT → Measure T` is composed with `asValM` jointly in `(e, c)`.

Builds on `toVal?.measurable` (stub) to dispatch on `e.toVal?`. -/
theorem Exp.asValM.measurable {T γ : Type _} [MeasurableSpace T] [MeasurableSpace γ]
    {g : γ × Val rT → Measure T} (hg : Measurable g) :
    Measurable (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v))) := by
  -- Factor: `(e, c) ↦ (e.toVal?, c) ↦ asValM-on-option`.
  -- Step 1: lift `toVal?.measurable` over the product.
  have htoVal : Measurable (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) :=
    (Exp.toVal_question.measurable (rT := rT)).comp measurable_fst |>.prodMk measurable_snd
  -- Step 2: prove joint measurability of `(o, c) ↦ asValM-body`.
  suffices h : Measurable (fun (q : Option (Val rT) × γ) =>
      match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) by
    have hrw : (fun (p : Exp rT × γ) => p.1.asValM (fun v => g (p.2, v)))
        = (fun (q : Option (Val rT) × γ) =>
            match q.1 with | none => (0 : Measure T) | some v => g (q.2, v))
          ∘ (fun (p : Exp rT × γ) => (p.1.toVal?, p.2)) := by
      funext ⟨e, c⟩
      show Exp.asValM e (fun v => g (c, v)) =
            match e.toVal? with | none => 0 | some v => g (c, v)
      unfold Exp.asValM
      rfl
    rw [hrw]
    exact h.comp htoVal
  -- Direct preimage: for measurable `S`, the preimage decomposes into
  -- `(if 0 ∈ S then {none} ×ˢ univ else ∅) ∪ (some × id)-image of (g ⁻¹' S after swap)`.
  intro S hS
  have hpre : (fun (q : Option (Val rT) × γ) =>
        match q.1 with | none => (0 : Measure T) | some v => g (q.2, v)) ⁻¹' S
      = (if (0 : Measure T) ∈ S then ({none} : Set (Option (Val rT))) ×ˢ Set.univ else ∅)
        ∪ (Prod.map some id) '' ((fun (p : Val rT × γ) => g (p.2, p.1)) ⁻¹' S) := by
    ext ⟨o, c⟩
    cases o with
    | none =>
      by_cases h0 : (0 : Measure T) ∈ S <;>
        simp [h0]
    | some v =>
      simp [Set.mem_preimage, Set.mem_image, Prod.map]
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact MeasurableSet.singleton_none.prod MeasurableSet.univ
    · exact MeasurableSet.empty
  · refine MeasurableEmbedding.measurableSet_image' ?_ ?_
    · exact MeasurableEmbedding.some_mk.prodMap .id
    · exact hg.comp (measurable_snd.prodMk measurable_fst) hS

/-- `Cfg.uniform` is measurable jointly in `(z, σ)`. -/
theorem Cfg.uniform.measurable :
    Measurable (fun (p : Int × State rT) => Cfg.uniform p.1 p.2) := by
  -- Outer split on `z : Int` (countable + ⊤). For each fixed `z`, the σ-fiber
  -- splits on `z.isPos`: positive → `(PMF z).toMeasure.map (.lit (.int n), σ)`;
  -- non-positive → `dirac ⟨.lit (.int -1), σ⟩`.
  apply measurable_from_prod_countable_right
  intro z
  show Measurable (fun σ : State rT => Cfg.uniform z σ)
  unfold Cfg.uniform
  cases hzp : z.isPos with
  | none =>
    -- σ ↦ dirac ⟨.lit (.int -1), σ⟩
    exact Cfg.measurable_dirac_mk measurable_const measurable_id
  | some w =>
    -- σ ↦ (PMF.uniformOfFinset (Ico 0 w.val) _).toMeasure.map (fun n => ⟨.lit (.int n), σ⟩)
    -- Apply `Measure.measurable_map_uncurry` with:
    --   α := State rT, β := Int, γ := Cfg rT
    --   h (σ, n) := Cfg.mk (.lit (.int n)) σ
    --   k σ := (PMF.uniformOfFinset _ _).toMeasure  -- constant in σ
    obtain ⟨w, hw⟩ := w
    set μ : Measure Int := (PMF.uniformOfFinset (Finset.Ico 0 w)
      (Finset.nonempty_Ico.mpr hw)).toMeasure with hμ_def
    have hμ_prob : IsProbabilityMeasure μ := by
      rw [hμ_def]; infer_instance
    have hk_const : Measurable (fun _ : State rT => μ) := measurable_const
    have hker_sfinite : ProbabilityTheory.IsSFiniteKernel
        (ProbabilityTheory.Kernel.mk (fun _ : State rT => μ) hk_const) := by
      -- The kernel `Kernel.mk (fun _ => μ) _` is the constant kernel, which is
      -- SFinite when μ is sfinite (here it's a probability measure, hence sfinite).
      have hSF : MeasureTheory.SFinite μ := inferInstance
      -- Kernel.mk vs Kernel.const should be the same thing up to defeq.
      have : ProbabilityTheory.Kernel.mk (fun _ : State rT => μ) hk_const
          = ProbabilityTheory.Kernel.const (State rT) μ := rfl
      rw [this]; infer_instance
    have hh : Measurable (fun p : State rT × Int => Cfg.mk (.lit (.int p.2)) p.1) := by
      rw [Cfg.measurable_iff]
      refine ⟨?_, ?_⟩
      · -- expr: .lit (.int p.2)
        exact Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd)
      · -- state: p.1
        exact measurable_fst
    exact @Measure.measurable_map_uncurry (State rT) Int (Cfg rT) _ _ _
      _ hh (fun _ => μ) hk_const hker_sfinite

/-- `Cfg.uniformReal` is measurable in `σ`. Same `Measure.measurable_map_uncurry`
recipe as `Cfg.uniform.measurable`, with the constant kernel `fun _ => unifUnit` and
the `σ`-parametrised embedding `(σ, r) ↦ ⟨.lit (.real r), σ⟩`. -/
theorem Cfg.uniformReal.measurable :
    Measurable (fun σ : State rT => Cfg.uniformReal σ) := by
  unfold Cfg.uniformReal
  set μ : Measure rT := ProbLangℝ.unifUnit (T := rT) with hμ_def
  have hk_const : Measurable (fun _ : State rT => μ) := measurable_const
  have hker_sfinite : ProbabilityTheory.IsSFiniteKernel
      (ProbabilityTheory.Kernel.mk (fun _ : State rT => μ) hk_const) := by
    have : ProbabilityTheory.Kernel.mk (fun _ : State rT => μ) hk_const
        = ProbabilityTheory.Kernel.const (State rT) μ := rfl
    rw [this]; infer_instance
  have hh : Measurable (fun p : State rT × rT => Cfg.mk (.lit (.real p.2)) p.1) := by
    rw [Cfg.measurable_iff]
    refine ⟨?_, ?_⟩
    · exact Exp.lit.measurable.comp (BaseLit.real.measurable.comp measurable_snd)
    · exact measurable_fst
  exact @Measure.measurable_map_uncurry (State rT) rT (Cfg rT) _ _ _
    _ hh (fun _ => μ) hk_const hker_sfinite

/-! ### `headStep` per-branch continuations.

`headStep` is a 22-way `Exp.casesOn` on `cfg.expr` with `cfg.state` threaded.
For elaboration speed, we lift each non-trivial continuation out of the main
`headStep.measurable` proof as a named `def + measurability theorem`. The
keystone `Exp.measurable_rec_param` then assembles them. -/

/-- `unop` branch of `headStep`: `e.isValM ((op.eval e).unwrapM (·, σ))`. -/
@[simp] def headStep.c_unop (p : State rT × UnOp × Exp rT) : Measure (Cfg rT) :=
  p.2.2.isValM ((p.2.1.eval p.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩))

theorem headStep.c_unop.measurable [Inhabited rT] :
    Measurable (headStep.c_unop (rT := rT)) := by
  have hoe : Measurable (fun p : State rT × UnOp × Exp rT => p.2.1.eval p.2.2) :=
    Exp.UnOp_eval.measurable.comp measurable_snd
  have hdir : Measurable
      (fun q : (State rT × UnOp × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    Cfg.measurable_dirac_mk measurable_snd (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun p : State rT × UnOp × Exp rT =>
      (p.2.1.eval p.2.2).unwrapM (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT)))) :=
    Option.unwrapM.measurable_param hoe hdir
  exact Exp.isValM.measurable_param (measurable_snd.comp measurable_snd) hu

/-- `app` branch: dispatch on `e1`. Only `.lam` and `.fix` non-trivial. -/
@[simp] def headStep.c_app (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lam e1' => p.2.2.isValM (dirac ⟨Exp.open' e1' p.2.2, p.1⟩)
  | .fix e1' => p.2.2.isValM
                  (dirac ⟨Exp.app (Exp.open' e1' (.fix e1')) p.2.2, p.1⟩)
  | _ => 0

theorem headStep.c_app.measurable :
    Measurable (headStep.c_app (rT := rT)) := by
  -- Inner case on `e1` with `(σ, e2)` as the param `β = State rT × Exp rT`.
  -- The target reshapes to `fun (q : Exp rT × β) => casesOn q.1 ...`.
  -- Continuations: `c_lam q = q.1.2.isValM (dirac ⟨open' q.2 q.1.2, q.1.1⟩)` etc.
  let c_lam_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.open' q.2 q.1.2, q.1.1⟩)
  let c_fix_inner : (State rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.1.2.isValM (dirac ⟨Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2, q.1.1⟩)
  have hrw : (headStep.c_app (rT := rT))
      = (fun q : Exp rT × (State rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e1' => c_lam_inner (q.2, e1')) (fun e1' => c_fix_inner (q.2, e1'))
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_app _ = _
    unfold headStep.c_app
    cases e1 <;> rfl
  rw [hrw]
  have hinner : Measurable (fun q : Exp rT × (State rT × Exp rT) =>
      Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
        (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun e1' => c_lam_inner (q.2, e1')) (fun e1' => c_fix_inner (q.2, e1'))
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)) := by
    -- c_lam_inner: isValM (q.1.2) of dirac. Joint in q.
    have h_lam_inner : Measurable c_lam_inner := by
      refine Exp.isValM.measurable_param
        (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
        (hm := fun q : (State rT × Exp rT) × Exp rT =>
                  (dirac (Cfg.mk (Exp.open' q.2 q.1.2) q.1.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_fst
      · exact Cfg.measurable_dirac_mk
          (Exp.open'.measurable.comp
            (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
          (measurable_fst.comp measurable_fst)
    -- c_fix_inner: isValM of dirac of app (open' e1 (fix e1)) e2.
    have h_fix_inner : Measurable c_fix_inner := by
      refine Exp.isValM.measurable_param
        (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
        (hm := fun q : (State rT × Exp rT) × Exp rT =>
                  (dirac (Cfg.mk
                    (Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2) q.1.1)
                    : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_fst
      · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
        show Measurable
            (fun q : (State rT × Exp rT) × Exp rT =>
              Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2)
        refine Exp.app.measurable.comp (Measurable.prodMk ?_ ?_)
        · refine Exp.open'.measurable.comp (Measurable.prodMk measurable_snd ?_)
          exact Exp.fix.measurable.comp measurable_snd
        · exact measurable_snd.comp measurable_fst
    exp_zero_app_apply c_lam_inner, h_lam_inner, c_fix_inner, h_fix_inner
  -- Now compose with the outer reshape.
  refine hinner.comp ?_
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- `alloc` branch: `asValM e (fun v => dirac ⟨.lit (.loc fresh), σ.update_heap ...⟩)`. -/
@[simp] def headStep.c_alloc (p : State rT × Exp rT) : Measure (Cfg rT) :=
  p.2.asValM (fun vd =>
    let ℓ := p.1.heap.fresh
    dirac ⟨.lit (.loc ℓ), p.1.update_heap (·.insert ℓ vd)⟩)

theorem headStep.c_alloc.measurable :
    Measurable (headStep.c_alloc (rT := rT)) := by
  -- `c_alloc (σ, e) = e.asValM (fun v => dirac ⟨.lit (.loc σ.heap.fresh),
  --                              σ.update_heap (·.insert σ.heap.fresh v)⟩)`.
  -- Apply `Exp.asValM.measurable` with γ := State rT, but `Exp.asValM.measurable`
  -- expects the form `(p : Exp rT × γ) ↦ p.1.asValM ...`. So we reshape via swap.
  have hreshape : Measurable (fun p : State rT × Exp rT => (p.2, p.1) : State rT × Exp rT → Exp rT × State rT) :=
    measurable_snd.prodMk measurable_fst
  -- The reshaped function: `(e, σ) ↦ e.asValM (fun v => g (σ, v))`.
  -- where `g (σ, v) = dirac ⟨.lit (.loc σ.heap.fresh), update_heap ...⟩`.
  have hg : Measurable (fun q : State rT × Val rT =>
      (dirac (Cfg.mk
        (Exp.lit (.loc q.1.heap.fresh))
        (q.1.update_heap (·.insert q.1.heap.fresh q.2)))
        : Measure (Cfg rT))) := by
    refine Cfg.measurable_dirac_mk ?_ ?_
    · show Measurable (fun q : State rT × Val rT =>
          (Exp.lit (.loc q.1.heap.fresh) : Exp rT))
      refine Exp.lit.measurable.comp (BaseLit.loc.measurable.comp ?_)
      exact LocHeap.measurable_fresh.comp (State.measurable_heap.comp measurable_fst)
    · show Measurable (fun q : State rT × Val rT =>
          (q.1.update_heap (·.insert q.1.heap.fresh q.2)))
      refine State.measurable_mk_param ?_ ?_
      · -- heap: insert_param applied to (q.1.heap, q.1.heap.fresh, q.2).
        have hheap : Measurable (fun q : State rT × Val rT => q.1.heap) :=
          State.measurable_heap.comp measurable_fst
        have hfresh : Measurable (fun q : State rT × Val rT => q.1.heap.fresh) :=
          LocHeap.measurable_fresh.comp hheap
        exact (Measurable.locHeap_insert_param (V := Val rT)).comp
          (hheap.prodMk (hfresh.prodMk measurable_snd))
      · exact State.measurable_tapes.comp measurable_fst
  have hAsValM := Exp.asValM.measurable hg
  -- hAsValM : Measurable (fun p : Exp rT × State rT => p.1.asValM (fun v => g (p.2, v)))
  -- We want: Measurable (fun p : State rT × Exp rT => p.2.asValM (...)).
  exact hAsValM.comp hreshape

/-- `cond` branch: dispatch on `ec`. Only `.lit (.bool true/false)` non-trivial. -/
@[simp] def headStep.c_cond (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.bool true) => dirac ⟨p.2.2.1, p.1⟩
  | .lit (.bool false) => dirac ⟨p.2.2.2, p.1⟩
  | _ => 0

theorem headStep.c_cond.measurable [Inhabited rT] :
    Measurable (headStep.c_cond (rT := rT)) := by
  -- Nested rec on `ec` with `(σ, et, ef)` as param.
  -- For each Exp ctor: only `.lit` non-zero, and within `.lit` only `.bool true/false`.
  -- Cleanest: use Exp.measurable_rec_param on ec, with c_lit doing a nested
  -- BaseLit.measurable_rec.
  let c_lit_inner : (State rT × Exp rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun q => match q.2 with
      | .bool true => dirac ⟨q.1.2.1, q.1.1⟩
      | .bool false => dirac ⟨q.1.2.2, q.1.1⟩
      | _ => 0
  have hrw : (headStep.c_cond (rT := rT))
      = (fun q : Exp rT × (State rT × Exp rT × Exp rT) =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT × Exp rT =>
            (p.2.1, p.1, p.2.2.1, p.2.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.c_cond _ = _
    unfold headStep.c_cond
    cases ec with
    | lit l => cases l with
      | bool b => cases b <;> rfl
      | _ => rfl
    | _ => rfl
  rw [hrw]
  -- c_lit_inner: BaseLit dispatch, only `.bool` live; bool→if-then-else of diracs.
  have hc_lit_inner : Measurable c_lit_inner := by
    let c_bool_inner : (State rT × Exp rT × Exp rT) × Bool → Measure (Cfg rT) :=
      fun r => if r.2 then dirac ⟨r.1.2.1, r.1.1⟩ else dirac ⟨r.1.2.2, r.1.1⟩
    have hrw2 : (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
          c_lit_inner q)
        = (fun p : BaseLit rT × (State rT × Exp rT × Exp rT) =>
            BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
              (fun _ => 0)
              (fun b => c_bool_inner (p.2, b))
              0 (fun _ => 0) (fun _ => 0) (fun _ => 0))
          ∘ (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT => (q.2, q.1)) := by
      funext ⟨c, l⟩
      show c_lit_inner _ = _
      cases l with
      | bool b => cases b <;> rfl
      | _ => rfl
    change Measurable (fun q : (State rT × Exp rT × Exp rT) × BaseLit rT =>
      c_lit_inner q)
    rw [hrw2]
    refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
    have h_bool_inner : Measurable c_bool_inner := by
      show Measurable (fun r : (State rT × Exp rT × Exp rT) × Bool =>
        if r.2 then (dirac ⟨r.1.2.1, r.1.1⟩ : Measure (Cfg rT))
                else dirac ⟨r.1.2.2, r.1.1⟩)
      refine Measurable.ite ?_ ?_ ?_
      · exact MeasurableSet.preimage (measurableSet_singleton true) measurable_snd
      · exact Cfg.measurable_dirac_mk
          ((measurable_fst.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
      · exact Cfg.measurable_dirac_mk
          ((measurable_snd.comp measurable_snd).comp measurable_fst)
          (measurable_fst.comp measurable_fst)
    baseLit_zero_bool_apply c_bool_inner, h_bool_inner
  -- Outer Exp dispatch: only c_lit live; stamp it.
  have hinner : Measurable (fun q : Exp rT × (State rT × Exp rT × Exp rT) =>
      Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
        (fun _ => 0) (fun _ => 0)
        (fun l => c_lit_inner (q.2, l))
        (fun _ => 0) (fun _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)) := by
    exp_zero_lit_apply c_lit_inner, hc_lit_inner
  refine hinner.comp ?_
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).comp measurable_snd |>.prodMk
        ((measurable_snd.comp measurable_snd).comp measurable_snd)))

/-- `case` branch: dispatch on `ec`, `.inl e`/`.inr e` non-trivial. -/
@[simp] def headStep.c_case (p : State rT × Exp rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .inl e => e.isValM (dirac ⟨p.2.2.1.app e, p.1⟩)
  | .inr e => e.isValM (dirac ⟨p.2.2.2.app e, p.1⟩)
  | _ => 0

theorem headStep.c_case.measurable :
    Measurable (headStep.c_case (rT := rT)) := by
  -- Inner case on `ec` with β := (State rT × Exp rT × Exp rT) carrying (σ, et, ef).
  -- Live arms: .inl e → e.isValM (dirac ⟨et.app e, σ⟩); .inr e → similar with ef.
  let c_inl_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.1.app q.2, q.1.1⟩)
  let c_inr_inner : (State rT × Exp rT × Exp rT) × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.isValM (dirac ⟨q.1.2.2.app q.2, q.1.1⟩)
  have hrw : (headStep.c_case (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
            (fun e => c_inl_inner (q.2, e))
            (fun e => c_inr_inner (q.2, e))
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, ec, et, ef⟩
    show headStep.c_case _ = _
    unfold headStep.c_case
    cases ec <;> rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  -- Two live arms: c_inl_inner and c_inr_inner.
  have h_inl_inner : Measurable c_inl_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
      (hm := fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk (q.1.2.1.app q.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      have hp : Measurable (fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
          (q.1.2.1, q.2)) :=
        (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
      exact Exp.app.measurable.comp hp
  have h_inr_inner : Measurable c_inr_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : (State rT × Exp rT × Exp rT) × Exp rT => q.2)
      (hm := fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk (q.1.2.2.app q.2) q.1.1) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_snd
    · refine Cfg.measurable_dirac_mk ?_ (measurable_fst.comp measurable_fst)
      have hp : Measurable (fun q : (State rT × Exp rT × Exp rT) × Exp rT =>
          (q.1.2.2, q.2)) :=
        (measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
      exact Exp.app.measurable.comp hp
  exp_zero_case_apply c_inl_inner, h_inl_inner, c_inr_inner, h_inr_inner

/-- `load` branch: dispatch on `e`, `.lit (.loc ℓ)` non-trivial, then heap lookup. -/
@[simp] def headStep.c_load (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.loc ℓ) => match p.1.heap[ℓ]? with
                      | none => 0
                      | some v => dirac ⟨Exp.ofVal v, p.1⟩
  | _ => 0

theorem headStep.c_load.measurable [Inhabited rT] :
    Measurable (headStep.c_load (rT := rT)) := by
  -- Three-level: outer Exp.lit live → inner BaseLit.loc live → option dispatch on
  -- heap[ℓ]?. The innermost some-branch is `dirac ⟨ofVal v, σ⟩`.
  let c_leaf : State rT × Loc → Measure (Cfg rT) :=
    fun q => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      q.1.heap[q.2]? 0 (fun v => dirac ⟨Exp.ofVal v, q.1⟩)
  let c_lit_inner : State rT × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_load (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_load _ = _
    unfold headStep.c_load
    cases e <;> (try rfl);
      (rename_i l; cases l <;> (try rfl))
    -- The remaining case is `.loc ℓ`: heap lookup.
    rename_i ℓ
    show _ = c_leaf (σ, ℓ)
    simp only [c_leaf]
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  -- c_leaf: option dispatch on heap[ℓ]? jointly measurable in (σ, ℓ).
  have hc_leaf : Measurable c_leaf := by
    -- Need joint measurability of (σ, ℓ) ↦ σ.heap[ℓ]?. Split on countable Loc.
    have hheap_getElem : Measurable
        (fun q : State rT × Loc => q.1.heap[q.2]?) := by
      have hflat : Measurable (fun p : Loc × State rT => p.2.heap[p.1]?) := by
        apply measurable_from_prod_countable_right
        intro ℓ
        exact (LocHeap.measurable_getElem? ℓ).comp State.measurable_heap
      exact hflat.comp (measurable_snd.prodMk measurable_fst)
    refine Option.measurable_elim_param_zero
      (f := fun q : State rT × Loc => q.1.heap[q.2]?)
      hheap_getElem
      (some_branch := fun q : (State rT × Loc) × Val rT =>
        (dirac (Cfg.mk (Exp.ofVal q.2) q.1.1) : Measure (Cfg rT))) ?_
    -- some_branch measurability: `dirac ⟨ofVal v, σ⟩`.
    exact Cfg.measurable_dirac_mk
      (Val.fst.measurable.comp measurable_snd) (measurable_fst.comp measurable_fst)
  -- c_lit_inner: BaseLit cases on `q.2` with only `.loc` live; swap & stamp.
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable (fun p : BaseLit rT × State rT =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, hc_leaf
    exact BaseLit.measurable_param_swap hbase
  -- Outer Exp.measurable_rec_param: only `c_lit` live; stamp it.
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- `store` branch: dispatch on `e1`, `.lit (.loc ℓ)` non-trivial, then asValM. -/
@[simp] def headStep.c_store (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1 with
  | .lit (.loc ℓ) => p.2.2.asValM (fun v =>
      match p.1.heap[ℓ]? with
      | none => 0
      | some _ => dirac ⟨.lit .unit, p.1.update_heap (·.insert ℓ v)⟩)
  | _ => 0

theorem headStep.c_store.measurable [Inhabited rT] :
    Measurable (headStep.c_store (rT := rT)) := by
  -- Three-level: outer Exp.lit live → inner BaseLit.loc live → asValM on e2 with
  -- inner heap-lookup option dispatch.
  -- After outer Exp + inner BaseLit dispatch, the live "leaf" takes (σ, ℓ, e2)
  -- and computes `e2.asValM (fun v => option_dispatch on heap[ℓ]?)`.
  let c_leaf_inner_someBranch : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => dirac ⟨.lit .unit, r.1.1.update_heap (·.insert r.1.2 r.2)⟩
  -- After heap[ℓ]?-option dispatch, the some-branch is `dirac (...)`.
  let c_leaf_g : (State rT × Loc) × Val rT → Measure (Cfg rT) :=
    fun r => Option.casesOn (motive := fun _ => Measure (Cfg rT))
      r.1.1.heap[r.1.2]? 0 (fun _ => c_leaf_inner_someBranch r)
  -- The leaf for c_store's lit-loc-only arm: takes (state × exp_e2) × Loc, produces measure.
  let c_leaf : (State rT × Exp rT) × Loc → Measure (Cfg rT) :=
    fun r => r.1.2.asValM (fun v => c_leaf_g ((r.1.1, r.2), v))
  let c_lit_inner : (State rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (q.1, ℓ)) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_store (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner ((q.2.1, q.2.2), l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_store _ = _
    unfold headStep.c_store
    cases e1 <;> (try rfl)
    rename_i l; cases l <;> (try rfl)
    -- The `.lit (.loc ℓ)` case: must show asValM matches c_leaf.
    rename_i ℓ
    show _ = c_leaf ((σ, e2), ℓ)
    simp only [c_leaf, c_leaf_g, c_leaf_inner_someBranch]
    unfold Exp.asValM
    cases e2.toVal? <;> (try rfl)
    rename_i v
    cases σ.heap[ℓ]? <;> rfl
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  -- c_leaf_inner_someBranch: dirac ⟨.lit .unit, σ.update_heap (insert ℓ v)⟩.
  have h_someBr : Measurable c_leaf_inner_someBranch := by
    refine Cfg.measurable_dirac_mk measurable_const ?_
    -- σ.update_heap (insert ℓ v): heap becomes heap.insert ℓ v; tapes unchanged.
    · show Measurable (fun r : (State rT × Loc) × Val rT =>
        r.1.1.update_heap (·.insert r.1.2 r.2))
      refine State.measurable_mk_param ?_ ?_
      · -- heap: insert
        show Measurable (fun r : (State rT × Loc) × Val rT =>
          r.1.1.heap.insert r.1.2 r.2)
        have hmk : Measurable
            (fun r : (State rT × Loc) × Val rT =>
              (r.1.1.heap, r.1.2, r.2)) :=
          (State.measurable_heap.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
        exact Measurable.locHeap_insert_param.comp hmk
      · exact State.measurable_tapes.comp (measurable_fst.comp measurable_fst)
  -- c_leaf_g: option dispatch on heap[ℓ]?.
  have h_g : Measurable c_leaf_g := by
    have hheap : Measurable (fun r : (State rT × Loc) × Val rT => r.1.1.heap[r.1.2]?) := by
      have hflat : Measurable (fun p : Loc × State rT => p.2.heap[p.1]?) := by
        apply measurable_from_prod_countable_right
        intro ℓ
        exact (LocHeap.measurable_getElem? ℓ).comp State.measurable_heap
      have hproj : Measurable (fun r : (State rT × Loc) × Val rT => (r.1.2, r.1.1)) :=
        (measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)
      exact hflat.comp hproj
    refine Option.measurable_elim_param_zero
      (f := fun r : (State rT × Loc) × Val rT => r.1.1.heap[r.1.2]?) hheap
      (some_branch := fun s : ((State rT × Loc) × Val rT) × Val rT =>
        c_leaf_inner_someBranch s.1) ?_
    exact h_someBr.comp measurable_fst
  -- c_leaf: e2.asValM (fun v => c_leaf_g ((σ, ℓ), v)). β = State rT × Exp rT
  have h_leaf : Measurable c_leaf := by
    -- Apply Exp.asValM.measurable with γ = State rT × Exp rT × Loc.
    -- Need to massage c_leaf into the right shape.
    -- Exp.asValM.measurable takes Measurable g : γ × Val → Measure T, gives
    -- Measurable (fun (p : Exp × γ) => p.1.asValM (fun v => g (p.2, v))).
    -- Our c_leaf : ((σ, e2), ℓ) ↦ e2.asValM (fun v => c_leaf_g ((σ, ℓ), v)).
    -- Reshape: γ := State × Loc, c_leaf = (asValM applied to ...) ∘ reshape.
    -- g : (State × Loc) × Val → Measure (Cfg rT) is c_leaf_g.
    have hasValM := Exp.asValM.measurable (γ := State rT × Loc) h_g
    -- hasValM : Measurable (fun (p : Exp × (State × Loc)) => p.1.asValM (fun v => c_leaf_g (p.2, v)))
    have hreshape : Measurable (fun r : (State rT × Exp rT) × Loc =>
        (r.1.2, r.1.1, r.2) : (State rT × Exp rT) × Loc → Exp rT × State rT × Loc) :=
      (measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact hasValM.comp hreshape
  -- c_lit_inner: BaseLit dispatch on q.2, only .loc live.
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Exp rT) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0) 0 (fun ℓ => c_leaf (p.2, ℓ)) (fun _ => 0) (fun _ => 0)) := by
      baseLit_zero_loc_apply c_leaf, h_leaf
    exact BaseLit.measurable_param_swap hbase
  -- Outer Exp dispatch: stamp.
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- `tape` branch: dispatch on `e`, `.lit (.int z)` non-trivial. -/
@[simp] def headStep.c_tape (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.int z) =>
    let α := p.1.tapes.fresh
    dirac ⟨.lit (.lbl α), p.1.update_tapes (·.insert α (.empty z))⟩
  | _ => 0

theorem headStep.c_tape.measurable [Inhabited rT] :
    Measurable (headStep.c_tape (rT := rT)) := by
  -- Two-level: outer `Exp.measurable_rec_param` only `.lit` live; inner
  -- `BaseLit.measurable_rec_param` only `.int` live. β := State rT throughout.
  let c_int_inner : State rT × Int → Measure (Cfg rT) :=
    fun q => dirac ⟨.lit (.lbl q.1.tapes.fresh),
      q.1.update_tapes (·.insert q.1.tapes.fresh (.empty q.2))⟩
  -- Outer Exp.measurable_rec_param calls c_lit with `(β, BaseLit) = (State, BaseLit)`.
  let c_lit_inner : State rT × BaseLit rT → Measure (Cfg rT) :=
    fun q =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) q.2
        (fun z => c_int_inner (q.1, z)) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hrw : (headStep.c_tape (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l => c_lit_inner (q.2, l))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_tape _ = _
    unfold headStep.c_tape
    cases e <;> (try rfl)
    rename_i l; cases l <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  -- Inner: c_int_inner is measurable.
  have hc_int : Measurable c_int_inner := by
    -- The result depends on (σ, z) through σ.tapes.fresh, σ.update_tapes (insert fresh (empty z)).
    refine Cfg.measurable_dirac_mk ?_ ?_
    · -- expr: .lit (.lbl q.1.tapes.fresh)
      refine Exp.lit.measurable.comp (BaseLit.lbl.measurable.comp ?_)
      exact LocHeap.measurable_fresh.comp (State.measurable_tapes.comp measurable_fst)
    · -- state: q.1.update_tapes (·.insert q.1.tapes.fresh (.empty q.2))
      show Measurable (fun q : State rT × Int =>
        q.1.update_tapes (·.insert q.1.tapes.fresh (Tape.empty q.2)))
      refine State.measurable_mk_param (State.measurable_heap.comp measurable_fst) ?_
      show Measurable (fun q : State rT × Int =>
        q.1.tapes.insert q.1.tapes.fresh (Tape.empty q.2))
      have htape_empty : Measurable (Tape.empty) := Measurable.of_discrete
      have hmk : Measurable
          (fun q : State rT × Int => (q.1.tapes, q.1.tapes.fresh, Tape.empty q.2)) :=
        (State.measurable_tapes.comp measurable_fst).prodMk
          ((LocHeap.measurable_fresh.comp (State.measurable_tapes.comp measurable_fst)).prodMk
            (htape_empty.comp measurable_snd))
      exact Measurable.locHeap_insert_param.comp hmk
  -- c_lit_inner: BaseLit.casesOn with only c_int live; swap & stamp.
  have hc_lit : Measurable c_lit_inner := by
    have hbase : Measurable
        (fun p : BaseLit rT × State rT =>
          BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
            (fun z => c_int_inner (p.2, z)) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)) := by
      baseLit_zero_int_apply c_int_inner, hc_int
    exact BaseLit.measurable_param_swap hbase
  -- Outer: Exp.measurable_rec_param with only c_lit live; stamp it.
  exp_zero_lit_apply c_lit_inner, hc_lit

/-- `rand` branch: doubly-nested dispatch on `(e1, e2)` shape. -/
@[simp] def headStep.c_rand (p : State rT × Exp rT × Exp rT) : Measure (Cfg rT) :=
  match p.2.1, p.2.2 with
  | .lit (.int z), .lit .unit => Cfg.uniform z p.1
  | .lit (.int z), .lit (.lbl α) =>
    match p.1.tapes[α]? with
    | none => 0
    | some ⟨M, ns⟩ =>
      if M = z then
        match ns with
        | [] => Cfg.uniform z p.1
        | n :: ns' => dirac ⟨.lit (.int n), p.1.update_tapes (·.insert α ⟨M, ns'⟩)⟩
      else Cfg.uniform z p.1
  | _, _ => 0

theorem headStep.c_rand.measurable [Inhabited rT] :
    Measurable (headStep.c_rand (rT := rT)) := by
  -- Structure: outer Exp dispatch (e1) → BaseLit dispatch (l1, only .int live) →
  -- inner Exp dispatch (e2) → BaseLit dispatch (l2, .unit AND .lbl live).
  -- The .lbl arm dispatches on `σ.tapes[α]?` (an Option Tape), and the some-branch
  -- further dispatches on the tape contents. Since Tape has Top σ-alg and is
  -- Countable, we factor out the discrete (α, z, optTape) and reduce to
  -- σ-measurability of three primitive arms (0, Cfg.uniform, dirac).

  -- Innermost: the function of (σ, z, α, optTape) returning Measure (Cfg rT).
  -- This is the body of the `.lbl α` arm. Lbl × Int × Option Tape are all
  -- countable + discrete, so we use `measurable_from_prod_countable_*`.
  let c_lbl_leaf : State rT × Int × Lbl × Option Tape → Measure (Cfg rT) :=
    fun ⟨σ, z, α, optTape⟩ =>
      match optTape with
      | none => 0
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => Cfg.uniform z σ
          | n :: ns' => dirac ⟨.lit (.int n), σ.update_tapes (·.insert α ⟨M, ns'⟩)⟩
        else Cfg.uniform z σ
  -- c_lbl_leaf is measurable in σ for each fixed (z, α, optTape) — factor as
  -- countable_right over (z, α, optTape).
  have hc_lbl_leaf : Measurable c_lbl_leaf := by
    -- Reshape (σ, z, α, optTape) ↦ ((z, α, optTape), σ).
    show Measurable c_lbl_leaf
    have hflat : Measurable
        (fun p : (Int × Lbl × Option Tape) × State rT =>
          c_lbl_leaf (p.2, p.1.1, p.1.2.1, p.1.2.2)) := by
      apply measurable_from_prod_countable_right
      intro ⟨z, α, optTape⟩
      -- Per fixed (z, α, optTape): function σ ↦ <body>.
      show Measurable (fun σ : State rT => c_lbl_leaf (σ, z, α, optTape))
      simp only [c_lbl_leaf]
      match optTape with
      | none => exact measurable_const  -- 0
      | some ⟨M, ns⟩ =>
        by_cases hMz : M = z
        · subst hMz
          simp only [↓reduceIte]
          match ns with
          | [] =>
            exact (Cfg.uniform.measurable (rT := rT)).comp
              (measurable_const.prodMk measurable_id)
          | n :: ns' =>
            -- dirac ⟨.lit (.int n), σ.update_tapes (·.insert α ⟨M, ns'⟩)⟩.
            refine Cfg.measurable_dirac_mk measurable_const ?_
            -- state: σ.update_tapes (·.insert α ⟨M, ns'⟩) — σ is the only varying part.
            show Measurable (fun σ : State rT =>
              σ.update_tapes (·.insert α ⟨M, ns'⟩))
            refine State.measurable_mk_param State.measurable_heap ?_
            show Measurable (fun σ : State rT => σ.tapes.insert α ⟨M, ns'⟩)
            -- insert with both ℓ and v constant in σ.
            have hpair : Measurable
                (fun σ : State rT => (σ.tapes, α, (⟨M, ns'⟩ : Tape))) :=
              State.measurable_tapes.prodMk (measurable_const.prodMk measurable_const)
            exact Measurable.locHeap_insert_param.comp hpair
        · -- M ≠ z: result is Cfg.uniform z σ.
          simp only [hMz, ↓reduceIte]
          exact (Cfg.uniform.measurable (rT := rT)).comp
            (measurable_const.prodMk measurable_id)
    -- hflat says (p : (Int × Lbl × Option Tape) × State) ↦ c_lbl_leaf (p.2, ...) is meas.
    -- We want (σ, z, α, optTape) ↦ c_lbl_leaf (σ, z, α, optTape).
    have hreshape : Measurable (fun q : State rT × Int × Lbl × Option Tape =>
        ((q.2.1, q.2.2.1, q.2.2.2), q.1) :
        State rT × Int × Lbl × Option Tape → (Int × Lbl × Option Tape) × State rT) :=
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk measurable_fst
    exact hflat.comp hreshape
  -- The `.lbl` arm wraps `c_lbl_leaf` by supplying σ.tapes[α]? for the optTape slot.
  -- Function of (σ, z, α : Lbl).
  let c_lbl_arm : State rT × Int × Lbl → Measure (Cfg rT) :=
    fun ⟨σ, z, α⟩ => c_lbl_leaf (σ, z, α, σ.tapes[α]?)
  have hc_lbl_arm : Measurable c_lbl_arm := by
    show Measurable c_lbl_arm
    -- Factor: c_lbl_arm = c_lbl_leaf ∘ (σ, z, α) ↦ (σ, z, α, σ.tapes[α]?).
    have hproj : Measurable
        (fun q : State rT × Int × Lbl =>
          (q.1, q.2.1, q.2.2, q.1.tapes[q.2.2]?)) := by
      refine measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk ?_))
      -- (σ, α) ↦ σ.tapes[α]? — split on countable Lbl.
      have hlookup : Measurable
          (fun q : State rT × Int × Lbl => q.1.tapes[q.2.2]?) := by
        have hflat : Measurable (fun p : Lbl × State rT => p.2.tapes[p.1]?) := by
          apply measurable_from_prod_countable_right
          intro α
          exact (LocHeap.measurable_getElem? α).comp State.measurable_tapes
        exact hflat.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
      exact hlookup
    exact hc_lbl_leaf.comp hproj
  -- The `.unit` arm of l2 (with z extracted from outer .lit .int):
  -- function of (σ, z, _ : Unit) returning Cfg.uniform z σ. Independent of the Unit.
  let c_unit_arm : State rT × Int × Unit → Measure (Cfg rT) :=
    fun ⟨σ, z, _⟩ => Cfg.uniform z σ
  have hc_unit_arm : Measurable c_unit_arm :=
    (Cfg.uniform.measurable (rT := rT)).comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  -- l2 BaseLit dispatch: takes (σ, z, l2) — only .unit and .lbl live.
  let c_l2_dispatch : (State rT × Int) × BaseLit rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, z⟩, l2⟩ =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) l2
        (fun _ => 0) (fun _ => 0)
        (c_unit_arm (σ, z, ()))
        (fun _ => 0)
        (fun α => c_lbl_arm (σ, z, α))
        (fun _ => 0)
  have hc_l2 : Measurable c_l2_dispatch := by
    -- BaseLit dispatch, two live arms (.unit, .lbl). No existing macro for two-arm
    -- BaseLit; do it manually with `apply BaseLit.measurable_rec_param`.
    have hswap : Measurable
        (fun q : (State rT × Int) × BaseLit rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Int) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0)
          (c_unit_arm (p.2.1, p.2.2, ()))
          (fun _ => 0)
          (fun α => c_lbl_arm (p.2.1, p.2.2, α))
          (fun _ => 0)) := by
      apply BaseLit.measurable_rec_param
        (c_int := fun _ => 0) (c_bool := fun _ => 0)
        (c_unit := fun q : (State rT × Int) × Unit => c_unit_arm (q.1.1, q.1.2, q.2))
        (c_loc := fun _ => 0)
        (c_lbl := fun q : (State rT × Int) × Lbl => c_lbl_arm (q.1.1, q.1.2, q.2))
        (c_real := fun _ => 0)
        (h_int := measurable_const) (h_bool := measurable_const)
        (h_unit := hc_unit_arm.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
        (h_loc := measurable_const)
        (h_lbl := hc_lbl_arm.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
        (h_real := measurable_const)
    exact hbase.comp hswap
  -- e2 Exp dispatch: only .lit live, feeding to c_l2_dispatch.
  let c_e2_dispatch : (State rT × Int) × Exp rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, z⟩, e2⟩ =>
      Exp.casesOn (motive := fun _ => Measure (Cfg rT)) e2
        (fun _ => 0) (fun _ => 0)
        (fun l2 => c_l2_dispatch ((σ, z), l2))
        (fun _ => 0) (fun _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)
  have hc_e2 : Measurable c_e2_dispatch := by
    -- The macro produces `Measurable (fun p : Exp × β => casesOn p.1 ...)` but
    -- c_e2_dispatch is `(β × Exp) → ...`. Swap via composition.
    have hswap : Measurable (fun q : (State rT × Int) × Exp rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : Exp rT × (State rT × Int) =>
        Exp.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun _ => 0) (fun _ => 0)
          (fun l => c_l2_dispatch (p.2, l))
          (fun _ => 0) (fun _ => 0)
          (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
          (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
          (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
          (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0)) := by
      exp_zero_lit_apply (fun q : (State rT × Int) × BaseLit rT => c_l2_dispatch q), hc_l2
    exact hbase.comp hswap
  -- l1 BaseLit dispatch: only .int live, extracting z and threading e2.
  -- β here is (State × Exp) carrying (σ, e2). Continuation takes (β, Int) i.e. (σ, e2, z).
  let c_l1_dispatch : (State rT × Exp rT) × BaseLit rT → Measure (Cfg rT) :=
    fun ⟨⟨σ, e2⟩, l1⟩ =>
      BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) l1
        (fun z => c_e2_dispatch ((σ, z), e2)) (fun _ => 0) 0 (fun _ => 0)
        (fun _ => 0) (fun _ => 0)
  have hc_l1 : Measurable c_l1_dispatch := by
    have hswap : Measurable
        (fun q : (State rT × Exp rT) × BaseLit rT => (q.2, q.1)) :=
      measurable_snd.prodMk measurable_fst
    have hbase : Measurable (fun p : BaseLit rT × (State rT × Exp rT) =>
        BaseLit.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun z => c_e2_dispatch ((p.2.1, z), p.2.2)) (fun _ => 0) 0
          (fun _ => 0) (fun _ => 0) (fun _ => 0)) := by
      apply BaseLit.measurable_rec_param
        (c_int := fun q : (State rT × Exp rT) × Int =>
          c_e2_dispatch ((q.1.1, q.2), q.1.2))
        (c_bool := fun _ => 0) (c_unit := fun _ => 0)
        (c_loc := fun _ => 0) (c_lbl := fun _ => 0) (c_real := fun _ => 0)
        (h_int := hc_e2.comp
          (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)))
        (h_bool := measurable_const) (h_unit := measurable_const)
        (h_loc := measurable_const) (h_lbl := measurable_const)
        (h_real := measurable_const)
    exact hbase.comp hswap
  -- Outer e1 Exp dispatch: only .lit live, with β = State × Exp carrying (σ, e2).
  -- Reshape c_rand to Exp.casesOn form composed with swap.
  have hrw : (headStep.c_rand (rT := rT))
      = (fun q : Exp rT × State rT × Exp rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0)
            (fun l1 => c_l1_dispatch ((q.2.1, q.2.2), l1))
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT × Exp rT => (p.2.1, p.1, p.2.2)) := by
    funext ⟨σ, e1, e2⟩
    show headStep.c_rand _ = _
    unfold headStep.c_rand
    -- The `match p.2.1, p.2.2 with` simultaneous match unfolds via cases.
    cases e1 <;> (try rfl);
      rename_i l1;
      cases l1 <;> (try rfl);
      rename_i z;
      cases e2 <;> (try rfl);
      rename_i l2;
      cases l2 <;> (try rfl)
  rw [hrw]
  refine Measurable.comp ?_
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exp_zero_lit_apply (fun q : (State rT × Exp rT) × BaseLit rT => c_l1_dispatch q), hc_l1

/-- `scrut` branch: `e.isValM` of dispatch on `Pat.tryMatch p e`. -/
@[simp] def headStep.c_scrut (p : State rT × Exp rT × Pat rT) : Measure (Cfg rT) :=
  p.2.1.isValM
    (match Pat.tryMatch p.2.2 p.2.1 with
      | some b => dirac ⟨.inl b, p.1⟩
      | none => dirac ⟨.inr (.lit .unit), p.1⟩)

theorem headStep.c_scrut.measurable : Measurable (headStep.c_scrut (rT := rT)) := by
  have hrw : (headStep.c_scrut (rT := rT))
      = fun p : State rT × Exp rT × Pat rT =>
        p.2.1.isValM
          (Option.casesOn (motive := fun _ => Measure (Cfg rT)) (Pat.tryMatch p.2.2 p.2.1)
            (Measure.dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
            (fun b => Measure.dirac (⟨.inl b, p.1⟩ : Cfg rT))) := by
    funext p
    show headStep.c_scrut p = _
    unfold headStep.c_scrut
    cases hp : Pat.tryMatch p.2.2 p.2.1 <;> rfl
  rw [hrw]
  apply Exp.isValM.measurable_param
  · exact measurable_fst.comp measurable_snd
  · -- Inner measure measurable via Option.measurable_elim_param.
    refine Option.measurable_elim_param
      (f := fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1)
      (default := fun p : State rT × Exp rT × Pat rT =>
        Measure.dirac (⟨.inr (.lit .unit), p.1⟩ : Cfg rT))
      (some_branch := fun s : (State rT × Exp rT × Pat rT) × Exp rT =>
        Measure.dirac (⟨.inl s.2, s.1.1⟩ : Cfg rT)) ?_ ?_ ?_
    · have : (fun p : State rT × Exp rT × Pat rT => Pat.tryMatch p.2.2 p.2.1)
          = (Function.uncurry (fun (p : Pat rT) (e : Exp rT) => Pat.tryMatch p e)) ∘
            (fun p : State rT × Exp rT × Pat rT => (p.2.2, p.2.1)) := by
        funext _; rfl
      rw [this]
      exact ProbLang.Exp.tryMatch.measurable_joint.comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
    · refine Cfg.measurable_dirac_mk measurable_const measurable_fst
    · refine Cfg.measurable_dirac_mk
        (Exp.inl.measurable.comp measurable_snd)
        (measurable_fst.comp measurable_fst)

/-- `fst (pair e1 e2)` branch: nested rec on subterm. -/
@[simp] def headStep.c_fst (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e1, p.1⟩))
  | _ => 0

theorem headStep.c_fst.measurable :
    Measurable (headStep.c_fst (rT := rT)) := by
  -- Inner case on `e` with `σ : State rT` as the param. Only `.pair` is live:
  -- `c_pair_inner (σ, e1, e2) = e1.isValM (e2.isValM (dirac ⟨e1, σ⟩))`.
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩))
  have hrw : (headStep.c_fst (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_fst _ = _
    unfold headStep.c_fst
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  -- c_pair_inner: e1.isValM (e2.isValM (dirac ⟨e1, σ⟩)). Joint in (σ, e1, e2).
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.1, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param
        (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.1 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_fst.comp measurable_snd) measurable_fst
  -- Stamp the outer dispatch.
  exp_zero_pair_apply c_pair_inner, h_pair_inner

/-- `snd (pair e1 e2)` branch: same shape as `c_fst`, projects e2. -/
@[simp] def headStep.c_snd (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e2, p.1⟩))
  | _ => 0

theorem headStep.c_snd.measurable :
    Measurable (headStep.c_snd (rT := rT)) := by
  -- Same pattern as `c_fst.measurable` but projecting e2 instead of e1.
  let c_pair_inner : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun q => q.2.1.isValM (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩))
  have hrw : (headStep.c_snd (rT := rT))
      = (fun q : Exp rT × State rT =>
          Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
            (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ => 0) (fun _ => 0)
            (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
            (fun e1 e2 => c_pair_inner (q.2, e1, e2))
            (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
            (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
            (fun _ => 0) (fun _ _ => 0) 0 0 (fun _ _ => 0))
        ∘ (fun p : State rT × Exp rT => (p.2, p.1)) := by
    funext ⟨σ, e⟩
    show headStep.c_snd _ = _
    unfold headStep.c_snd
    cases e <;> rfl
  rw [hrw]
  refine Measurable.comp ?_ (measurable_snd.prodMk measurable_fst)
  -- c_pair_inner: e1.isValM (e2.isValM (dirac ⟨e2, σ⟩)).
  have h_pair_inner : Measurable c_pair_inner := by
    refine Exp.isValM.measurable_param
      (he := fun q : State rT × Exp rT × Exp rT => q.2.1)
      (hm := fun q : State rT × Exp rT × Exp rT =>
        (q.2.2.isValM (dirac ⟨q.2.2, q.1⟩) : Measure (Cfg rT)))
      ?_ ?_
    · exact measurable_fst.comp measurable_snd
    · refine Exp.isValM.measurable_param
        (he := fun q : State rT × Exp rT × Exp rT => q.2.2)
        (hm := fun q : State rT × Exp rT × Exp rT =>
          (dirac (Cfg.mk q.2.2 q.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_snd
      · exact Cfg.measurable_dirac_mk (measurable_snd.comp measurable_snd) measurable_fst
  exp_zero_pair_apply c_pair_inner, h_pair_inner

/-- `binop` branch: `e1.isValM (e2.isValM ((op.eval e1 e2).unwrapM (·, σ)))`. -/
@[simp] def headStep.c_binop (p : State rT × BinOp × Exp rT × Exp rT) : Measure (Cfg rT) :=
  p.2.2.1.isValM (p.2.2.2.isValM
    ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩)))

theorem headStep.c_binop.measurable : Measurable (headStep.c_binop (rT := rT)) := by
  -- Same shape as c_unop, with one extra inner `isValM`.
  have hoe : Measurable
      (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.1.eval p.2.2.1 p.2.2.2) :=
    Exp.BinOp_eval.measurable.comp measurable_snd
  have hdir : Measurable
      (fun q : (State rT × BinOp × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    Cfg.measurable_dirac_mk measurable_snd (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT =>
      (p.2.1.eval p.2.2.1 p.2.2.2).unwrapM
        (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT)))) :=
    Option.unwrapM.measurable_param hoe hdir
  -- inner isValM on e2:
  have he2 : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hinner : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT =>
      p.2.2.2.isValM ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM
        (fun e' => (dirac (Cfg.mk e' p.1) : Measure (Cfg rT))))) :=
    Exp.isValM.measurable_param he2 hu
  -- outer isValM on e1:
  have he1 : Measurable (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  exact Exp.isValM.measurable_param he1 hinner

@[fun_prop]
theorem headStep.measurable :
    Measurable (headStep : Cfg rT → Measure (Cfg rT)) := by
  -- Strategy: reduce to a joint `Exp rT × State rT → Measure (Cfg rT)` and apply
  -- `Exp.measurable_rec_param` with `β := State rT`. The continuations
  -- correspond to each `headStep` case; many use `isValM`, `asValM`, `unwrapM`,
  -- `Cfg.uniform`, or nested case-splits (which use a second `Exp.measurable_rec`
  -- on the relevant subterm).
  --
  -- First step: reduce `Measurable headStep` to joint
  -- `Measurable (fun p : Exp rT × State rT => headStep ⟨p.1, p.2⟩)` via
  -- composition with `(Cfg.measurable_expr, Cfg.measurable_state)`.
  suffices hjoint :
      Measurable (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) by
    have hCfg : Measurable (fun cfg : Cfg rT => (cfg.expr, cfg.state)) :=
      Cfg.measurable_expr.prodMk Cfg.measurable_state
    have hrw : (headStep : Cfg rT → Measure (Cfg rT))
        = (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2)) ∘
          (fun cfg : Cfg rT => (cfg.expr, cfg.state)) := by
      funext cfg; rfl
    rw [hrw]
    exact hjoint.comp hCfg
  -- Now prove the joint version. Use `Exp.measurable_rec_param` with `β := State rT`.
  -- Each `c_X` continuation is a `State rT × Payload → Measure (Cfg rT)` map
  -- matching the corresponding `headStep` branch.
  --
  -- Define per-constructor continuations. For branches that further pattern-match
  -- on subterms (e.g. `app (lam _) _`), the continuation itself uses a nested
  -- `Exp.measurable_rec`. We split out a helper for each such case.

  -- Continuations for trivial-zero outer constructors:
  let c_bvar  : State rT × Nat → Measure (Cfg rT) := fun _ => 0
  let c_fvar  : State rT × Var → Measure (Cfg rT) := fun _ => 0
  let c_lit   : State rT × BaseLit rT → Measure (Cfg rT) := fun _ => 0
  let c_lam   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_fix   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_fail  : State rT × Unit → Measure (Cfg rT) := fun _ => 0
  let c_urand : State rT × Unit → Measure (Cfg rT) := fun p => Cfg.uniformReal p.1
  -- `app (e1, e2)` continuation: nested case on `e1`.
  -- We define `appBody : State rT × Exp rT × Exp rT → Measure (Cfg rT)` as
  -- `appBody (σ, e1, e2) := <nested case on e1>`. Measurable via
  -- `Exp.measurable_rec` on `e1` with `(σ, e2)` as joint param.
  let c_app   : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2.1 with
      | .lam e1' => p.2.2.isValM (dirac ⟨Exp.open' e1' p.2.2, p.1⟩)
      | .fix e1' => p.2.2.isValM
                      (dirac ⟨Exp.app (Exp.open' e1' (.fix e1')) p.2.2, p.1⟩)
      | _ => 0
  let c_unop  : State rT × UnOp × Exp rT → Measure (Cfg rT) :=
    fun p => p.2.2.isValM ((p.2.1.eval p.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩))
  let c_binop : State rT × BinOp × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => p.2.2.1.isValM (p.2.2.2.isValM
                ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩)))
  let c_cond  : State rT × Exp rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2.1 with
      | .lit (.bool true) => dirac ⟨p.2.2.1, p.1⟩
      | .lit (.bool false) => dirac ⟨p.2.2.2, p.1⟩
      | _ => 0
  let c_pair  : State rT × Exp rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_fst   : State rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2 with
      | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e1, p.1⟩))
      | _ => 0
  let c_snd   : State rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2 with
      | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e2, p.1⟩))
      | _ => 0
  let c_inl   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_inr   : State rT × Exp rT → Measure (Cfg rT) := fun _ => 0
  let c_case  : State rT × Exp rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2.1 with
      | .inl e => e.isValM (dirac ⟨p.2.2.1.app e, p.1⟩)
      | .inr e => e.isValM (dirac ⟨p.2.2.2.app e, p.1⟩)
      | _ => 0
  let c_alloc : State rT × Exp rT → Measure (Cfg rT) :=
    fun p => p.2.asValM (fun vd =>
              let ℓ := p.1.heap.fresh
              dirac ⟨.lit (.loc ℓ), p.1.update_heap (·.insert ℓ vd)⟩)
  let c_load  : State rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2 with
      | .lit (.loc ℓ) => match p.1.heap[ℓ]? with
                          | none => 0
                          | some v => dirac ⟨Exp.ofVal v, p.1⟩
      | _ => 0
  let c_store : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2.1 with
      | .lit (.loc ℓ) => p.2.2.asValM (fun v =>
          match p.1.heap[ℓ]? with
          | none => 0
          | some _ => dirac ⟨.lit .unit, p.1.update_heap (·.insert ℓ v)⟩)
      | _ => 0
  let c_tape  : State rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2 with
      | .lit (.int z) =>
        let α := p.1.tapes.fresh
        dirac ⟨.lit (.lbl α), p.1.update_tapes (·.insert α (.empty z))⟩
      | _ => 0
  let c_rand  : State rT × Exp rT × Exp rT → Measure (Cfg rT) :=
    fun p => match p.2.1, p.2.2 with
      | .lit (.int z), .lit .unit => Cfg.uniform z p.1
      | .lit (.int z), .lit (.lbl α) =>
        match p.1.tapes[α]? with
        | none => 0
        | some ⟨M, ns⟩ =>
          if M = z then
            match ns with
            | [] => Cfg.uniform z p.1
            | n :: ns' => dirac ⟨.lit (.int n), p.1.update_tapes (·.insert α ⟨M, ns'⟩)⟩
          else Cfg.uniform z p.1
      | _, _ => 0
  let c_scrut : State rT × Exp rT × Pat rT → Measure (Cfg rT) :=
    fun p => p.2.1.isValM
              (match Pat.tryMatch p.2.2 p.2.1 with
                | some b => dirac ⟨.inl b, p.1⟩
                | none => dirac ⟨.inr (.lit .unit), p.1⟩)
  -- Now the key claim: the joint headStep equals the casesOn-param assembly of
  -- these continuations.
  have hheq : (fun p : Exp rT × State rT => headStep (Cfg.mk p.1 p.2))
      = fun p : Exp rT × State rT => Exp.casesOn (motive := fun _ => Measure (Cfg rT)) p.1
          (fun n => c_bvar (p.2, n)) (fun x => c_fvar (p.2, x))
          (fun l => c_lit (p.2, l))
          (fun e => c_lam (p.2, e)) (fun e => c_fix (p.2, e))
          (fun e1 e2 => c_app (p.2, e1, e2))
          (fun u e => c_unop (p.2, u, e))
          (fun b e1 e2 => c_binop (p.2, b, e1, e2))
          (fun ec et ef => c_cond (p.2, ec, et, ef))
          (fun e1 e2 => c_pair (p.2, e1, e2))
          (fun e => c_fst (p.2, e)) (fun e => c_snd (p.2, e))
          (fun e => c_inl (p.2, e)) (fun e => c_inr (p.2, e))
          (fun ec el er => c_case (p.2, ec, el, er))
          (fun e => c_alloc (p.2, e)) (fun e => c_load (p.2, e))
          (fun e1 e2 => c_store (p.2, e1, e2))
          (fun e => c_tape (p.2, e))
          (fun e1 e2 => c_rand (p.2, e1, e2))
          (c_fail (p.2, ()))
          (c_urand (p.2, ()))
          (fun e pat => c_scrut (p.2, e, pat)) := by
    funext ⟨e, σ⟩
    -- Equate headStep on each Exp shape with the corresponding continuation.
    -- For branches that further case-split (app, cond, fst, snd, case, load,
    -- store, tape, rand, scrut), inner `cases` matches headStep's nested
    -- pattern. Cases that don't pattern-match on subterms close by `rfl`.
    cases e with
    | bvar | fvar | lit | lam | fix | fail | urand => rfl
    | app e1 e2 => cases e1 <;> rfl
    | unop op e => rfl
    | binop op e1 e2 => rfl
    | cond ec et ef => cases ec <;> try rfl
                       case lit l => cases l <;> try rfl
                                     case bool b => cases b <;> rfl
    | pair _ _ => rfl
    | fst e => cases e <;> rfl
    | snd e => cases e <;> rfl
    | inl _ => rfl
    | inr _ => rfl
    | case ec el er => cases ec <;> rfl
    | alloc _ => rfl
    | load e => cases e <;> try rfl
                case lit l => cases l <;> rfl
    | store e1 e2 => cases e1 <;> try rfl
                     case lit l => cases l <;> rfl
    | tape e => cases e <;> try rfl
                case lit l => cases l <;> rfl
    | rand e1 e2 => cases e1 <;> try rfl
                    case lit l1 =>
                      cases l1 <;> try rfl
                      case int z =>
                        cases e2 <;> try rfl
                        case lit l2 => cases l2 <;> rfl
    | scrut _ _ => rfl
  rw [hheq]
  -- Now apply the keystone, with measurability of each continuation.
  apply Exp.measurable_rec_param
    (c_bvar := c_bvar) (c_fvar := c_fvar) (c_lit := c_lit)
    (c_lam := c_lam) (c_fix := c_fix)
    (c_app := c_app) (c_unop := c_unop) (c_binop := c_binop)
    (c_cond := c_cond) (c_pair := c_pair)
    (c_fst := c_fst) (c_snd := c_snd)
    (c_inl := c_inl) (c_inr := c_inr) (c_case := c_case)
    (c_alloc := c_alloc) (c_load := c_load) (c_store := c_store)
    (c_tape := c_tape) (c_rand := c_rand)
    (c_fail := c_fail) (c_urand := c_urand) (c_scrut := c_scrut)
  -- Trivial-zero continuations:
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  -- c_app: matches `headStep.c_app` extracted above.
  · exact headStep.c_app.measurable
  -- c_unop: matches `headStep.c_unop` extracted above.
  · exact headStep.c_unop.measurable
  -- c_binop: matches `headStep.c_binop` extracted above.
  · exact headStep.c_binop.measurable
  -- c_cond: matches `headStep.c_cond` extracted above.
  · exact headStep.c_cond.measurable
  -- c_pair = const 0.
  · exact measurable_const
  -- c_fst: nested case on subterm.
  · exact headStep.c_fst.measurable  -- stubbed; pattern same as c_app
  · exact headStep.c_snd.measurable  -- stubbed; pattern same as c_app
  -- c_inl, c_inr = const 0.
  · exact measurable_const
  · exact measurable_const
  -- c_case: nested case on `ec`.
  · exact headStep.c_case.measurable
  -- c_alloc: matches `headStep.c_alloc` extracted above.
  · exact headStep.c_alloc.measurable
  -- c_load: nested case + match on heap lookup.
  · exact headStep.c_load.measurable
  -- c_store: nested case + asValM.
  · exact headStep.c_store.measurable
  -- c_tape: nested case on subterm.
  · exact headStep.c_tape.measurable
  -- c_rand: nested cases on both subterms + Cfg.uniform.
  · exact headStep.c_rand.measurable
  -- c_fail = const 0.
  · exact measurable_const
  -- c_urand: σ ↦ Cfg.uniformReal σ.
  · exact Cfg.uniformReal.measurable.comp measurable_fst
  -- c_scrut: isValM + tryMatch.
  · exact headStep.c_scrut.measurable

def headStepKernel : Kernel (Cfg rT) (Cfg rT) where
  measurable' := headStep.measurable
  toFun := headStep


theorem val_head_stuck {e : Exp rT} {σ : State rT} : headStep ⟨e, σ⟩ ≠ 0 → ¬e.isValue := by
  head_case <;> simp_all [Exp.isValue_iff_isValueR, Exp.isValueR]

/-- A value-*shaped* term never head-steps (stronger than `val_head_stuck`, since
`isValue → isValueR`). Used by the context-decomposition lemmas, which only need to
rule out value shape, not closed-value-hood. -/
theorem Discrete.val_head_stuck_R {e : Exp rT} {σ : State rT} {ρ : Cfg rT} :
    0 < headStep ⟨e, σ⟩ {ρ} → ¬e.isValueR := by
  head_case <;> simp_all [Exp.isValueR]

theorem val_head_stuck_R {e : Exp rT} {σ : State rT} : headStep ⟨e, σ⟩ ≠ 0 → ¬e.isValueR := by
  head_case <;> simp_all [Exp.isValueR]

theorem Exp.toVal?_isValue {e : Exp α} : e.toVal? = some v → e.isValue := by
  intro h; by_contra hne; rw [Exp.toVal?_eq_none.mpr hne] at h; exact absurd h (by simp)

theorem Exp.toVal?_isValueR {e : Exp α} (h : e.toVal? = some v) : e.isValueR :=
  (Exp.isValue_iff_isValueR.mp (Exp.toVal?_isValue h)).1

set_option maxHeartbeats 4000000 in
theorem head_ctx_step_val {e : Exp rT} {σ : State rT} {Ki : EctxItem rT} :
    headStep ⟨Ki.fillItem e, σ⟩ ≠ 0 → e.isValueR := by
  head_case
  all_goals try · simp
  all_goals cases Ki <;> intro h <;>
    simp_all [EctxItem.fillItem, Exp.isValue_iff_isValueR, Exp.isValueR, Exp.toVal?_isValueR]

inductive HeadStepSupport : Cfg rT → Cfg rT → Prop
| BetaLamS :
  e2.isValue →
  e' = Exp.open' e1 e2 →
  HeadStepSupport ⟨.app (.lam e1) e2, σ⟩ ⟨e', σ⟩
| BetaFixS :
  e2.isValue →
  e' = Exp.app (Exp.open' e1 (.fix e1)) e2 →
  HeadStepSupport ⟨.app (.fix e1) e2, σ⟩ ⟨e', σ⟩
| UnOpS :
  e.isValue →
  some e' = op.eval e →
  HeadStepSupport ⟨.unop op e, σ⟩ ⟨e', σ⟩
| BinOpS :
  e1.isValue →
  e2.isValue →
  some e' = op.eval e1 e2 →
  HeadStepSupport ⟨.binop op e1 e2, σ⟩ ⟨e', σ⟩
| IfTrueS :
  HeadStepSupport ⟨.cond (.lit (.bool true)) et _, σ⟩ ⟨et, σ⟩
| IfFalseS :
  HeadStepSupport ⟨.cond (.lit (.bool false)) _ ef, σ⟩ ⟨ef, σ⟩
| FstS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩
| SndS :
  e1.isValue →
  e2.isValue →
  HeadStepSupport ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩
| CaseLS :
  e.isValue →
  HeadStepSupport ⟨.case (.inl e) el er, σ⟩ ⟨el.app e, σ⟩
| CaseRS :
  e.isValue →
  HeadStepSupport ⟨.case (.inr e) el er, σ⟩ ⟨er.app e, σ⟩
| AllocS :
  ed.toVal? = some vd →
  ℓ = σ.heap.fresh →
  σ' = σ.update_heap (·.insert ℓ vd) →
  HeadStepSupport ⟨.alloc ed, σ⟩ ⟨.lit (.loc ℓ), σ'⟩
| LoadS :
  σ.heap[ℓ]? = some v →
  e' = Exp.ofVal v →
  HeadStepSupport ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨e', σ⟩
| StoreS :
  e.toVal? = some v →
  σ.heap[ℓ]?.isSome →
  σ' = σ.update_heap (·.insert ℓ v) →
  HeadStepSupport ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ'⟩
| RandNoTapeS :
  0 < z →
  0 ≤ v →
  v < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ ⟨.lit (.int v), σ⟩
| RandNonposS :
  ¬ 0 < z →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit .unit), σ⟩ ⟨.lit (.int (-1)), σ⟩
| TapeS :
  ℓ = σ.tapes.fresh →
  σ' = σ.update_tapes (·.insert ℓ (.empty z)) →
  HeadStepSupport ⟨.tape (.lit (.int z)), σ⟩ ⟨.lit (.lbl ℓ), σ'⟩
| RandTapeS :
  σ.tapes[α]? = some ⟨N, nn :: ns⟩ →
  z = N →
  v = nn.1 →
  σ' = σ.update_tapes (·.insert α ⟨N, ns⟩) →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeEmptyS :
  0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  0 ≤ v →
  v < z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeOtherS :
  0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  0 ≤ v →
  v < z →
  σ' = σ →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int v), σ'⟩
| RandTapeNonposEmptyS :
  ¬ 0 < z →
  σ.tapes[α]? = some ⟨N, []⟩ →
  z = N →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ⟩
| RandTapeNonposOtherS :
  ¬ 0 < z →
  σ.tapes[α]? = some ⟨N, L⟩ →
  z ≠ N →
  HeadStepSupport ⟨.rand (.lit (.int z)) (.lit (.lbl α)), σ⟩ ⟨.lit (.int (-1)), σ⟩
| ScrutSuccessS :
  e.isValue →
  Pat.tryMatch p e = some bindings →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inl bindings, σ⟩
| ScrutFailureS :
  e.isValue →
  Pat.tryMatch p e = none →
  HeadStepSupport ⟨.scrut e p, σ⟩ ⟨.inr (.lit .unit), σ⟩
| UrandS :
  ProbLangℝ.unifUnitSupport r →
  HeadStepSupport ⟨.urand, σ⟩ ⟨.lit (.real r), σ⟩

-- TODO: Not sure how to generalize you yet, let's see what the call sites look like
@[simp, discrete]
theorem Discrete.dirac_singleton_pos [Countable rT] [MeasurableSingletonClass rT]
    {a b : Cfg rT} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a .of_discrete, Set.indicator_singleton, Pi.single, Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (Set.mem_singleton _)]

/-- Countable-free version of `Discrete.dirac_singleton_pos`: needs only
`[MeasurableSingletonClass rT]` (so the singleton `{b}` is measurable), not the
full discrete structure. -/
theorem dirac_singleton_pos' [MeasurableSingletonClass rT]
    {a b : Cfg rT} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a (measurableSet_singleton b), Set.indicator_singleton, Pi.single,
        Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (Set.mem_singleton _)]

@[simp]
theorem isValM_singleton_pos [MeasurableSpace T] {e : Exp α} {m : Measure T} {s : Set T} :
    0 < (e.isValM m) s ↔ e.isValue ∧ 0 < m s := by
  simp only [Exp.isValM]
  by_cases He : e.isValue
  · rw [if_pos He]; exact ⟨fun h => ⟨He, h⟩, And.right⟩
  · rw [if_neg He]; exact ⟨fun h => absurd h (by simp), fun ⟨hv, _⟩ => absurd hv He⟩

@[simp, discrete]
theorem Discrete.unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

/-- Non-`@[discrete]` copy of `Discrete.unwrapM_singleton_pos` — it needs no
discreteness — for use in Countable-free proofs. -/
theorem unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

@[simp]
theorem asValM_singleton_pos [MeasurableSpace T] {e : Exp α} {f : Val α → Measure T} :
    0 < (e.asValM f) s ↔ ∃ v, e.toVal? = some v ∧ 0 < (f v) s := by
  unfold Exp.asValM; cases e.toVal? <;> simp

/-- Countable-free version of `Discrete.Cfg.uniform_singleton_pos_inv`: needs only
`[MeasurableSingletonClass rT]`. The `Int → Cfg rT` embedding is measurable for
any `rT`, and the only singleton-measurability used is on `Cfg rT` (from
`MeasurableSingletonClass rT`). -/
theorem Cfg.uniform_singleton_pos_inv' [MeasurableSingletonClass rT]
    {z : Int} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < Cfg.uniform z σ {ρ}) :
    ρ.state = σ ∧
    ((0 < z ∧ ∃ v : Int, ρ.expr = .lit (.int v) ∧ 0 ≤ v ∧ v < z) ∨
     (¬ 0 < z ∧ ρ.expr = .lit (.int (-1)))) := by
  unfold Cfg.uniform Int.isPos at h
  by_cases Hz : 0 < z
  · simp only [Hz, dite_true] at h
    rw [Measure.map_apply (by measurability) (measurableSet_singleton ρ),
        PMF.toMeasure_uniformOfFinset_apply _ _ (by measurability),
        ENNReal.div_pos_iff] at h
    obtain ⟨hcard, _⟩ := h
    rw [Nat.cast_ne_zero, Finset.card_ne_zero, Finset.filter_nonempty_iff] at hcard
    obtain ⟨a, ha, hfa⟩ := hcard
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hfa
    rw [Finset.mem_Ico] at ha
    subst hfa
    exact ⟨rfl, .inl ⟨Hz, a, rfl, ha.1, ha.2⟩⟩
  · simp only [Hz, dite_false] at h
    rw [dirac_singleton_pos'] at h
    have ⟨h1, h2⟩ := (Cfg.mk.injEq ..).mp h
    exact ⟨h2.symm, .inr ⟨Hz, h1.symm⟩⟩

@[discrete]
theorem Discrete.Cfg.uniform_singleton_pos_of_mem [Countable rT] [MeasurableSingletonClass rT]
    {z v : Int} {σ : State rT}
    (Hz : 0 < z) (Hv0 : 0 ≤ v) (Hvz : v < z) :
    0 < Cfg.uniform z σ {⟨.lit (.int v), σ⟩} := by
  unfold Cfg.uniform Int.isPos
  simp only [Hz, dite_true]
  rw [Measure.map_apply (f := fun x => (⟨.lit (.int x), σ⟩ : Cfg rT)) Measurable.of_discrete MeasurableSet.of_discrete]
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ MeasurableSet.of_discrete]
  rw [ENNReal.div_pos_iff]
  refine ⟨?_, ?_⟩
  · rw [ne_eq, Nat.cast_eq_zero]
    exact Finset.card_ne_zero.mpr ⟨v, by simp [Finset.mem_filter, Finset.mem_Ico, Hv0, Hvz, Set.mem_preimage]⟩
  · exact ENNReal.natCast_ne_top _

/-- Decompose `0 < (dirac a) {b}` into Cfg component equalities, then substitute. -/
macro "cfg_dirac" h:ident : tactic =>
  `(tactic| (rw [Discrete.dirac_singleton_pos] at $h:ident
             have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

/-- Countable-free `cfg_dirac`, using `dirac_singleton_pos'`. -/
macro "cfg_dirac'" h:ident : tactic =>
  `(tactic| (rw [dirac_singleton_pos'] at $h:ident
             have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

/-- Measurability-free `←` core for the `rand` constructors: every value in
`[0, z)` is a *possible* outcome of the uniform head step. The key point is that
this needs no `MeasurableSingletonClass rT` — `Possible.map` transports the fact
along the (measurable) `Int → Cfg rT` embedding, and the only singleton-mass
reasoning happens on `Int`, which is countable. -/
theorem Cfg.uniform_possible {z v : Int} {σ : State rT}
    (Hz : 0 < z) (Hv0 : 0 ≤ v) (Hvz : v < z) :
    Possible (⟨.lit (.int v), σ⟩ : Cfg rT) (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  simp only [Hz, dite_true]
  refine Possible.map (g := fun x : Int => (⟨.lit (.int x), σ⟩ : Cfg rT)) (ρ := v)
    (by measurability) ?_
  rw [possible_iff_pos, PMF.toMeasure_uniformOfFinset_apply _ _ (measurableSet_singleton v)]
  rw [ENNReal.div_pos_iff]
  refine ⟨?_, ENNReal.natCast_ne_top _⟩
  rw [ne_eq, Nat.cast_eq_zero]
  exact Finset.card_ne_zero.mpr ⟨v, by simp [Finset.mem_filter, Finset.mem_Ico, Hv0, Hvz]⟩

/-- A support point witnesses that the head step is nonzero. This is the
**universally-true** (measurability-free) fact every total-path caller needs
(`HeadReducible`, `headStep … ≠ 0`); it is the replacement for the atom-based
`HeadStepSupport.possible`, which is false for the diffuse continuous sampler.
The deterministic constructors reduce `headStep` to a `dirac` (nonzero, known to
`simp`); the discrete-`rand` constructors reduce to a `Cfg.uniform`
(`Cfg.uniform_possible.ne_zero`); and the continuous `urand` step is a
pushforward of the probability measure `unifUnit`, hence itself a probability
measure (`isProbabilityMeasure_map`) and so nonzero. -/
theorem HeadStepSupport.ne_zero {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩) :
    headStep ⟨e1, σ1⟩ ≠ 0 := by
  cases h with
  | UrandS _ =>
    have hg : Measurable (fun r : rT => (⟨.lit (.real r), σ1⟩ : Cfg rT)) := by
      rw [Cfg.measurable_iff]
      exact ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
    have hprob : IsProbabilityMeasure (headStep ⟨Exp.urand, σ1⟩) := by
      show IsProbabilityMeasure (Cfg.uniformReal σ1)
      rw [Cfg.uniformReal]; exact isProbabilityMeasure_map hg.aemeasurable
    exact hprob.ne_zero
  | BetaLamS hv he | BetaFixS hv he =>
    subst he; simp [headStep, Exp.isValM, hv]
  | IfTrueS | IfFalseS =>
    simp [headStep]
  | FstS hv1 hv2 | SndS hv1 hv2 =>
    simp [headStep, Exp.isValM, hv1, hv2]
  | CaseLS hv | CaseRS hv =>
    simp [headStep, Exp.isValM, hv]
  | UnOpS hv heval =>
    simp [headStep, Exp.isValM, hv, Option.unwrapM, ← heval]
  | BinOpS hv1 hv2 heval =>
    simp [headStep, Exp.isValM, hv1, hv2, Option.unwrapM, ← heval]
  | AllocS hvd hl hσ =>
    subst hl; subst hσ; simp [headStep, Exp.asValM, hvd]
  | LoadS hlook he =>
    subst he; simp [headStep, hlook]
  | StoreS hv hsome hσ =>
    subst hσ
    obtain ⟨vold, hvold⟩ := Option.isSome_iff_exists.mp hsome
    simp [headStep, Exp.asValM, hv, hvold]
  | TapeS hl hσ =>
    subst hl; subst hσ; simp [headStep]
  | ScrutSuccessS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]
  | ScrutFailureS hv hmatch =>
    simp [headStep, Exp.isValM, hv, hmatch]
  | RandNoTapeS Hz Hv0 Hvz =>
    simp only [headStep]; exact (Cfg.uniform_possible Hz Hv0 Hvz).ne_zero
  | RandNonposS Hz =>
    simp [headStep, Cfg.uniform, Int.isPos, Hz]
  | RandTapeS htape hz hv hσ =>
    subst hz; subst hv; subst hσ; simp [headStep, htape]
  | RandTapeEmptyS Hz htape hz Hv0 Hvz hσ =>
    subst hσ; subst hz; simp only [headStep, htape, ↓reduceIte]
    exact (Cfg.uniform_possible Hz Hv0 Hvz).ne_zero
  | RandTapeOtherS Hz htape hzN Hv0 Hvz hσ =>
    subst hσ; simp only [headStep, htape, if_neg (Ne.symm hzN)]
    exact (Cfg.uniform_possible Hz Hv0 Hvz).ne_zero
  | RandTapeNonposEmptyS Hz htape hz =>
    subst hz
    simp [headStep, htape, Cfg.uniform, Int.isPos, Hz]
  | RandTapeNonposOtherS Hz htape hzN =>
    simp [headStep, htape, if_neg (Ne.symm hzN), Cfg.uniform, Int.isPos, Hz]

/-- `→` direction of the continuous support characterisation. Unlike
`HeadStepSupport.possible`, this needs `[MeasurableSingletonClass rT]`: recovering
*which* outcome occurred from a positive-mass fact requires separating configs by
measurable sets, which on the `rT`-payload needs measurable singletons. **No
`[Countable rT]`**: the proof mirrors the `→` direction of
`Discrete.headStep_support_iff` but uses the Countable-free inversions
(`dirac_singleton_pos'`, `Cfg.uniform_singleton_pos_inv'`). -/
theorem headStep_support_of_pos [MeasurableSingletonClass rT]
    (e1 e2 : Exp rT) (σ1 σ2 : State rT) :
    0 < headStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} → HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ := by
  head_case
  all_goals try (· simp)
  case cond.true | cond.false => intro h; cfg_dirac' h; constructor
  case beta.lam.redex => intro h; cfg_dirac' h; exact .BetaLamS ‹_› rfl
  case beta.fix.redex => intro h; cfg_dirac' h; exact .BetaFixS ‹_› rfl
  case fst.redex => intro h; cfg_dirac' h; exact .FstS ‹_› ‹_›
  case snd.redex => intro h; cfg_dirac' h; exact .SndS ‹_› ‹_›
  case case.left.redex => intro h; cfg_dirac' h; exact .CaseLS ‹_›
  case case.right.redex => intro h; cfg_dirac' h; exact .CaseRS ‹_›
  case tape => intro h; cfg_dirac' h; exact .TapeS rfl rfl
  case load.redex => intro h; cfg_dirac' h; exact .LoadS ‹_› rfl
  case alloc.redex => intro h; cfg_dirac' h; exact .AllocS ‹_› rfl rfl
  case store.redex =>
    intro h; cfg_dirac' h
    exact .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl
  case rand.tape.deterministic =>
    intro h; cfg_dirac' h; exact .RandTapeS ‹_› rfl rfl rfl
  case unop.redex =>
    intro h; rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac' h; exact .UnOpS ‹_› hr.symm
  case binop.redex =>
    intro h; rw [unwrapM_singleton_pos] at h
    obtain ⟨r, hr, h⟩ := h; cfg_dirac' h; exact .BinOpS ‹_› ‹_› hr.symm
  case rand.plain =>
    intro h
    obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv' h
    simp at hσ; subst hσ
    rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
    · simp at hv; subst hv; exact .RandNoTapeS Hz Hv0 Hvz
    · simp at hv; subst hv; exact .RandNonposS Hz
  case rand.tape =>
    intro h
    obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv' h
    simp at hσ; subst hσ
    rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
    · simp at hv; subst hv; exact .RandTapeEmptyS Hz ‹_› rfl Hv0 Hvz rfl
    · simp at hv; subst hv; exact .RandTapeNonposEmptyS Hz ‹_› rfl
  case rand.tape.mismatch =>
    intro h
    obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv' h
    simp at hσ; subst hσ
    rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
    · simp at hv; subst hv; exact .RandTapeOtherS Hz ‹_› (Ne.symm ‹_›) Hv0 Hvz rfl
    · simp at hv; subst hv; exact .RandTapeNonposOtherS Hz ‹_› (Ne.symm ‹_›)
  case scrut_success => intro h; cfg_dirac' h; exact .ScrutSuccessS ‹_› ‹_›
  case scrut_failure => intro h; cfg_dirac' h; exact .ScrutFailureS ‹_› ‹_›
  case urand =>
    -- Continuous sampler: positive mass forces a real-literal outcome at the
    -- unchanged state. Inverts the pushforward `unifUnit.map (⟨.lit (.real ·), σ⟩)`
    -- via injectivity (`map_singleton_pos`) — no atoms/countability.
    rename_i _ σ' heq
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..) ▸ heq
    intro h
    have hg : Measurable (fun r : rT => (⟨.lit (.real r), σ1⟩ : Cfg rT)) := by
      rw [Cfg.measurable_iff]
      exact ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
    have hinj : Function.Injective (fun r : rT => (⟨.lit (.real r), σ1⟩ : Cfg rT)) := by
      intro a b hab; simp only [Cfg.mk.injEq, Exp.lit.injEq, BaseLit.real.injEq, and_true] at hab
      exact hab
    unfold Cfg.uniformReal at h
    obtain ⟨r, hr, hpos⟩ := map_singleton_pos hg hinj h
    rw [← hr]
    refine .UrandS (rT := rT) ?_
    -- `r` carries positive `unifUnit`-mass, so it lies in `unifUnitSupport`:
    -- otherwise `{r} ⊆ unifUnitSupportᶜ` would force `unifUnit {r} = 0`.
    by_contra hr_notin
    have hsub : ({r} : Set rT) ⊆ (ProbLangℝ.unifUnitSupport)ᶜ := by simpa using hr_notin
    exact (ne_of_gt hpos)
      (le_zero_iff.mp ((measure_mono hsub).trans_eq ProbLangℝ.unifUnitIsConcentrated))

/-- `→` direction of the continuous support characterisation. Needs
`[MeasurableSingletonClass rT]` (to recover *which* outcome occurred), but **not**
`[Countable rT]`. Routes through `possible_iff_pos` to `headStep_support_of_pos`. -/
theorem Possible.headStepSupport [MeasurableSingletonClass rT]
    {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : Possible (⟨e2, σ2⟩ : Cfg rT) (headStep ⟨e1, σ1⟩)) :
    HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ :=
  headStep_support_of_pos e1 e2 σ1 σ2 (possible_iff_pos.mp h)

/-- **Atomicity of `headStep` (countability-free).** A nonzero head step has
a support point: `headStep ⟨e, σ⟩` is always `0`, a `dirac`, or a
`Cfg.uniform`, so if it is nonzero it has some `HeadStepSupport` witness.
The `head_case` enumeration mirrors `headStep_support_of_pos`, but here the
witness is produced *structurally* from each branch (no positivity needed). -/
theorem headStep_exists_support_of_ne_zero
    {e : Exp rT} {σ : State rT} (h : headStep ⟨e, σ⟩ ≠ 0) :
    ∃ ρ', HeadStepSupport ⟨e, σ⟩ ρ' := by
  revert h
  head_case
  all_goals intro h
  all_goals try (exact absurd rfl h)
  case cond.true => exact ⟨_, .IfTrueS⟩
  case cond.false => exact ⟨_, .IfFalseS⟩
  case beta.lam.redex => exact ⟨_, .BetaLamS ‹_› rfl⟩
  case beta.fix.redex => exact ⟨_, .BetaFixS ‹_› rfl⟩
  case fst.redex => exact ⟨_, .FstS ‹_› ‹_›⟩
  case snd.redex => exact ⟨_, .SndS ‹_› ‹_›⟩
  case case.left.redex => exact ⟨_, .CaseLS ‹_›⟩
  case case.right.redex => exact ⟨_, .CaseRS ‹_›⟩
  case tape => exact ⟨_, .TapeS rfl rfl⟩
  case load.redex => exact ⟨_, .LoadS ‹_› rfl⟩
  case alloc.redex => exact ⟨_, .AllocS ‹_› rfl rfl⟩
  case store.redex =>
    exact ⟨_, .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl⟩
  case rand.tape.deterministic => exact ⟨_, .RandTapeS ‹_› rfl rfl rfl⟩
  case scrut_success => exact ⟨_, .ScrutSuccessS ‹_› ‹_›⟩
  case scrut_failure => exact ⟨_, .ScrutFailureS ‹_› ‹_›⟩
  case unop.redex =>
    simp only [Option.unwrapM] at h
    split at h
    · rename_i hv optx r heval
      exact ⟨⟨r, σ⟩, .UnOpS hv heval.symm⟩
    · exact absurd rfl h
  case binop.redex =>
    simp only [Option.unwrapM] at h
    split at h
    · rename_i hv1 hv2 optx r heval
      exact ⟨⟨r, σ⟩, .BinOpS hv1 hv2 heval.symm⟩
    · exact absurd rfl h
  case rand.plain =>
    rename_i z
    by_cases hz : 0 < z
    · exact ⟨_, .RandNoTapeS hz (le_refl 0) hz⟩
    · exact ⟨_, .RandNonposS hz⟩
  case rand.tape =>
    rename_i z α optT ns htape
    by_cases hz : 0 < z
    · exact ⟨_, .RandTapeEmptyS hz htape rfl (le_refl 0) hz rfl⟩
    · exact ⟨_, .RandTapeNonposEmptyS hz htape rfl⟩
  case rand.tape.mismatch =>
    rename_i z α optT N ns htape hne
    by_cases hz : 0 < z
    · exact ⟨_, .RandTapeOtherS hz htape (Ne.symm hne) (le_refl 0) hz rfl⟩
    · exact ⟨_, .RandTapeNonposOtherS hz htape (Ne.symm hne)⟩
  case urand =>
    rename_i _ σ' heq
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..) ▸ heq
    -- `unifUnit` is a probability measure concentrated on `unifUnitSupport`, so
    -- the support is nonempty; any of its points is a reachable real outcome.
    obtain ⟨r, hr⟩ := ProbLangℝ.unifUnitSupport_nonempty rT
    exact ⟨_, HeadStepSupport.UrandS (r := r) hr⟩

theorem isValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp α} {m : Measure T}
    (he : e.isValue) [IsProbabilityMeasure m] : IsProbabilityMeasure (e.isValM m) := by
  rw [Exp.isValM, if_pos he]; infer_instance

theorem asValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp α} {f : Val α → Measure T}
    {v : Val α} (hv : e.toVal? = some v) [IsProbabilityMeasure (f v)] :
    IsProbabilityMeasure (e.asValM f) := by
  simp [Exp.asValM, hv]; infer_instance

instance Cfg.uniform_isProbabilityMeasure {z : Int} {σ : State rT} :
    IsProbabilityMeasure (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  by_cases Hz : 0 < z
  · simp only [Hz, dite_true]
    exact Measure.isProbabilityMeasure_map (μ := (PMF.uniformOfFinset _ _).toMeasure)
      AEMeasurable.of_discrete
  · simp only [Hz, dite_false]; infer_instance

instance Cfg.uniformReal_isProbabilityMeasure {σ : State rT} :
    IsProbabilityMeasure (Cfg.uniformReal σ) := by
  unfold Cfg.uniformReal
  have hg : Measurable (fun r : rT => (⟨.lit (.real r), σ⟩ : Cfg rT)) := by
    rw [Cfg.measurable_iff]
    exact ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  exact Measure.isProbabilityMeasure_map hg.aemeasurable

theorem head_step_mass {e : Exp rT} {σ : State rT} :
    (headStep ⟨e, σ⟩ ≠ 0) → IsProbabilityMeasure (headStep ⟨e, σ⟩) := by
  head_case
  all_goals try (· simp)
  case beta.lam.redex | beta.fix.redex | cond.true | cond.false
     | fst.redex | snd.redex | case.left.redex | case.right.redex
     | alloc.redex | load.redex | store.redex | tape
     | rand.tape.deterministic
     | scrut_success | scrut_failure => intro _; infer_instance
  case unop.redex ρ op e H =>
    cases H : (op.eval e)
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case binop.redex ρ op e1 e2 H1 H2=>
    cases H : (op.eval e1 e2)
    · simp [Option.unwrapM]
    · simpa [Option.unwrapM] using dirac.isProbabilityMeasure
  case rand.plain | rand.tape | rand.tape.mismatch =>
    intro _; exact Cfg.uniform_isProbabilityMeasure
  case urand => intro _; exact Cfg.uniformReal_isProbabilityMeasure

/-! ### Pure atomicity of `headStep`

`headStep` (and hence `primStep`) is *purely atomic*: it assigns zero mass to the
set of points it gives zero mass to. This is the countability-free replacement for
the discrete `Pgl.zero_positive` (which used `Countable (Cfg rT)` to make the
co-support countable). The proof reduces every branch to `0`, a `dirac`, or a
`Cfg.uniform` — each of which is a `PMF.toMeasure`, and `PMF.toMeasure` is atomic
because its zero-set is exactly `(support)ᶜ`, disjoint from the support. -/

/-- A measure is *atomic* if it gives zero mass to its own null singletons. -/
def IsAtomicSupport {α : Type _} [MeasurableSpace α] (μ : Measure α) : Prop :=
  μ {x | μ {x} = 0} = 0

theorem isAtomicSupport_zero {α : Type _} [MeasurableSpace α] :
    IsAtomicSupport (0 : Measure α) := by simp [IsAtomicSupport]

/-- Every `PMF.toMeasure` is atomic: its null-singleton set is exactly the
complement of the (countable) support. -/
theorem PMF.toMeasure_isAtomicSupport {α : Type _} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) : IsAtomicSupport p.toMeasure := by
  unfold IsAtomicSupport
  have hset : {x : α | p.toMeasure {x} = 0} = (p.support : Set α)ᶜ := by
    ext x
    rw [Set.mem_setOf_eq, p.toMeasure_apply_singleton x (measurableSet_singleton x),
      Set.mem_compl_iff, PMF.mem_support_iff, not_not]
  rw [hset, p.toMeasure_apply_eq_zero_iff p.support_countable.measurableSet.compl]
  exact disjoint_compl_right

theorem isAtomicSupport_dirac {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : IsAtomicSupport (Measure.dirac a) := by
  unfold IsAtomicSupport
  refine measure_mono_null (t := {a}ᶜ) ?_ ?_
  · intro x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    rw [Set.mem_setOf_eq, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at hx
    exact one_ne_zero hx
  · rw [Measure.dirac_apply' _ (measurableSet_singleton a).compl, Set.indicator_of_notMem (by simp)]

omit [ProbLangℝ rT] in
theorem isAtomicSupport_isValM {T : Type _} [MeasurableSpace T] (e : Exp rT) {m : Measure T}
    (hm : IsAtomicSupport m) : IsAtomicSupport (e.isValM m) := by
  by_cases hv : e.isValue
  · rw [Exp.isValM_some hv]; exact hm
  · rw [Exp.isValM_none hv]; exact isAtomicSupport_zero

omit [ProbLangℝ rT] in
theorem isAtomicSupport_asValM {T : Type _} [MeasurableSpace T] (e : Exp rT)
    {f : Val rT → Measure T} (hf : ∀ v, IsAtomicSupport (f v)) :
    IsAtomicSupport (e.asValM f) := by
  unfold Exp.asValM
  split <;> first | exact isAtomicSupport_zero | exact hf _

theorem isAtomicSupport_unwrapM {β T : Type _} [MeasurableSpace T] (o : Option β)
    (f : β → Measure T) (hf : ∀ a, IsAtomicSupport (f a)) :
    IsAtomicSupport (o.unwrapM f) := by
  cases o with
  | none => simpa only [Option.unwrapM] using (isAtomicSupport_zero : IsAtomicSupport (0 : Measure T))
  | some a => simpa only [Option.unwrapM] using hf a

theorem isAtomicSupport_uniform (z : Int) (σ : State rT) :
    IsAtomicSupport (Cfg.uniform z σ) := by
  by_cases hz : 0 < z
  · have hrw : Cfg.uniform z σ
        = ((PMF.uniformOfFinset (Finset.Ico (0:Int) z) (Finset.nonempty_Ico.mpr hz)).map
            (fun n : Int => (⟨.lit (.int n), σ⟩ : Cfg rT))).toMeasure := by
      unfold Cfg.uniform
      simp only [Int.isPos, dif_pos hz]
      rw [PMF.toMeasure_map _ _ Measurable.of_discrete]
    rw [hrw]; exact PMF.toMeasure_isAtomicSupport _
  · have hrw : Cfg.uniform z σ = Measure.dirac (⟨.lit (.int (-1)), σ⟩ : Cfg rT) := by
      unfold Cfg.uniform; simp only [Int.isPos, dif_neg hz]
    rw [hrw]; exact isAtomicSupport_dirac _

set_option maxHeartbeats 1000000 in
/-- **`headStep` is purely atomic** for the *discrete* fragment. `@[discrete]`:
atomicity is a discrete notion — it is FALSE for the continuous sampler `urand`
(`Cfg.uniformReal` is diffuse when `unifUnit` is). The continuous WP path never
uses atomicity; it uses the `Concentrated`-on-image certificate instead. The
`urand` arm is therefore deferred (`sorry`) within the discrete fragment. -/
@[discrete]
theorem headStep_atomic (e : Exp rT) (σ : State rT) :
    IsAtomicSupport (headStep ⟨e, σ⟩) := by
  show IsAtomicSupport (headStep ⟨e, σ⟩)
  unfold headStep
  split
  case _ => apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- app lam
  case _ => apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- app fix
  case _ => -- unop
    apply isAtomicSupport_isValM; apply isAtomicSupport_unwrapM; intro _; exact isAtomicSupport_dirac _
  case _ => -- binop
    apply isAtomicSupport_isValM; apply isAtomicSupport_isValM
    apply isAtomicSupport_unwrapM; intro _; exact isAtomicSupport_dirac _
  case _ => exact isAtomicSupport_dirac _ -- cond.true
  case _ => exact isAtomicSupport_dirac _ -- cond.false
  case _ => apply isAtomicSupport_isValM; apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- fst
  case _ => apply isAtomicSupport_isValM; apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- snd
  case _ => apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- case inl
  case _ => apply isAtomicSupport_isValM; exact isAtomicSupport_dirac _ -- case inr
  case _ => apply isAtomicSupport_asValM; intro _; exact isAtomicSupport_dirac _ -- alloc
  case _ => -- load
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case _ => -- store
    apply isAtomicSupport_asValM; intro _
    split
    · exact isAtomicSupport_zero
    · exact isAtomicSupport_dirac _
  case _ => exact isAtomicSupport_uniform _ _ -- rand.plain
  case _ => exact isAtomicSupport_dirac _ -- tape
  case _ => -- rand.tape
    split
    · exact isAtomicSupport_zero
    · split
      · split
        · exact isAtomicSupport_uniform _ _
        · exact isAtomicSupport_dirac _
      · exact isAtomicSupport_uniform _ _
  case _ => -- scrut
    apply isAtomicSupport_isValM
    split <;> exact isAtomicSupport_dirac _
  case _ => sorry -- urand: Cfg.uniformReal is diffuse; atomicity false (discrete fragment)
  case _ => exact isAtomicSupport_zero -- default

/-! ### `Concentrated`: the unary support-lifting

`Concentrated μ S` says the measure `μ` lives on the set `S` — its complement is
`μ`-null. It is the unary degenerate of a relational coupling/lifting `μ ~_R ν`
(the relation collapsed to a one-sided predicate `S`), which is why it composes
like a coupling (`mono`, `map`, …). `IsAtomicSupport` is the special case where
`S` is the atom set (`IsAtomicSupport.concentrated_atoms`). This is the support
certificate the WP step rule needs, and — unlike atomicity — it survives diffuse
measures: a pushforward measure is always concentrated on the image of its source
support (`concentratedOn_map`). -/
def Concentrated {α : Type _} [MeasurableSpace α] (μ : Measure α) (S : Set α) : Prop :=
  μ Sᶜ = 0

theorem Concentrated.univ {α : Type _} [MeasurableSpace α] {μ : Measure α} :
    Concentrated μ Set.univ := by simp [Concentrated]

theorem concentratedOn_zero {α : Type _} [MeasurableSpace α] {S : Set α} :
    Concentrated (0 : Measure α) S := by simp [Concentrated]

/-- Enlarging the concentration set preserves concentration. -/
theorem Concentrated.mono {α : Type _} [MeasurableSpace α] {μ : Measure α} {S T : Set α}
    (hST : S ⊆ T) (h : Concentrated μ S) : Concentrated μ T :=
  MeasureTheory.measure_mono_null (Set.compl_subset_compl.mpr hST) h

/-- A `dirac` is concentrated on any (measurable) set containing its point. -/
theorem concentratedOn_dirac {α : Type _} [MeasurableSpace α] {a : α} {S : Set α}
    (hS : MeasurableSet S) (h : a ∈ S) : Concentrated (Measure.dirac a) S := by
  unfold Concentrated
  rw [Measure.dirac_apply' a hS.compl, Set.indicator_of_notMem (by simpa using h)]

/-- **The engine.** A pushforward `ν.map f` is concentrated on the image `f '' T`
of any set `T` carrying `ν` — needs only `Measurable f` and `MeasurableSet (f '' T)`.
Covers both `Cfg.uniform` (image of a finite PMF) and a future `Cfg.uniformReal`
(image of a continuous uniform), uniformly. -/
theorem concentratedOn_map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) {ν : Measure α} {T : Set α}
    (hfT : MeasurableSet (f '' T)) (h : Concentrated ν T) :
    Concentrated (ν.map f) (f '' T) := by
  unfold Concentrated at h ⊢
  rw [Measure.map_apply hf hfT.compl]
  refine MeasureTheory.measure_mono_null (fun x hx => ?_) h
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxT => hx ⟨x, hxT, rfl⟩

/-- `IsAtomicSupport` is exactly concentration on the atom set. This recovers the
existing atomicity machinery as a `Concentrated` instance. -/
theorem IsAtomicSupport.concentrated_atoms {α : Type _} [MeasurableSpace α]
    {μ : Measure α} (h : IsAtomicSupport μ) : Concentrated μ {x | 0 < μ {x}} := by
  have hset : {x | 0 < μ {x}}ᶜ = {x | μ {x} = 0} := by
    ext x; simp [Set.mem_compl_iff, not_lt, nonpos_iff_eq_zero]
  rw [Concentrated, hset]; exact h

/-- `headStep` is a sub-probability measure for arbitrary `rT`: by case analysis,
each branch returns either `0`, a `dirac`, or a probability measure (gated by
`isValM`/`asValM`/`unwrapM` which only ever shrink mass). -/
theorem headStep_univ_le_one' (ρ : Cfg rT) : (headStep ρ) Set.univ ≤ 1 := by
  -- Helper: isValM-univ shrinks mass.
  have hisValM_le : ∀ {T : Type _} [MeasurableSpace T] (e : Exp rT) (m : Measure T),
      m Set.univ ≤ 1 → (e.isValM m) Set.univ ≤ 1 := by
    intro T _ e m hm
    by_cases hv : e.isValue
    · rw [Exp.isValM_some hv]; exact hm
    · rw [Exp.isValM_none hv]; simp
  have hasValM_le : ∀ {T : Type _} [MeasurableSpace T] (e : Exp rT) (f : Val rT → Measure T),
      (∀ v, (f v) Set.univ ≤ 1) → (e.asValM f) Set.univ ≤ 1 := by
    intro T _ e f hf
    unfold Exp.asValM
    rcases hv : e.toVal? with _ | v
    · simp
    · exact hf v
  have hunwrapM_le : ∀ {α T : Type _} [MeasurableSpace T] (o : Option α) (f : α → Measure T),
      (∀ a, (f a) Set.univ ≤ 1) → (o.unwrapM f) Set.univ ≤ 1 := by
    intro α T _ o f hf
    cases o
    · simp [Option.unwrapM]
    · simp [Option.unwrapM]; exact hf _
  have hdirac : ∀ {T : Type _} [MeasurableSpace T] (x : T), (Measure.dirac x) Set.univ ≤ 1 := by
    intro T _ x
    rw [Measure.dirac_apply' _ MeasurableSet.univ]; simp
  have huniform : ∀ z (σ : State rT), (Cfg.uniform z σ) Set.univ ≤ 1 := by
    intro z σ
    have := @Cfg.uniform_isProbabilityMeasure rT _ z σ
    exact this.measure_univ.le
  obtain ⟨e, σ⟩ := ρ
  set_option maxHeartbeats 1000000 in
  show (headStep ⟨e, σ⟩) Set.univ ≤ 1
  unfold headStep
  split
  case _ => -- app (.lam _) _
    apply hisValM_le; apply hdirac
  case _ => -- app (.fix _) _
    apply hisValM_le; apply hdirac
  case _ => -- unop
    apply hisValM_le; apply hunwrapM_le; intro _; apply hdirac
  case _ => -- binop
    apply hisValM_le; apply hisValM_le; apply hunwrapM_le; intro _; apply hdirac
  case _ => apply hdirac -- cond.true
  case _ => apply hdirac -- cond.false
  case _ => apply hisValM_le; apply hisValM_le; apply hdirac -- fst.pair
  case _ => apply hisValM_le; apply hisValM_le; apply hdirac -- snd.pair
  case _ => apply hisValM_le; apply hdirac -- case.inl
  case _ => apply hisValM_le; apply hdirac -- case.inr
  case _ => apply hasValM_le; intro _; apply hdirac -- alloc
  case _ => -- load
    split
    · simp
    · apply hdirac
  case _ => -- store
    apply hasValM_le; intro _
    split
    · simp
    · apply hdirac
  case _ => apply huniform -- rand.plain
  case _ => apply hdirac -- tape
  case _ => -- rand.tape
    split
    · simp
    · split
      · split
        · apply huniform
        · apply hdirac
      · apply huniform
  case _ => -- scrut
    apply hisValM_le
    split <;> apply hdirac
  case _ => exact Cfg.uniformReal_isProbabilityMeasure.measure_univ.le -- urand
  case _ => simp -- default

set_option maxHeartbeats 400000
-- TODO: This other theorem is proved, but I do think that the below commented out proof
-- might let us delete it (the primed version is horrible)
theorem headStep_univ_le_one (ρ : Cfg rT) : (headStep ρ) Set.univ ≤ 1 :=
  headStep_univ_le_one' ρ

  -- by_cases hred : (headStep ρ) = 0
  -- · simp [hred]
  -- · have X := head_step_mass hred
  --   sorry

end ProbLang
