module

public import Metrology.ProbLang.CoreMeasures
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

omit [ProbLangℝ rT] in
@[simp] theorem Exp.isValM_some [MeasurableSpace T] {e : Exp rT} {m : Measure T} (He : e.isValue) :
    e.isValM m = m := if_pos He

theorem Exp.isValM_some' [MeasurableSpace T] {e : Exp rT} {m : Measure T} (w : IsVal e) :
    e.isValM m = m := isValM_some w.toIsValue

omit [ProbLangℝ rT] in
@[simp] theorem Exp.isValM_none [MeasurableSpace T] {e : Exp rT} {m : Measure T} (He : ¬ e.isValue) :
    e.isValM m = 0 := if_neg He

def Int.isPos (z : Int) : Option { z : Int // 0 < z } :=
  if H : 0 < z then some ⟨z, H⟩ else none


/-- `Cfg.uniform z σ` is the measure putting uniform mass on configs
`⟨.lit (.int n), σ⟩` for `n ∈ {0, 1, …, z−1}` (i.e. `Finset.Ico 0 z`),
matching the semantics of `rand z` sampling from `{0, …, z−1}`. The
state fiber is constant at `σ`. If `z ≤ 0`, the measure is the dirac
on `⟨.lit (.int (-1)), σ⟩` — `rand` on a non-positive bound is total
and returns the sentinel value `-1`. -/
def Cfg.uniform (z : Int) (σ : State rT) : Measure (Cfg rT) :=
  match z.isPos with
  | some ⟨z, Hz⟩ =>
    PMF.uniformOfFinset (.Ico 0 z) (Finset.nonempty_Ico.mpr Hz)
      |>.toMeasure.map (⟨.lit <| .int ·, σ⟩)
  | none => dirac ⟨.lit (.int (-1)), σ⟩

-- TODO: What if we change Cfg to Option (Exp × State)?
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
    on_goal 18 => rename_goal default
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

def headStepKernel [Countable rT] [MeasurableSingletonClass rT] :
    Kernel (Cfg rT) (Cfg rT) where
  measurable' := .of_discrete
  toFun := headStep

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
           {e : Exp rT | e.isValueR} ×ˢ (Set.univ : Set (Measure T)) := by
      ext ⟨e, m⟩; simp [Exp.isValue_iff_isValueR]
    rw [this]
    exact (Exp.isValueR.measurable.setOf).prod MeasurableSet.univ
  refine Measurable.ite hpred ?_ ?_
  · -- True branch: `fun p => p.2`. Measurable as `measurable_snd`.
    exact measurable_snd
  · -- False branch: constant `0`.
    exact measurable_const

/-- **Per-callsite joint `Exp.isValM`**.

Stamping convenience: given measurable extractors `he : γ → Exp rT` and
`hm : γ → Measure T`, `c ↦ (he c).isValM (hm c)` is measurable. Direct
composition with `Exp.isValM.measurable`. -/
theorem Exp.isValM.measurable_param {T γ : Type _} [MeasurableSpace T] [MeasurableSpace γ]
    {he : γ → Exp rT} (hhe : Measurable he)
    {hm : γ → Measure T} (hhm : Measurable hm) :
    Measurable (fun c : γ => (he c).isValM (hm c)) :=
  Exp.isValM.measurable.comp (hhe.prodMk hhm)

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
  -- Strategy: outer split on `z : Int` (countable + ⊤) via
  -- `measurable_from_prod_countable_right`. The `z ≤ 0` branch reduces to
  -- dirac-measurability in `σ`; the `z > 0` branch needs measurability of
  -- the parameterized pushforward `σ ↦ pmf.toMeasure.map (.lit (.int ·), σ)`.
  -- Latter requires a Mathlib lemma about parameterized `Measure.map`; left
  -- as `sorry` pending that.
  sorry

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
    measurable_dirac.comp (Cfg.measurable_mk.comp
      (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
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
            (fun _ => 0) (fun _ _ => 0) 0 (fun _ _ => 0))
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
        (fun _ => 0) (fun _ _ => 0) 0 (fun _ _ => 0)) := by
    apply Exp.measurable_rec_param
      (β := State rT × Exp rT) (α := Measure (Cfg rT))
      (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
      (c_lam := c_lam_inner) (c_fix := c_fix_inner)
      (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
      (c_cond := fun _ => 0) (c_pair := fun _ => 0)
      (c_fst := fun _ => 0) (c_snd := fun _ => 0)
      (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ => 0)
      (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
      (c_tape := fun _ => 0) (c_rand := fun _ => 0)
      (c_fail := fun _ => 0) (c_scrut := fun _ => 0)
    · exact measurable_const  -- c_bvar
    · exact measurable_const  -- c_fvar
    · exact measurable_const  -- c_lit
    · -- c_lam_inner: isValM (e2 := q.1.2) of dirac. Joint in q.
      refine Exp.isValM.measurable_param
        (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
        (hm := fun q : (State rT × Exp rT) × Exp rT =>
                  (dirac (Cfg.mk (Exp.open' q.2 q.1.2) q.1.1) : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_fst
      · refine measurable_dirac.comp ?_
        rw [Cfg.measurable_iff]
        refine ⟨?_, ?_⟩
        · show Measurable (fun q : (State rT × Exp rT) × Exp rT => Exp.open' q.2 q.1.2)
          exact Exp.open'.measurable.comp
            (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
        · show Measurable (fun q : (State rT × Exp rT) × Exp rT => q.1.1)
          exact measurable_fst.comp measurable_fst
    · -- c_fix_inner: isValM of dirac of app (open' e1 (fix e1)) e2.
      refine Exp.isValM.measurable_param
        (he := fun q : (State rT × Exp rT) × Exp rT => q.1.2)
        (hm := fun q : (State rT × Exp rT) × Exp rT =>
                  (dirac (Cfg.mk
                    (Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2) q.1.1)
                    : Measure (Cfg rT)))
        ?_ ?_
      · exact measurable_snd.comp measurable_fst
      · refine measurable_dirac.comp ?_
        rw [Cfg.measurable_iff]
        refine ⟨?_, ?_⟩
        · show Measurable
            (fun q : (State rT × Exp rT) × Exp rT =>
              Exp.app (Exp.open' q.2 (.fix q.2)) q.1.2)
          refine Exp.app.measurable.comp (Measurable.prodMk ?_ ?_)
          · refine Exp.open'.measurable.comp (Measurable.prodMk measurable_snd ?_)
            exact Exp.fix.measurable.comp measurable_snd
          · exact measurable_snd.comp measurable_fst
        · show Measurable (fun q : (State rT × Exp rT) × Exp rT => q.1.1)
          exact measurable_fst.comp measurable_fst
    all_goals exact measurable_const
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
    refine measurable_dirac.comp ?_
    rw [Cfg.measurable_iff]
    refine ⟨?_, ?_⟩
    · show Measurable (fun q : State rT × Val rT =>
          (Exp.lit (.loc q.1.heap.fresh) : Exp rT))
      refine Exp.lit.measurable.comp (BaseLit.loc.measurable.comp ?_)
      exact LocHeap.measurable_fresh.comp (State.measurable_heap.comp measurable_fst)
    · show Measurable (fun q : State rT × Val rT =>
          (q.1.update_heap (·.insert q.1.heap.fresh q.2)))
      rw [State.measurable_iff]
      refine ⟨?_, ?_⟩
      · -- show Measurable (fun q : State rT × Val rT =>
        --   q.1.heap.insert q.1.heap.fresh q.2)
        -- = locHeap_insert_param applied to triple (q.1.heap, q.1.heap.fresh, q.2).
        have hheap : Measurable (fun q : State rT × Val rT => q.1.heap) :=
          State.measurable_heap.comp measurable_fst
        have hfresh : Measurable (fun q : State rT × Val rT => q.1.heap.fresh) :=
          LocHeap.measurable_fresh.comp hheap
        have hval : Measurable (fun q : State rT × Val rT => q.2) := measurable_snd
        have hpair : Measurable (fun q : State rT × Val rT =>
            (q.1.heap, q.1.heap.fresh, q.2) : State rT × Val rT → LocHeap (Val rT) × Loc × Val rT) :=
          hheap.prodMk (hfresh.prodMk hval)
        exact (Measurable.locHeap_insert_param (V := Val rT)).comp hpair
      · show Measurable (fun q : State rT × Val rT => q.1.tapes)
        exact State.measurable_tapes.comp measurable_fst
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
            (fun _ => 0) (fun _ _ => 0) 0 (fun _ _ => 0))
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
  have hinner : Measurable (fun q : Exp rT × (State rT × Exp rT × Exp rT) =>
      Exp.casesOn (motive := fun _ => Measure (Cfg rT)) q.1
        (fun _ => 0) (fun _ => 0)
        (fun l => c_lit_inner (q.2, l))
        (fun _ => 0) (fun _ => 0)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
        (fun _ => 0) (fun _ _ => 0) 0 (fun _ _ => 0)) := by
    apply Exp.measurable_rec_param
      (β := State rT × Exp rT × Exp rT) (α := Measure (Cfg rT))
      (c_bvar := fun _ => 0) (c_fvar := fun _ => 0)
      (c_lit := c_lit_inner)
      (c_lam := fun _ => 0) (c_fix := fun _ => 0)
      (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
      (c_cond := fun _ => 0) (c_pair := fun _ => 0)
      (c_fst := fun _ => 0) (c_snd := fun _ => 0)
      (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ => 0)
      (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
      (c_tape := fun _ => 0) (c_rand := fun _ => 0)
      (c_fail := fun _ => 0) (c_scrut := fun _ => 0)
    · exact measurable_const
    · exact measurable_const
    · -- c_lit_inner: dispatch on BaseLit, only `.bool` is non-zero.
      -- Within `.bool`, further case on bool: true → dirac et, false → dirac ef.
      -- Use BaseLit.measurable_rec_param.
      -- c_lit_inner q = match q.2 with
      --   | .bool true => dirac ⟨q.1.2.1, q.1.1⟩
      --   | .bool false => dirac ⟨q.1.2.2, q.1.1⟩
      --   | _ => 0
      -- Reshape to BaseLit.measurable_rec_param shape:
      -- `(p : BaseLit rT × β) ↦ casesOn p.1 ... p.2 threaded`.
      -- β = (State rT × Exp rT × Exp rT).
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
      apply BaseLit.measurable_rec_param
        (β := State rT × Exp rT × Exp rT) (α := Measure (Cfg rT))
        (c_int := fun _ => 0) (c_bool := c_bool_inner)
        (c_unit := fun _ => 0) (c_loc := fun _ => 0)
        (c_lbl := fun _ => 0) (c_real := fun _ => 0)
      · exact measurable_const
      · -- c_bool_inner measurability
        show Measurable (fun r : (State rT × Exp rT × Exp rT) × Bool =>
          if r.2 then (dirac ⟨r.1.2.1, r.1.1⟩ : Measure (Cfg rT))
                  else dirac ⟨r.1.2.2, r.1.1⟩)
        refine Measurable.ite ?_ ?_ ?_
        · -- `r.2` is the bool itself; the predicate is `r.2 = true` which is just r.2.
          -- {r | r.2} = (fun r => r.2) ⁻¹' {true}, measurable as preimage of {true}.
          exact MeasurableSet.preimage (measurableSet_singleton true) measurable_snd
        · -- True branch: dirac ⟨r.1.2.1, r.1.1⟩
          refine measurable_dirac.comp ?_
          rw [Cfg.measurable_iff]
          refine ⟨?_, ?_⟩
          · show Measurable
              (fun r : (State rT × Exp rT × Exp rT) × Bool => r.1.2.1)
            exact (measurable_fst.comp measurable_snd).comp measurable_fst
          · show Measurable
              (fun r : (State rT × Exp rT × Exp rT) × Bool => r.1.1)
            exact measurable_fst.comp measurable_fst
        · -- False branch: dirac ⟨r.1.2.2, r.1.1⟩
          refine measurable_dirac.comp ?_
          rw [Cfg.measurable_iff]
          refine ⟨?_, ?_⟩
          · show Measurable
              (fun r : (State rT × Exp rT × Exp rT) × Bool => r.1.2.2)
            exact (measurable_snd.comp measurable_snd).comp measurable_fst
          · show Measurable
              (fun r : (State rT × Exp rT × Exp rT) × Bool => r.1.1)
            exact measurable_fst.comp measurable_fst
      · exact measurable_const
      · exact measurable_const
      · exact measurable_const
      · exact measurable_const
    all_goals exact measurable_const
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
  -- Same pattern as `c_app`: nested rec on `ec` via Exp.measurable_rec_param.
  sorry

/-- `load` branch: dispatch on `e`, `.lit (.loc ℓ)` non-trivial, then heap lookup. -/
@[simp] def headStep.c_load (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.loc ℓ) => match p.1.heap[ℓ]? with
                      | none => 0
                      | some v => dirac ⟨Exp.ofVal v, p.1⟩
  | _ => 0

theorem headStep.c_load.measurable [Inhabited rT] :
    Measurable (headStep.c_load (rT := rT)) := by
  -- Nested rec on `e`; inner BaseLit dispatch on `.loc ℓ`; further dispatch on
  -- heap lookup. Two-level pattern match analogous to UnOp.eval's structure.
  sorry

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
  -- Same pattern as c_load, plus asValM for the inner `e2` continuation.
  sorry

/-- `tape` branch: dispatch on `e`, `.lit (.int z)` non-trivial. -/
@[simp] def headStep.c_tape (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .lit (.int z) =>
    let α := p.1.tapes.fresh
    dirac ⟨.lit (.lbl α), p.1.update_tapes (·.insert α (.empty z))⟩
  | _ => 0

theorem headStep.c_tape.measurable [Inhabited rT] :
    Measurable (headStep.c_tape (rT := rT)) := by
  -- Nested rec on `e` with BaseLit dispatch on `.int z`.
  sorry

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
  -- Doubly-nested rec on (e1, e2). Most complex of the 13 branches; uses
  -- Cfg.uniform.measurable (stub) + LocHeap lookup.
  sorry

/-- `scrut` branch: `e.isValM` of dispatch on `Pat.tryMatch p e`. -/
@[simp] def headStep.c_scrut (p : State rT × Exp rT × Pat rT) : Measure (Cfg rT) :=
  p.2.1.isValM
    (match Pat.tryMatch p.2.2 p.2.1 with
      | some b => dirac ⟨.inl b, p.1⟩
      | none => dirac ⟨.inr (.lit .unit), p.1⟩)

theorem headStep.c_scrut.measurable [ProbLangℝ rT] :
    Measurable (headStep.c_scrut (rT := rT)) := by
  -- isValM_param + Option.unwrapM_param-style + tryMatch.measurable (stub).
  sorry

/-- `fst (pair e1 e2)` branch: nested rec on subterm. -/
@[simp] def headStep.c_fst (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e1, p.1⟩))
  | _ => 0

theorem headStep.c_fst.measurable :
    Measurable (headStep.c_fst (rT := rT)) := by
  -- Pattern: nested rec on `e` via `Exp.measurable_rec_param`, β := State rT,
  -- only the `.pair` continuation is non-trivial; identical proof shape to `c_app`.
  -- (Currently times out on the giant `apply`; pattern is settled, just slow.)
  sorry

/-- `snd (pair e1 e2)` branch: same shape as `c_fst`, projects e2. -/
@[simp] def headStep.c_snd (p : State rT × Exp rT) : Measure (Cfg rT) :=
  match p.2 with
  | .pair e1 e2 => e1.isValM (e2.isValM (dirac ⟨e2, p.1⟩))
  | _ => 0

theorem headStep.c_snd.measurable :
    Measurable (headStep.c_snd (rT := rT)) := by
  -- Same pattern as `c_fst.measurable`.
  sorry

/-- `binop` branch: `e1.isValM (e2.isValM ((op.eval e1 e2).unwrapM (·, σ)))`. -/
@[simp] def headStep.c_binop (p : State rT × BinOp × Exp rT × Exp rT) : Measure (Cfg rT) :=
  p.2.2.1.isValM (p.2.2.2.isValM
    ((p.2.1.eval p.2.2.1 p.2.2.2).unwrapM (fun e' => dirac ⟨e', p.1⟩)))

theorem headStep.c_binop.measurable [ProbLangℝ rT] :
    Measurable (headStep.c_binop (rT := rT)) := by
  -- Same shape as c_unop, with one extra inner `isValM`.
  have hoe : Measurable
      (fun p : State rT × BinOp × Exp rT × Exp rT => p.2.1.eval p.2.2.1 p.2.2.2) :=
    Exp.BinOp_eval.measurable.comp measurable_snd
  have hdir : Measurable
      (fun q : (State rT × BinOp × Exp rT × Exp rT) × Exp rT =>
        (dirac (Cfg.mk q.2 q.1.1) : Measure (Cfg rT))) :=
    measurable_dirac.comp (Cfg.measurable_mk.comp
      (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
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
          (fun e pat => c_scrut (p.2, e, pat)) := by
    funext ⟨e, σ⟩
    -- Equate headStep on each Exp shape with the corresponding continuation.
    -- For branches that further case-split (app, cond, fst, snd, case, load,
    -- store, tape, rand, scrut), inner `cases` matches headStep's nested
    -- pattern. Cases that don't pattern-match on subterms close by `rfl`.
    cases e with
    | bvar | fvar | lit | lam | fix | fail => rfl
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
    (c_fail := c_fail) (c_scrut := c_scrut)
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
  -- c_scrut: isValM + tryMatch.
  · exact headStep.c_scrut.measurable

/-- Markov kernel of the head step, without the discrete-`rT` hypotheses. -/
def headStepKernelM : Kernel (Cfg rT) (Cfg rT) where
  measurable' := headStep.measurable
  toFun := headStep


theorem val_head_stuck {e : Exp rT} {σ : State rT} {ρ : Cfg rT} :
    0 < headStep ⟨e, σ⟩ {ρ} → ¬e.isValue := by
  head_case <;> simp [Exp.isValue_iff_isValueR]

omit [ProbLangℝ rT] in
theorem Exp.toVal?_isValue {e : Exp rT} : e.toVal? = some v → e.isValue := by
  intro h; by_contra hne; rw [Exp.toVal?_eq_none.mpr hne] at h; exact absurd h (by simp)

theorem head_ctx_step_val {e : Exp rT} {σ : State rT} {ρ : Cfg rT} {Ki : EctxItem rT} :
    0 < headStep ⟨Ki.fillItem e, σ⟩ {ρ} → e.isValue := by
  -- Original (times out at `whnf` after rT parameterization; revisit):
  -- have Hzero : (0 < (0 : Measure (Cfg rT)) {ρ}) → False := by simp
  -- head_case
  -- all_goals try (exact fun H => (Hzero H).elim)
  -- all_goals cases Ki <;> (intro _; simp_all [EctxItem.fillItem, Exp.isValue_iff_isValueR])
  -- all_goals exact (Exp.isValue_iff_isValueR.mp (Exp.toVal?_isValue ‹_›))
  sorry

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

@[simp]
theorem dirac_singleton_pos [Countable rT] [MeasurableSingletonClass rT]
    {a b : Cfg rT} :
    0 < (dirac a) {b} ↔ a = b := by
  constructor
  · rw [dirac_apply' a .of_discrete, Set.indicator_singleton, Pi.single, Function.update]
    split <;> simp; trivial
  · simp_all [dirac_apply_of_mem (Set.mem_singleton _)]

omit [ProbLangℝ rT] in
@[simp]
theorem isValM_singleton_pos [MeasurableSpace T] {e : Exp rT} {m : Measure T} {s : Set T} :
    0 < (e.isValM m) s ↔ e.isValue ∧ 0 < m s := by
  simp only [Exp.isValM]
  by_cases He : e.isValue
  · rw [if_pos He]; exact ⟨fun h => ⟨He, h⟩, And.right⟩
  · rw [if_neg He]; exact ⟨fun h => absurd h (by simp), fun ⟨hv, _⟩ => absurd hv He⟩

@[simp]
theorem unwrapM_singleton_pos {α β : Type _} [MeasurableSpace β]
    {f : α → Measure β} {opt : Option α} {s : Set β} :
    0 < (opt.unwrapM f) s ↔ ∃ a, opt = some a ∧ 0 < (f a) s := by
  cases opt <;> simp [Option.unwrapM]

omit [ProbLangℝ rT] in
@[simp]
theorem asValM_singleton_pos [MeasurableSpace T] {e : Exp rT} {f : Val rT → Measure T} :
    0 < (e.asValM f) s ↔ ∃ v, e.toVal? = some v ∧ 0 < (f v) s := by
  unfold Exp.asValM; cases e.toVal? <;> simp

theorem Cfg.uniform_singleton_pos_inv [Countable rT] [MeasurableSingletonClass rT]
    {z : Int} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < Cfg.uniform z σ {ρ}) :
    ρ.state = σ ∧
    ((0 < z ∧ ∃ v : Int, ρ.expr = .lit (.int v) ∧ 0 ≤ v ∧ v < z) ∨
     (¬ 0 < z ∧ ρ.expr = .lit (.int (-1)))) := by
  unfold Cfg.uniform Int.isPos at h
  by_cases Hz : 0 < z
  · simp only [Hz, dite_true] at h
    simp [Measure.map_apply .of_discrete .of_discrete] at h
    obtain ⟨_, _, _, rfl⟩ := h
    refine ⟨rfl, .inl ⟨Hz, _, rfl, ?_, ?_⟩⟩ <;> simp_all
  · simp only [Hz, dite_false] at h
    rw [dirac_singleton_pos] at h
    have ⟨h1, h2⟩ := (Cfg.mk.injEq ..).mp h
    exact ⟨h2.symm, .inr ⟨Hz, h1.symm⟩⟩

theorem Cfg.uniform_singleton_pos_of_mem [Countable rT] [MeasurableSingletonClass rT]
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

theorem Cfg.uniform_singleton_nonpos [Countable rT] [MeasurableSingletonClass rT]
    {z : Int} {σ : State rT} (Hz : ¬ 0 < z) :
    0 < Cfg.uniform z σ {⟨.lit (.int (-1)), σ⟩} := by
  unfold Cfg.uniform Int.isPos
  simp only [Hz, dite_false]
  rw [dirac_singleton_pos]

/-- Decompose `0 < (dirac a) {b}` into Cfg component equalities, then substitute. -/
macro "cfg_dirac" h:ident : tactic =>
  `(tactic| (rw [dirac_singleton_pos] at $h:ident
             have ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp $h:ident))

theorem headStep_support_iff [Countable rT] [MeasurableSingletonClass rT]
    (e1 e2 : Exp rT) (σ1 σ2 : State rT) :
    0 < headStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} ↔ HeadStepSupport ⟨e1, σ1⟩ ⟨e2, σ2⟩ := by
  constructor
  · head_case
    all_goals try (· simp)
    case cond.true | cond.false => intro h; cfg_dirac h; constructor
    case beta.lam.redex => intro h; cfg_dirac h; exact .BetaLamS ‹_› rfl
    case beta.fix.redex => intro h; cfg_dirac h; exact .BetaFixS ‹_› rfl
    case fst.redex => intro h; cfg_dirac h; exact .FstS ‹_› ‹_›
    case snd.redex => intro h; cfg_dirac h; exact .SndS ‹_› ‹_›
    case case.left.redex => intro h; cfg_dirac h; exact .CaseLS ‹_›
    case case.right.redex => intro h; cfg_dirac h; exact .CaseRS ‹_›
    case tape => intro h; cfg_dirac h; exact .TapeS rfl rfl
    case load.redex => intro h; cfg_dirac h; exact .LoadS ‹_› rfl
    case alloc.redex => intro h; cfg_dirac h; exact .AllocS ‹_› rfl rfl
    case store.redex =>
      intro h; cfg_dirac h
      exact .StoreS ‹_› (by rw [Option.isSome_iff_exists]; exact ⟨_, ‹_›⟩) rfl
    case rand.tape.deterministic =>
      intro h; cfg_dirac h; exact .RandTapeS ‹_› rfl rfl rfl
    case unop.redex =>
      intro h; rw [unwrapM_singleton_pos] at h
      obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .UnOpS ‹_› hr.symm
    case binop.redex =>
      intro h; rw [unwrapM_singleton_pos] at h
      obtain ⟨r, hr, h⟩ := h; cfg_dirac h; exact .BinOpS ‹_› ‹_› hr.symm
    case rand.plain =>
      intro h
      obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hσ; subst hσ
      rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
      · simp at hv; subst hv; exact .RandNoTapeS Hz Hv0 Hvz
      · simp at hv; subst hv; exact .RandNonposS Hz
    case rand.tape =>
      intro h
      obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hσ; subst hσ
      rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
      · simp at hv; subst hv; exact .RandTapeEmptyS Hz ‹_› rfl Hv0 Hvz rfl
      · simp at hv; subst hv; exact .RandTapeNonposEmptyS Hz ‹_› rfl
    case rand.tape.mismatch =>
      intro h
      obtain ⟨hσ, hbr⟩ := Cfg.uniform_singleton_pos_inv h
      simp at hσ; subst hσ
      rcases hbr with ⟨Hz, v, hv, Hv0, Hvz⟩ | ⟨Hz, hv⟩
      · simp at hv; subst hv; exact .RandTapeOtherS Hz ‹_› (Ne.symm ‹_›) Hv0 Hvz rfl
      · simp at hv; subst hv; exact .RandTapeNonposOtherS Hz ‹_› (Ne.symm ‹_›)
    case scrut_success => intro h; cfg_dirac h; exact .ScrutSuccessS ‹_› ‹_›
    case scrut_failure => intro h; cfg_dirac h; exact .ScrutFailureS ‹_› ‹_›
  · intro hsupp
    cases hsupp with
    | BetaLamS | BetaFixS | IfTrueS | IfFalseS | FstS |SndS | CaseLS | CaseRS | LoadS
    | TapeS | RandTapeS | AllocS | StoreS
    | ScrutSuccessS | ScrutFailureS =>
      simp_all [headStep]
    | RandNoTapeS | RandTapeEmptyS =>
      simp_all [headStep, Cfg.uniform_singleton_pos_of_mem]
    | UnOpS _ heval | BinOpS _ _ heval =>
      simp_all [headStep]
      exact ⟨_, heval.symm, by simp⟩
    | RandTapeOtherS Hz htape hzN Hv0 Hvz hσ =>
      subst hσ
      simp only [headStep, htape]
      split
      · next hM => rw [hM] at hzN; exact absurd rfl hzN
      · exact Cfg.uniform_singleton_pos_of_mem Hz Hv0 Hvz
    | RandNonposS Hz =>
      simp only [headStep]; exact Cfg.uniform_singleton_nonpos Hz
    | RandTapeNonposEmptyS Hz htape hzN =>
      subst hzN
      simp only [headStep, htape, ↓reduceIte]
      exact Cfg.uniform_singleton_nonpos Hz
    | RandTapeNonposOtherS Hz htape hzN =>
      simp only [headStep, htape]
      rw [if_neg (Ne.symm hzN)]
      exact Cfg.uniform_singleton_nonpos Hz

omit [ProbLangℝ rT] in
theorem isValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp rT} {m : Measure T}
    (he : e.isValue) [IsProbabilityMeasure m] : IsProbabilityMeasure (e.isValM m) := by
  rw [Exp.isValM, if_pos he]; infer_instance

omit [ProbLangℝ rT] in
theorem asValM_isProbabilityMeasure [MeasurableSpace T] {e : Exp rT} {f : Val rT → Measure T}
    {v : Val rT} (hv : e.toVal? = some v) [IsProbabilityMeasure (f v)] :
    IsProbabilityMeasure (e.asValM f) := by
  simp [Exp.asValM, hv]; infer_instance

theorem Cfg.uniform_isProbabilityMeasure [Countable rT] [MeasurableSingletonClass rT]
    {z : Int} {σ : State rT} :
    IsProbabilityMeasure (Cfg.uniform z σ) := by
  unfold Cfg.uniform Int.isPos
  by_cases Hz : 0 < z
  · simp only [Hz, dite_true]
    exact Measure.isProbabilityMeasure_map (μ := (PMF.uniformOfFinset _ _).toMeasure)
      AEMeasurable.of_discrete
  · simp only [Hz, dite_false]; infer_instance

theorem head_step_mass [Countable rT] [MeasurableSingletonClass rT]
    (e : Exp rT) (σ : State rT) :
    (∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) → IsProbabilityMeasure (headStep ⟨e, σ⟩) := by
  head_case
  all_goals try (· simp)
  case beta.lam.redex | beta.fix.redex | cond.true | cond.false
     | fst.redex | snd.redex | case.left.redex | case.right.redex
     | alloc.redex | load.redex | store.redex | tape
     | rand.tape.deterministic
     | scrut_success | scrut_failure => intro _; infer_instance
  case unop.redex | binop.redex =>
    intro ⟨_, hρ⟩; rw [unwrapM_singleton_pos] at hρ
    obtain ⟨_, he, _⟩ := hρ; simp [Option.unwrapM, he]; infer_instance
  case rand.plain | rand.tape | rand.tape.mismatch =>
    intro _; exact Cfg.uniform_isProbabilityMeasure

/-- `headStep` is a sub-probability measure: total mass is at most 1.
Case split on whether any singleton has positive mass: if so, `headStep ρ`
is a probability measure (by `head_step_mass`); if not, it is the zero
measure (since `Cfg` is countable, the total mass is a tsum of singletons). -/
theorem headStep_univ_le_one [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) : (headStep ρ) Set.univ ≤ 1 := by
  by_cases hred : ∃ ρ' : Cfg rT, 0 < (headStep ρ) {ρ'}
  · obtain ⟨e, σ⟩ := ρ
    have := head_step_mass e σ hred
    exact (measure_univ (μ := headStep ⟨e, σ⟩)).le
  · have hzero : ∀ ρ', (headStep ρ) {ρ'} = 0 := fun ρ' =>
      le_antisymm (by simpa using (not_exists.mp hred ρ')) bot_le
    have hunivzero : (headStep ρ) Set.univ = 0 := by
      rw [show (Set.univ : Set (Cfg rT)) = ⋃ c : Cfg rT, ({c} : Set (Cfg rT)) from by ext; simp]
      rw [measure_iUnion
          (fun i j hij => by simp only [Set.disjoint_singleton]; exact hij)
          (fun _ => .of_discrete)]
      simp [hzero]
    rw [hunivzero]; exact zero_le_one

end ProbLang
