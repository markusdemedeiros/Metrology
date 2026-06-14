module

public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.Discrete

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

variable {rT : Type _}

@[simp] def Ectx.fillCfg [ProbLangℝ rT] (K : Ectx rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fill ρ.expr, ρ.state⟩

theorem Ectx.fillCfg_comp [ProbLangℝ rT] (K1 K2 : Ectx rT) :
    (K1.comp K2).fillCfg = K1.fillCfg ∘ K2.fillCfg := by
  funext ⟨e, σ⟩; simp [Ectx.fill_comp]

@[simp]
theorem Ectx.fillCfg_empty [ProbLangℝ rT] : Ectx.fillCfg ([] : Ectx rT) = id := by
  funext ⟨e, σ⟩; simp [Ectx.fillCfg, Ectx.fill]

theorem Ectx.fillCfg_injective [ProbLangℝ rT] (K : Ectx rT) :
    Function.Injective K.fillCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simpa [Cfg.mk.injEq, Ectx.fill_injective K |>.eq_iff] using h

@[fun_prop]
theorem Ectx.fillCfg.measurable [ProbLangℝ rT] (K : Ectx rT) :
    Measurable K.fillCfg := by
  rw [Cfg.measurable_iff]
  exact ⟨Exp.Ectx_fill.measurable.comp (measurable_const.prodMk Cfg.measurable_expr),
    Cfg.measurable_state⟩

/-- For a fixed evaluation-context *item* `Ki`, plugging an expression into its
hole is a measurable embedding `Exp rT → Exp rT`: it is the corresponding `Exp`
constructor embedding precomposed with inserting `e` into the appropriate slot
(the remaining slots being constants). Each constant-insertion is itself a
measurable embedding because `Exp rT` has measurable singletons (from
`ProbLangℝ.toMeasurableEq`). -/
theorem EctxItem.fillItem.measurableEmbedding [ProbLangℝ rT] (Ki : EctxItem rT) :
    MeasurableEmbedding Ki.fillItem := by
  cases Ki with
  | appL v2 => exact Exp.app.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | appR e1 => exact Exp.app.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | unop op => exact Exp.unop.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | binopL op v2 =>
      exact Exp.binop.measurableEmbedding.comp
        (MeasurableEmbedding.prodMk_left _ (measurableEmbedding_prod_mk_right _))
  | binopR op e1 =>
      exact Exp.binop.measurableEmbedding.comp
        (MeasurableEmbedding.prodMk_left _ (measurableEmbedding_prodMk_left _))
  | condC e1 e2 =>
      exact Exp.cond.measurableEmbedding.comp (measurableEmbedding_prod_mk_right (e1, e2))
  | pairL v2 => exact Exp.pair.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | pairR e1 => exact Exp.pair.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | fst => exact Exp.fst.measurableEmbedding
  | snd => exact Exp.snd.measurableEmbedding
  | inl => exact Exp.inl.measurableEmbedding
  | inr => exact Exp.inr.measurableEmbedding
  | case e1 e2 =>
      exact Exp.case.measurableEmbedding.comp (measurableEmbedding_prod_mk_right (e1, e2))
  | alloc => exact Exp.alloc.measurableEmbedding
  | load => exact Exp.load.measurableEmbedding
  | storeL v2 => exact Exp.store.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | storeR e1 => exact Exp.store.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | tape => exact Exp.tape.measurableEmbedding
  | randL v2 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)
  | randR e1 => exact Exp.rand.measurableEmbedding.comp (measurableEmbedding_prodMk_left _)
  | scrut p => exact Exp.scrut.measurableEmbedding.comp (measurableEmbedding_prod_mk_right _)

/-- Filling a fixed evaluation context `K` is a measurable embedding
`Exp rT → Exp rT`. By induction on `K` (as a `foldl` of per-item fills): the
empty context is the identity and `K = Ki :: K'` is `K'.fill ∘ Ki.fillItem`, a
composition of measurable embeddings. -/
theorem Ectx.fill.measurableEmbedding [ProbLangℝ rT] (K : Ectx rT) :
    MeasurableEmbedding K.fill := by
  induction K with
  | nil => exact MeasurableEmbedding.id
  | cons Ki K ih => exact ih.comp (EctxItem.fillItem.measurableEmbedding Ki)

/-- `Cfg rT` is measurably isomorphic to `Exp rT × State rT`. -/
def Cfg.measurableEquivProd [ProbLangℝ rT] : Cfg rT ≃ᵐ Exp rT × State rT where
  toFun ρ := (ρ.expr, ρ.state)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Cfg.measurable_expr.prodMk Cfg.measurable_state
  measurable_invFun := Cfg.measurable_mk

/-- `K.fillCfg` is a measurable embedding: under the measurable isomorphism
`Cfg rT ≃ᵐ Exp rT × State rT` it is `Prod.map K.fill id`, a composition of
measurable embeddings. -/
theorem Ectx.fillCfg.measurableEmbedding [ProbLangℝ rT] (K : Ectx rT) :
    MeasurableEmbedding K.fillCfg := by
  have h : K.fillCfg
      = Cfg.measurableEquivProd.symm ∘ Prod.map K.fill id ∘ Cfg.measurableEquivProd := by
    funext ρ; rfl
  rw [h]
  exact (Cfg.measurableEquivProd.symm.measurableEmbedding.comp
    ((Ectx.fill.measurableEmbedding K).prodMap MeasurableEmbedding.id)).comp
    Cfg.measurableEquivProd.measurableEmbedding

/-- `K.fillCfg` is a **measurable embedding**: it carries measurable sets to
measurable sets. It factors through the measurable isomorphism
`Cfg rT ≃ᵐ Exp rT × State rT` as `Prod.map K.fill id`, where `K.fill` is a
measurable embedding (`Ectx.fill.measurableEmbedding`, built per-constructor from
the `Exp` constructor embeddings). This is the single remaining fact behind the
countability-free `glm'_bind` (the transported support predicate
`K.fillCfg '' {R}` must be measurable). -/
theorem Ectx.measurableSet_fillCfg_image [ProbLangℝ rT] (K : Ectx rT)
    {S : Set (Cfg rT)} (hS : MeasurableSet S) : MeasurableSet (K.fillCfg '' S) :=
  (Ectx.fillCfg.measurableEmbedding K).measurableSet_image' hS

@[simp] def EctxItem.fillItemCfg [ProbLangℝ rT] (K : EctxItem rT) (ρ : Cfg rT) : Cfg rT :=
  ⟨K.fillItem ρ.expr, ρ.state⟩

theorem Ectx.fillItemCfg_injective [ProbLangℝ rT] (K : EctxItem rT) :
    Function.Injective K.fillItemCfg  := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ ha
  simp only [EctxItem.fillItemCfg, Cfg.mk.injEq] at ha
  have _ := @Ectx.fillItem_injective rT K e1 e2
  grind

def primStep [ProbLangℝ rT] (cfg : Cfg rT) : Measure (Cfg rT) :=
  let (K, e') := cfg.expr.decomp
  (headStep ⟨e', cfg.state⟩).map K.fillCfg


/-! ### Measurability for arbitrary measurable `rT`. -/

/-- `primStep : Cfg rT → Measure (Cfg rT)` is measurable.

`primStep cfg = (headStep ⟨decomp.2, cfg.state⟩).map (decomp.1.fillCfg)`. The
parameterized pushforward (via `Measure.measurable_map_uncurry`) reduces
measurability to joint measurability of:
- the "fill" map `(cfg, ρ) ↦ cfg.expr.decomp.1.fillCfg ρ`, which uses
  `Ectx.fill.measurable` (stamped via `List.measurable_foldl`),
- the "headStep input" map `cfg ↦ ⟨cfg.expr.decomp.2, cfg.state⟩` composed
  with `headStep.measurable`. -/
@[fun_prop]
theorem primStep.measurable [ProbLangℝ rT] : Measurable (primStep : Cfg rT → Measure (Cfg rT)) := by
  -- Source kernel `k : Cfg rT → Measure (Cfg rT)`.
  have hk_inner : Measurable
      (fun cfg : Cfg rT => (Cfg.mk cfg.expr.decomp.2 cfg.state : Cfg rT)) := by
    measurability
  have hk : Measurable (fun cfg : Cfg rT =>
      headStep (Cfg.mk cfg.expr.decomp.2 cfg.state)) :=
    headStep.measurable.comp hk_inner
  -- Joint pushforward function `h : Cfg rT × Cfg rT → Cfg rT`.
  have hh : Measurable (fun (p : Cfg rT × Cfg rT) => p.1.expr.decomp.1.fillCfg p.2) := by
    -- p.1.expr.decomp.1.fillCfg p.2 = Cfg.mk (Ectx.fill p.1.expr.decomp.1 p.2.expr) p.2.state
    rw [Cfg.measurable_iff]
    refine ⟨?_, ?_⟩
    · refine Exp.Ectx_fill.measurable.comp (Measurable.prodMk ?_ ?_)
      · measurability
      · measurability
    · measurability
  -- Uniform mass bound ≤ 1 gives IsFiniteKernel, hence IsSFiniteKernel.
  have hFin : ProbabilityTheory.IsFiniteKernel (ProbabilityTheory.Kernel.mk (fun cfg : Cfg rT =>
      headStep (Cfg.mk cfg.expr.decomp.2 cfg.state)) hk) :=
    ⟨1, ENNReal.one_lt_top, fun cfg => headStep_univ_le_one' _⟩
  have hSF : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk (fun cfg : Cfg rT =>
      headStep (Cfg.mk cfg.expr.decomp.2 cfg.state)) hk) := inferInstance
  exact Measure.measurable_map_uncurry hh hk

def primStepKernel [ProbLangℝ rT] : Kernel (Cfg rT) (Cfg rT) where
  measurable' := primStep.measurable
  toFun := primStep

-- -> Use Reducible
@[discrete]
abbrev Discrete.Reducible [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ∃ ρ : Cfg rT, 0 < primStep ⟨e, σ⟩ {ρ}

abbrev Reducible [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  primStep ⟨e, σ⟩ ≠ 0

-- This one needs no continuous anlogue, it's purely discrete reasoning
@[discrete]
theorem Discrete.primStep_discrete_iff {e : Exp rT} {σ : State rT}
    [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] :
    (∃ ρ, 0 < (primStep { expr := e, state := σ }) {ρ}) ↔ primStep { expr := e, state := σ } ≠ 0 := by
  refine ⟨fun ⟨ρ, Hρ⟩ Hz => by simp [Hz] at Hρ, ?_⟩
  by_contra!
  rcases this with ⟨Hnz, H⟩
  refine Hnz <| ext_of_singleton fun ρ => ?_
  simp [nonpos_iff_eq_zero.mp (H ρ)]

-- Bridge
@[discrete]
theorem Reducible_ReducibleM_iff {e : Exp rT} {σ : State rT}
    [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] :
    Discrete.Reducible e σ ↔ Reducible e σ := by
  unfold Discrete.Reducible Reducible
  exact Discrete.primStep_discrete_iff

/-! ## Values can't step -/

theorem val_stuck [ProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (h : primStep ⟨e, σ⟩ ≠ 0) : ¬e.isValue := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  refine Ectx.fill_noVal ?_
  refine val_head_stuck (σ := σ) ?_
  intro hz; rw [hz] at h; simp at h

-- use val_stuck (old proof deleted)
@[discrete]
nonrec theorem Discrete.val_stuck [ProbLangℝ rT] [Countable rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < primStep ⟨e, σ⟩ {ρ}) : ¬e.isValue := by
  refine val_stuck (σ := σ) ?_
  refine Discrete.primStep_discrete_iff.mp ?_
  exists ρ

/-- `primStep` is a sub-probability measure: total mass is at most 1.
Follows from `Discrete.headStep_univ_le_one` via `Measure.map` preserving total mass. -/
theorem primStep_univ_le_one [ProbLangℝ rT] (ρ : Cfg rT) : (primStep ρ) Set.univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  simp only [primStep]
  have Hmeas : Measurable e.decomp.1.fillCfg := by measurability
  rw [Measure.map_apply Hmeas MeasurableSet.univ]
  simpa using headStep_univ_le_one' ⟨e.decomp.2, σ⟩

/-- `primStep` of a reducible configuration is a probability measure. Countability-free
analogue of `prim_step_mass_discrete`: `Reducible e σ` means `primStep ⟨e,σ⟩ ≠ 0`, which
forces the underlying `headStep` to be nonzero, hence (by `head_step_mass`) a probability
measure; pushing forward under the measurable `fillCfg` preserves total mass `1`. -/
theorem prim_step_mass [ProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) : IsProbabilityMeasure (primStep ⟨e, σ⟩) := by
  have hmeas : Measurable e.decomp.1.fillCfg := by measurability
  have hhs : headStep ⟨e.decomp.2, σ⟩ ≠ 0 := by
    intro h
    apply hred
    simp only [primStep, h, Measure.map_zero]
  haveI := head_step_mass hhs
  simp only [primStep]
  exact isProbabilityMeasure_map hmeas.aemeasurable

/-! ## Bridge: headStep ↔ primStep -/

-- Use primStep_eq_headStep
@[discrete]
theorem primStep_eq_headStep_discrete [ProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) : primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by
    simp only [primStep, hd, Ectx.fillCfg_empty, Measure.map_id]
  rw [e.decomp_unfold]
  rcases hm : e.decompItem with _ | ⟨Ki, e'⟩
  · simp
  · obtain ⟨hfill, hne⟩ := Exp.decompItem_fill hm
    obtain ⟨ρ, hρ⟩ := hred
    rw [← hfill] at hρ
    exact (hne (Discrete.head_ctx_step_val hρ)).elim

theorem primStep_eq_headStep [ProbLangℝ rT] {e : Exp rT} {σ : State rT} (hred : HeadReducible e σ) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by simp [primStep, hd]
  unfold Exp.decomp
  cases H : e.decompItem
  · simp
  · rename_i redex
    obtain ⟨K, e'⟩ := redex
    obtain ⟨hfill, hne⟩ := Exp.decompItem_fill H
    exfalso
    exact hne <| head_ctx_step_val (hfill ▸ hred)

@[discrete]
theorem primStep_pos_of_headStep_discrete [ProbLangℝ rT] {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : 0 < primStep ⟨e, σ⟩ {ρ} :=
  primStep_eq_headStep_discrete ⟨ρ, h⟩ ▸ h

theorem reducible_of_headReducible [ProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (h : HeadReducible e σ) : Reducible e σ := by
  unfold Reducible
  rw [primStep_eq_headStep h]
  exact h

/-! ## Context fill interaction with primStep -/

theorem primStep_fill [ProbLangℝ rT] {K : Ectx rT} {e : Exp rT} {σ : State rT} (hv : ¬e.isValue) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [Measure.map_map ?G1 ?G2]
  case G1 => measurability
  case G2 => measurability
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_app]

theorem primStep_fillItem [ProbLangℝ rT]
    (Ki : EctxItem rT) {e : Exp rT} {σ : State rT} (hv : ¬e.isValue) :
    primStep ⟨Ki.fillItem e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨Ki.fillItem ρ.expr, ρ.state⟩) := by
  have : Ki.fillItem e = Ectx.fill [Ki] e := by simp [Ectx.fill, List.foldl, flip]
  rw [this, primStep_fill hv]; congr 1

-- TODO: This generalized to continuous, though really I imagine it can't be used in any continuous way.
-- I won't mark it as discrete, but I'd guess this should really be changed to be primStep_fill
theorem primStep_fill_singleton [ProbLangℝ rT] {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue) : primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [primStep_fill hv, Measure.map_apply ?G1 ?G2]
  case G1 => measurability
  case G2 => measurability
  congr 1
  ext ⟨e', σ'⟩
  simp [(Ectx.fill_injective K).eq_iff]

-- primStep_fill_pos
@[discrete]
theorem primStep_fill_pos_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : 0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩}) :
    0 < primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rwa [← primStep_fill_singleton (Discrete.val_stuck h)]

theorem primStep_fill_pos [ProbLangℝ rT] {K : Ectx rT} {e : Exp rT} {σ : State rT}
    (h : primStep ⟨e, σ⟩ ≠ 0) : primStep ⟨K.fill e, σ⟩ ≠ 0 := by
  by_cases hk : e.isValue
  · exact val_stuck h hk |>.elim
  · rw [primStep_fill hk]
    have hm : Measurable (fun ρ : Cfg rT ↦ (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT)) := by measurability
    refine fun H => h ?_
    refine Measure.measure_univ_eq_zero.mp ?_
    have := H ▸ Measure.map_apply hm .univ (μ := primStep ⟨e, σ⟩)
    simpa using this.symm

-- primStep_fill_inv
@[discrete]
theorem primStep_fill_inv_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue)
    (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := Discrete.map_singleton_pos h
  simp [Cfg.mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

theorem primStep_fill_inv [ProbLangℝ rT]  {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue) (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos (by measurability) (Ectx.fillCfg_injective K) h
  simp [Cfg.mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

/-! ## Discrete.Reducible: fill interaction -/

-- Reducible.fill
@[discrete]
theorem Discrete.Reducible.fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : Discrete.Reducible e σ) : Discrete.Reducible (K.fill e) σ :=
  let ⟨⟨e2, σ2⟩, hρ⟩ := hred; ⟨⟨K.fill e2, σ2⟩, primStep_fill_pos_discrete hρ⟩

theorem Reducible.fill [ProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) : Reducible (K.fill e) σ :=
  primStep_fill_pos hred

-- Reducible.of_fill
@[discrete]
theorem Discrete.Reducible.of_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hred : Discrete.Reducible (K.fill e) σ) : Discrete.Reducible e σ :=
  let ⟨⟨_, σ2⟩, hρ⟩ := hred; let ⟨e2', _, hρ'⟩ := primStep_fill_inv_discrete hv hρ; ⟨⟨e2', σ2⟩, hρ'⟩

theorem Reducible.of_fill [ProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hred : Reducible (K.fill e) σ) : Reducible e σ := by
  unfold Reducible at hred ⊢
  rw [primStep_fill hv] at hred
  exact fun h0 => hred (by rw [h0]; simp)

-- Reducible.of_head
@[discrete]
theorem Discrete.Reducible.of_head [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Discrete.Reducible e σ :=
  let ⟨ρ, hρ⟩ := hred; ⟨ρ, primStep_pos_of_headStep_discrete hρ⟩

theorem Reducible.of_head [ProbLangℝ rT] {e : Exp rT} {σ : State rT} (hred : HeadReducible e σ) :
    Reducible e σ := reducible_of_headReducible hred

-- Reducible.of_head_fill
@[discrete]
theorem Discrete.Reducible.of_head_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Discrete.Reducible (K.fill e) σ :=
  (Discrete.Reducible.of_head hred).fill K

theorem Reducible.of_head_fill [ProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : HeadReducible e σ) : Reducible (K.fill e) σ :=
  Reducible.of_head hred |>.fill K

/-! ## Irreducible: contrapositives -/

-- irreducible_fill
@[discrete]
theorem irreducible_fill_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hirr : ¬ Discrete.Reducible e σ) : ¬ Discrete.Reducible (K.fill e) σ :=
  fun hred => hirr (hred.of_fill K hv)

theorem irreducible_fill [ProbLangℝ rT] (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hirr : ¬ Reducible e σ) : ¬ Reducible (K.fill e) σ :=
  fun hr => hirr (hr.of_fill K hv)

-- irreducible_fill_inv
@[discrete]
theorem irreducible_fill_inv_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hirr : ¬ Discrete.Reducible (K.fill e) σ) : ¬ Discrete.Reducible e σ :=
  fun hred => hirr (hred.fill K)

theorem irreducible_fill_inv [ProbLangℝ rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hirr : ¬ Reducible (K.fill e) σ) : ¬ Reducible e σ :=
  fun hred => hirr (hred.fill K)

-- Reducible.headStep_zero
@[discrete]
theorem Discrete.Reducible.headStep_zero [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ¬ Discrete.Reducible e σ) :
    ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0 :=
  fun ρ => by
    by_contra h
    exact hirr ⟨ρ, primStep_pos_of_headStep_discrete (pos_iff_ne_zero.mpr h)⟩

theorem Reducible.headStep_zero [ProbLangℝ rT] {e : Exp rT} {σ : State rT} (hirr : ¬ Reducible e σ) :
    headStep ⟨e, σ⟩ = 0 := by
  by_contra h; exact hirr <| reducible_of_headReducible h

/-! ## Context decomposition -/

-- head_ctx_step_val_ectx
@[discrete]
theorem head_ctx_step_val_ectx_discrete [ProbLangℝ rT]
    (K : Ectx rT) (e : Exp rT) (σ : State rT) (ρ : Cfg rT)
    (hstep : 0 < headStep ⟨K.fill e, σ⟩ {ρ}) :
    e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [Ectx.fill_snoc] at hstep
    exact .inl (Ectx.fill_isValue (Discrete.head_ctx_step_val hstep))

theorem head_ctx_step_val_ectx [ProbLangℝ rT] (K : Ectx rT) (e : Exp rT) (σ : State rT)
    (hstep : HeadReducible (K.fill e) σ) : e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [Ectx.fill_snoc] at hstep
    exact .inl (Ectx.fill_isValue (head_ctx_step_val hstep))

-- step_by_val
@[discrete]
theorem step_by_val_discrete [ProbLangℝ rT]
    (K' K_redex : Ectx rT) (e1' e1_redex : Exp rT) (σ : State rT) (ρ : Cfg rT)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : ¬e1'.isValue)
    (hstep : 0 < headStep ⟨e1_redex, σ⟩ {ρ}) :
    ∃ K'' : Ectx rT, K_redex = K'.comp K'' := by
  induction K' using List.reverseRecOn generalizing K_redex e1_redex with
  | nil => exact ⟨K_redex, (List.append_nil K_redex).symm⟩
  | append_singleton K'_rest Ki' ih =>
    simp only [Ectx.fill_snoc] at hfill
    rcases List.eq_nil_or_snoc K_redex with rfl | ⟨K_redex_rest, Ki_redex, rfl⟩
    · simp only [Ectx.fill, List.foldl_nil] at hfill
      subst hfill
      exact absurd (Ectx.fill_isValue (Discrete.head_ctx_step_val hstep)) hv
    · simp only [Ectx.fill_snoc] at hfill ⊢
      have hKi := EctxItem.fillItem_noVal_inj (Ectx.fill_noVal hv) (Ectx.fill_noVal (Discrete.val_head_stuck hstep)) hfill
      subst hKi
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex (Ectx.fillItem_injective hfill) hstep
      exact ⟨K'', by rw [hK'']; simp [Ectx.comp, List.append_assoc]⟩

theorem step_by_val [ProbLangℝ rT] (K' K_redex : Ectx rT) (e1' e1_redex : Exp rT) (σ : State rT)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : ¬e1'.isValue)
    (hstep : HeadReducible e1_redex σ) :
    ∃ K'' : Ectx rT, K_redex = K'.comp K'' := by
  induction K' using List.reverseRecOn generalizing K_redex e1_redex with
  | nil => exact ⟨K_redex, (List.append_nil K_redex).symm⟩
  | append_singleton K'_rest Ki' ih =>
    simp only [Ectx.fill_snoc] at hfill
    rcases List.eq_nil_or_snoc K_redex with rfl | ⟨K_redex_rest, Ki_redex, rfl⟩
    · simp only [Ectx.fill, List.foldl_nil] at hfill
      subst hfill
      exact absurd (Ectx.fill_isValue (head_ctx_step_val hstep)) hv
    · simp only [Ectx.fill_snoc] at hfill ⊢
      have hKi := EctxItem.fillItem_noVal_inj (Ectx.fill_noVal hv) (Ectx.fill_noVal (val_head_stuck hstep)) hfill
      subst hKi
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex (Ectx.fillItem_injective hfill) hstep
      exact ⟨K'', by rw [hK'']; simp [Ectx.comp, List.append_assoc]⟩

-- not_headReducible_iff
@[discrete]
theorem not_head_reducible [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT} :
    (¬ ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) ↔ (∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0) := by
  push Not; exact forall_congr' fun _ => nonpos_iff_eq_zero

theorem not_headReducible_iff [ProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    (¬ HeadReducible e σ) ↔ (headStep ⟨e, σ⟩ = 0) := by
  push Not
  rfl

-- head_redex_unique
@[discrete]
theorem head_redex_unique_discrete [ProbLangℝ rT]
    (K K' : Ectx rT) (e e' : Exp rT) (σ : State rT)
    (hfill : K.fill e = K'.fill e')
    (hred  : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ})
    (hred' : ∃ ρ : Cfg rT, 0 < headStep ⟨e', σ⟩ {ρ}) :
    -- FIXME: Make this just be K = K'
    K = K'.comp [] ∧ e = e' := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  obtain ⟨⟨e2', σ2'⟩, hρ'⟩ := hred'
  obtain ⟨K'', hK⟩ := step_by_val_discrete K' K e' e σ _ hfill.symm (Discrete.val_head_stuck hρ') hρ
  subst hK
  rw [← Ectx.fill_comp] at hfill
  have he := Ectx.fill_injective K' hfill
  rcases head_ctx_step_val_ectx_discrete K'' e σ _ (he ▸ hρ') with hval | rfl
  · exact absurd hval (Discrete.val_head_stuck hρ)
  · simp [Ectx.fill] at he
    exact ⟨rfl, he⟩

theorem head_redex_unique [ProbLangℝ rT] (K K' : Ectx rT) (e e' : Exp rT) (σ : State rT)
    (hfill : K.fill e = K'.fill e') (hred  : HeadReducible e σ) (hred' : HeadReducible e' σ) :
    -- FIXME: Make this just be K = K'
    K = K'.comp [] ∧ e = e' := by
  obtain ⟨K'', rfl⟩ := step_by_val K K' e e' σ hfill (val_head_stuck hred) hred'
  rw [← Ectx.fill_comp] at hfill
  have he := Ectx.fill_injective _ hfill
  rcases @head_ctx_step_val_ectx rT _ K'' e' σ (he ▸ hred) with hval | rfl
  · exact absurd hval (val_head_stuck hred')
  · simp [Ectx.fill] at he
    exact ⟨rfl, he⟩


/-! ## primStep characterization -/

-- TODO: Not yet sure...
@[discrete]
theorem prim_step_iff_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e1 e2 : Exp rT} {σ1 σ2 : State rT} :
    0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} ↔
    ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      0 < headStep ⟨e1', σ1⟩ {⟨e2', σ2⟩} := by
  constructor
  · intro h
    simp only [primStep] at h
    set d := e1.decomp with hd; obtain ⟨K, e1'⟩ := d
    obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := Discrete.map_singleton_pos h
    simp [Ectx.fillCfg, Cfg.mk.injEq] at heq
    exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, heq.1, heq.2 ▸ hpos⟩
  · rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
    rw [← primStep_fill_singleton (Discrete.val_head_stuck hhs)]
    exact primStep_pos_of_headStep_discrete hhs

/-- Countable-free version of `prim_step_iff_discrete`, stated with the
measurability-free `Possible` predicate. Needs only `[ProbLangℝ rT]` (the
`MeasurableSingletonClass (Cfg rT)` that `map_singleton_pos`/`possible_iff_pos`
want is derivable from it), not the full discrete structure. -/
theorem prim_step_iff [ProbLangℝ rT]
    {e1 e2 : Exp rT} {σ1 σ2 : State rT} :
    Possible (⟨e2, σ2⟩ : Cfg rT) (primStep ⟨e1, σ1⟩) ↔
    ∃ (K : Ectx rT) (e1' e2' : Exp rT),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      Possible (⟨e2', σ2⟩ : Cfg rT) (headStep ⟨e1', σ1⟩) := by
  simp only [possible_iff_pos]
  constructor
  · intro h
    simp only [primStep] at h
    set d := e1.decomp with hd; obtain ⟨K, e1'⟩ := d
    obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ :=
      map_singleton_pos (by measurability) (Ectx.fillCfg_injective K) h
    simp [Ectx.fillCfg, Cfg.mk.injEq] at heq
    exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, heq.1, heq.2 ▸ hpos⟩
  · rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
    rw [← primStep_fill_singleton (val_head_stuck (by intro h0; rw [h0] at hhs; simp at hhs))]
    exact primStep_pos_of_headStep_discrete hhs

-- TODO: Blocked
@[discrete]
theorem prim_step_iff'_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hstep : Discrete.Reducible e σ) :
    ∃ (K : Ectx rT) (e' : Exp rT), K.fill e' = e ∧
      (∃ ρ : Cfg rT, 0 < headStep ⟨e', σ⟩ {ρ}) ∧
      primStep ⟨e, σ⟩ = (headStep ⟨e', σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  obtain ⟨⟨e2, σ2⟩, h⟩ := hstep
  rw [prim_step_iff_discrete] at h
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := h
  exact ⟨K, e1', hfill1, ⟨_, hhs⟩, by
    rw [← hfill1, primStep_fill (Discrete.val_head_stuck hhs), primStep_eq_headStep_discrete ⟨_, hhs⟩]⟩

-- TODO: Blocked
@[discrete]
theorem prim_step_mass_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (cfg : Cfg rT) :
    Discrete.Reducible cfg.expr cfg.state → IsProbabilityMeasure (primStep cfg) := by
  intro hred
  obtain ⟨_, e'', _, hhead_red, hps_eq⟩ := prim_step_iff'_discrete hred
  rw [hps_eq]
  haveI := Discrete.head_step_mass e'' cfg.state hhead_red
  exact Measure.isProbabilityMeasure_map .of_discrete

/-! ## headStep ↔ primStep in context -/

-- TODO: Blocked
@[discrete]
theorem Discrete.headStep_of_primStep_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e1 : Exp rT} {σ1 : State rT} {e2 : Exp rT} {σ2 : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e1, σ1⟩ {ρ})
    (hstep : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < headStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [prim_step_iff_discrete] at hstep
  obtain ⟨K', e1', e2', hfill1, hfill2, hhs⟩ := hstep
  obtain ⟨ρ_red, hρ_red⟩ := hred
  obtain ⟨K'', hK''⟩ := step_by_val_discrete K' K e1' e1 σ1 _ hfill1 (Discrete.val_head_stuck hhs) hρ_red
  subst hK''
  simp only [Ectx.comp, fill_app] at hfill1
  have he1' := Ectx.fill_injective K' hfill1
  rcases head_ctx_step_val_ectx_discrete K'' e1 σ1 _ (he1' ▸ hhs) with hval | rfl
  · exact absurd hval (Discrete.val_head_stuck hρ_red)
  · simp only [Ectx.fill, List.foldl_nil] at he1' hfill2
    exact ⟨e2', hfill2.symm, he1' ▸ hhs⟩

-- TODO: Blocked
@[discrete]
theorem headStep_of_primStep_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (hred : ∃ ρ' : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ'})
    (hstep : 0 < primStep ⟨e, σ⟩ {ρ}) : 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨_, σ₂⟩ := ρ
  obtain ⟨e2', hfill, hhs⟩ := Discrete.headStep_of_primStep_fill [] hred hstep
  simp [Ectx.fill] at hfill; exact hfill ▸ hhs

-- TODO: Blocked
@[discrete]
theorem head_irreducible_zero_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0) :
    headStep ⟨e, σ⟩ = 0 := by
  ext S _
  by_contra hne
  obtain ⟨x, _, hx⟩ := Discrete.measure_pos_of_singleton_pos _ S (bot_lt_iff_ne_bot.mpr hne)
  simp [hirr x] at hx

-- TODO: Blocked
@[discrete]
theorem head_step_not_stuck_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) :
    ¬e.isValue ∧ Discrete.Reducible e σ :=
  ⟨Discrete.val_head_stuck h, ρ, primStep_pos_of_headStep_discrete h⟩

/-! ## subRedexesAreValues -/

def subRedexesAreValues [ProbLangℝ rT] (e : Exp rT) : Prop :=
  ∀ (K : Ectx rT) (e' : Exp rT), e = K.fill e' → ¬e'.isValue → K = []

theorem ectxi_language_subRedexesAreValues [ProbLangℝ rT] {e : Exp rT}
    (h : ∀ (Ki : EctxItem rT) (e' : Exp rT), e = Ki.fillItem e' → e'.isValue) :
    subRedexesAreValues e := by
  intro K e' hfill hv
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · rfl
  · simp only [Ectx.fill_snoc] at hfill
    exact absurd (Ectx.fill_isValue (h Ki _ hfill)) hv

-- TODO: Blocked
@[discrete]
theorem prim_head_reducible_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hred : Discrete.Reducible e σ) (hsub : subRedexesAreValues e) :
    ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨⟨e2, σ2⟩, hstep⟩ := hred
  rw [prim_step_iff_discrete] at hstep
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := hstep
  have hK := hsub K e1' hfill1.symm (Discrete.val_head_stuck hhs)
  subst hK
  simp [Ectx.fill] at hfill1
  subst hfill1
  exact ⟨_, hhs⟩

-- TODO: Blocked
@[discrete]
theorem prim_head_irreducible_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬ Discrete.Reducible e σ :=
  fun hred => not_head_reducible.mpr hirr (prim_head_reducible_discrete hred hsub)

-- TODO: Blocked
@[discrete]
theorem head_stuck_stuck_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hstuck : ¬e.isValue ∧ ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬e.isValue ∧ ¬ Discrete.Reducible e σ :=
  ⟨hstuck.1, prim_head_irreducible_discrete hstuck.2 hsub⟩

/-! ## notStuck_discrete / stuck_discrete -/

-- notStuck
@[discrete]
def notStuck_discrete [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  e.isValue ∨ Discrete.Reducible e σ

def notStuck [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  e.isValue ∨ Reducible e σ

-- NotStuck.of_fill
@[discrete]
theorem NotStuck.of_fill_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : notStuck_discrete (K.fill e) σ) : notStuck_discrete e σ := by
  rcases h with hv | hred
  · exact .inl (Ectx.fill_isValue hv)
  · exact if hv : e.isValue then .inl hv
    else .inr (hred.of_fill K hv)

theorem NotStuck.of_fill [ProbLangℝ rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : notStuck (K.fill e) σ) : notStuck e σ := by
  rcases h with hv | hred
  · exact .inl (Ectx.fill_isValue hv)
  · exact if hv : e.isValue then .inl hv
    else .inr (hred.of_fill K hv)

-- stuck
@[discrete]
def stuck_discrete [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ¬ e.isValue ∧ ¬ Discrete.Reducible e σ

def stuck [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ¬ e.isValue ∧ ¬ Reducible e σ

-- stuck_iff_not_notStuck
@[discrete]
theorem stuck_iff_not_notStuck_discrete [ProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    stuck_discrete e σ ↔ ¬ notStuck_discrete e σ := by
  simp [stuck_discrete, notStuck_discrete, not_or]

theorem stuck_iff_not_notStuck [ProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    stuck e σ ↔ ¬ notStuck e σ := by simp [stuck, notStuck]

-- Stuck.fill
@[discrete]
theorem Stuck.fill_discrete [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : stuck_discrete e σ) : stuck_discrete (K.fill e) σ :=
  ⟨fun hv => h.1 (Ectx.fill_isValue hv),
   fun hred => h.2 (hred.of_fill K h.1)⟩

theorem Stuck.fill [ProbLangℝ rT] 
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : stuck e σ) : stuck (K.fill e) σ :=
  ⟨fun hv => h.1 (Ectx.fill_isValue hv),
   fun hred => h.2 (hred.of_fill K h.1)⟩

/-- The positive-mass ("support") set of `primStep ⟨e, σ⟩` is measurable.
`primStep` is purely atomic (a pushforward of the dirac/uniform `headStep`),
so its support is countable, hence measurable in the `MeasurableSingletonClass`
space `Cfg rT`. Establishing the countable support countability-free is the
remaining structural fact (it follows from the `headStep` atomicity enumeration
`headStep_exists_support_of_ne_zero`). -/
theorem measurableSet_primStep_support [ProbLangℝ rT] (e : Exp rT) (σ : State rT) :
    MeasurableSet {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  -- `primStep` is a finite measure, so its set of positive-mass points (atoms) is
  -- countable (`Measure.countable_meas_level_set_pos`), hence measurable.
  haveI : IsFiniteMeasure (primStep ⟨e, σ⟩) :=
    ⟨lt_of_le_of_lt (primStep_univ_le_one _) ENNReal.one_lt_top⟩
  have hc : {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}.Countable := by
    have h := MeasureTheory.Measure.countable_meas_level_set_pos
      (μ := primStep ⟨e, σ⟩) (g := (id : Cfg rT → Cfg rT)) measurable_id
    simpa only [id_eq, Set.setOf_eq_eq_singleton] using h
  exact hc.measurableSet

/-- **`primStep` is purely atomic** (countability-free): it gives zero mass to the
set of points it gives zero mass to. Transfers `headStep_atomic` through the
injective pushforward `K.fillCfg` (so the co-support pulls back to `headStep`'s
co-support, with no need for `fillCfg`-image measurability). -/
theorem primStep_atomic [ProbLangℝ rT] (e : Exp rT) (σ : State rT) :
    IsAtomicSupport (primStep ⟨e, σ⟩) := by
  have hmeas : Measurable e.decomp.1.fillCfg := by measurability
  have hinj : Function.Injective e.decomp.1.fillCfg := Ectx.fillCfg_injective _
  -- Singleton masses transfer along the injective pushforward.
  have hsingle : ∀ ρ' : Cfg rT,
      (primStep ⟨e, σ⟩) {e.decomp.1.fillCfg ρ'} = (headStep ⟨e.decomp.2, σ⟩) {ρ'} := by
    intro ρ'
    show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg) {e.decomp.1.fillCfg ρ'} = _
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  -- The co-support is measurable (complement of the countable support).
  have hcomeas : MeasurableSet {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} := by
    have heq : {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0}
        = {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ := by
      ext ρ; simp [pos_iff_ne_zero]
    rw [heq]; exact (measurableSet_primStep_support e σ).compl
  unfold IsAtomicSupport
  show ((headStep ⟨e.decomp.2, σ⟩).map e.decomp.1.fillCfg)
      {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} = 0
  rw [Measure.map_apply hmeas hcomeas]
  have hpre : e.decomp.1.fillCfg ⁻¹' {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0}
      = {ρ' : Cfg rT | (headStep ⟨e.decomp.2, σ⟩) {ρ'} = 0} := by
    ext ρ'; simp only [Set.mem_preimage, Set.mem_setOf_eq, hsingle ρ']
  rw [hpre]
  exact headStep_atomic e.decomp.2 σ

end ProbLang
end
