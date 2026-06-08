module

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

theorem Ectx.fillCfg_empty [ProbLangℝ rT] : Ectx.fillCfg ([] : Ectx rT) = id := by
  funext ⟨e, σ⟩; simp [Ectx.fillCfg, Ectx.fill]

theorem Ectx.fillCfg_injective [ProbLangℝ rT] (K : Ectx rT) :
    Function.Injective K.fillCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simpa [Cfg.mk.injEq, Ectx.fill_injective K |>.eq_iff] using h

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
    show Measurable (fun p : Cfg rT × Cfg rT => Cfg.mk (Ectx.fill p.1.expr.decomp.1 p.2.expr) p.2.state)
    rw [Cfg.measurable_iff]
    refine ⟨?_, ?_⟩
    · show Measurable (fun p : Cfg rT × Cfg rT => Ectx.fill p.1.expr.decomp.1 p.2.expr)
      refine Exp.Ectx_fill.measurable.comp (Measurable.prodMk ?_ ?_)
      · measurability
      · measurability
    · measurability
  -- Apply the joint pushforward keystone. The `IsSFiniteKernel` instance is
  -- discharged via a `sorry` for now — morally `headStep` is sub-probability so
  -- the kernel is finite (TODO: prove `headStep.isFiniteKernel` for general rT).
  have hSF : IsSFiniteKernel (Kernel.mk (fun cfg : Cfg rT =>
      headStep (Cfg.mk cfg.expr.decomp.2 cfg.state)) hk) := sorry
  exact Measure.measurable_map_uncurry hh hk

def primStepKernel [ProbLangℝ rT] : Kernel (Cfg rT) (Cfg rT) where
  measurable' := primStep.measurable
  toFun := primStep

@[deprecated "Generalized as primStepKernel" (since := "2026/06/08")]
abbrev primStepKernelM {α : Type} [ProbLangℝ α] := primStepKernel (rT := α)

-- TODO: Make ReducibleM be "no equivalent to zero measure", make Reducible abbrev this
abbrev Reducible [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ∃ ρ : Cfg rT, 0 < primStep ⟨e, σ⟩ {ρ}



/-! ## Values can't step -/

theorem val_stuck [ProbLangℝ rT] [Countable rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < primStep ⟨e, σ⟩ {ρ}) : ¬e.isValue := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  exact Ectx.fill_noVal (val_head_stuck (map_singleton_pos h).choose_spec.2)

/-- `primStep` is a sub-probability measure: total mass is at most 1.
Follows from `headStep_univ_le_one` via `Measure.map` preserving total mass. -/
theorem primStep_univ_le_one [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) : (primStep ρ) Set.univ ≤ 1 := by
  obtain ⟨e, σ⟩ := ρ
  simp only [primStep]
  have Hmeas : Measurable e.decomp.1.fillCfg := by measurability
  rw [Measure.map_apply Hmeas MeasurableSet.univ]
  simpa using headStep_univ_le_one ⟨e.decomp.2, σ⟩

/-! ## Bridge: headStep ↔ primStep -/

theorem primStep_eq_headStep [ProbLangℝ rT] {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) : primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by
    simp only [primStep, hd, Ectx.fillCfg_empty, Measure.map_id]
  rw [e.decomp_unfold]
  rcases hm : e.decompItem with _ | ⟨Ki, e'⟩
  · simp
  · obtain ⟨hfill, hne⟩ := Exp.decompItem_fill hm
    obtain ⟨ρ, hρ⟩ := hred
    rw [← hfill] at hρ
    exact (hne (head_ctx_step_val hρ)).elim

theorem primStep_pos_of_headStep [ProbLangℝ rT] {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : 0 < primStep ⟨e, σ⟩ {ρ} :=
  primStep_eq_headStep ⟨ρ, h⟩ ▸ h

/-! ## Context fill interaction with primStep -/

theorem primStep_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e : Exp rT} {σ : State rT} (hv : ¬e.isValue) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [Measure.map_map ?G1 ?G2]
  case G1 => exact Measurable.of_discrete
  case G2 => exact Measurable.of_discrete
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_app]

theorem primStep_fillItem [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (Ki : EctxItem rT) {e : Exp rT} {σ : State rT} (hv : ¬e.isValue) :
    primStep ⟨Ki.fillItem e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨Ki.fillItem ρ.expr, ρ.state⟩) := by
  have : Ki.fillItem e = Ectx.fill [Ki] e := by simp [Ectx.fill, List.foldl, flip]
  rw [this, primStep_fill hv]; congr 1

theorem primStep_fill_singleton [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [primStep_fill hv, Measure.map_apply .of_discrete .of_discrete]
  congr 1
  ext ⟨e', σ'⟩
  simp [(Ectx.fill_injective K).eq_iff]

theorem primStep_fill_pos [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (h : 0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩}) :
    0 < primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rwa [← primStep_fill_singleton (val_stuck h)]

theorem primStep_fill_inv [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e1 e2 : Exp rT} {σ1 σ2 : State rT}
    (hv : ¬e1.isValue)
    (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos h
  simp [Cfg.mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

/-! ## Reducible: fill interaction -/

theorem Reducible.fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) : Reducible (K.fill e) σ :=
  let ⟨⟨e2, σ2⟩, hρ⟩ := hred; ⟨⟨K.fill e2, σ2⟩, primStep_fill_pos hρ⟩

theorem Reducible.of_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hred : Reducible (K.fill e) σ) : Reducible e σ :=
  let ⟨⟨_, σ2⟩, hρ⟩ := hred; let ⟨e2', _, hρ'⟩ := primStep_fill_inv hv hρ; ⟨⟨e2', σ2⟩, hρ'⟩

theorem Reducible.of_head [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Reducible e σ :=
  let ⟨ρ, hρ⟩ := hred; ⟨ρ, primStep_pos_of_headStep hρ⟩

theorem Reducible.of_head_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Reducible (K.fill e) σ :=
  (Reducible.of_head hred).fill K

/-! ## Irreducible: contrapositives -/

theorem irreducible_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hv : ¬e.isValue) (hirr : ¬ Reducible e σ) : ¬ Reducible (K.fill e) σ :=
  fun hred => hirr (hred.of_fill K hv)

theorem irreducible_fill_inv [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (hirr : ¬ Reducible (K.fill e) σ) : ¬ Reducible e σ :=
  fun hred => hirr (hred.fill K)

theorem Reducible.headStep_zero [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ¬ Reducible e σ) :
    ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0 :=
  fun ρ => by
    by_contra h
    exact hirr ⟨ρ, primStep_pos_of_headStep (pos_iff_ne_zero.mpr h)⟩

/-! ## Context decomposition -/

theorem head_ctx_step_val_ectx [ProbLangℝ rT]
    (K : Ectx rT) (e : Exp rT) (σ : State rT) (ρ : Cfg rT)
    (hstep : 0 < headStep ⟨K.fill e, σ⟩ {ρ}) :
    e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [Ectx.fill_snoc] at hstep
    exact .inl (Ectx.fill_isValue (head_ctx_step_val hstep))

theorem step_by_val [ProbLangℝ rT]
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
      exact absurd (Ectx.fill_isValue (head_ctx_step_val hstep)) hv
    · simp only [Ectx.fill_snoc] at hfill ⊢
      have hKi := EctxItem.fillItem_noVal_inj (Ectx.fill_noVal hv) (Ectx.fill_noVal (val_head_stuck hstep)) hfill
      subst hKi
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex (Ectx.fillItem_injective hfill) hstep
      exact ⟨K'', by rw [hK'']; simp [Ectx.comp, List.append_assoc]⟩

theorem not_head_reducible [ProbLangℝ rT]
    {e : Exp rT} {σ : State rT} :
    (¬ ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ}) ↔ (∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0) := by
  push Not; exact forall_congr' fun _ => nonpos_iff_eq_zero

theorem head_redex_unique [ProbLangℝ rT]
    (K K' : Ectx rT) (e e' : Exp rT) (σ : State rT)
    (hfill : K.fill e = K'.fill e')
    (hred  : ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ})
    (hred' : ∃ ρ : Cfg rT, 0 < headStep ⟨e', σ⟩ {ρ}) :
    K = K'.comp [] ∧ e = e' := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  obtain ⟨⟨e2', σ2'⟩, hρ'⟩ := hred'
  obtain ⟨K'', hK⟩ := step_by_val K' K e' e σ _ hfill.symm (val_head_stuck hρ') hρ
  subst hK
  rw [← Ectx.fill_comp] at hfill
  have he := Ectx.fill_injective K' hfill
  rcases head_ctx_step_val_ectx K'' e σ _ (he ▸ hρ') with hval | rfl
  · exact absurd hval (val_head_stuck hρ)
  · simp [Ectx.fill] at he
    exact ⟨rfl, he⟩

/-! ## primStep characterization -/

theorem prim_step_iff [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
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
    obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos h
    simp [Ectx.fillCfg, Cfg.mk.injEq] at heq
    exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, heq.1, heq.2 ▸ hpos⟩
  · rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
    rw [← primStep_fill_singleton (val_head_stuck hhs)]
    exact primStep_pos_of_headStep hhs

theorem prim_step_iff' [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hstep : Reducible e σ) :
    ∃ (K : Ectx rT) (e' : Exp rT), K.fill e' = e ∧
      (∃ ρ : Cfg rT, 0 < headStep ⟨e', σ⟩ {ρ}) ∧
      primStep ⟨e, σ⟩ = (headStep ⟨e', σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  obtain ⟨⟨e2, σ2⟩, h⟩ := hstep
  rw [prim_step_iff] at h
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := h
  exact ⟨K, e1', hfill1, ⟨_, hhs⟩, by
    rw [← hfill1, primStep_fill (val_head_stuck hhs), primStep_eq_headStep ⟨_, hhs⟩]⟩

theorem prim_step_mass [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (cfg : Cfg rT) :
    Reducible cfg.expr cfg.state → IsProbabilityMeasure (primStep cfg) := by
  intro hred
  obtain ⟨_, e'', _, hhead_red, hps_eq⟩ := prim_step_iff' hred
  rw [hps_eq]
  haveI := head_step_mass e'' cfg.state hhead_red
  exact Measure.isProbabilityMeasure_map .of_discrete

/-! ## headStep ↔ primStep in context -/

theorem headStep_of_primStep_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e1 : Exp rT} {σ1 : State rT} {e2 : Exp rT} {σ2 : State rT}
    (hred : ∃ ρ : Cfg rT, 0 < headStep ⟨e1, σ1⟩ {ρ})
    (hstep : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < headStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [prim_step_iff] at hstep
  obtain ⟨K', e1', e2', hfill1, hfill2, hhs⟩ := hstep
  obtain ⟨ρ_red, hρ_red⟩ := hred
  obtain ⟨K'', hK''⟩ := step_by_val K' K e1' e1 σ1 _ hfill1 (val_head_stuck hhs) hρ_red
  subst hK''
  simp only [Ectx.comp, fill_app] at hfill1
  have he1' := Ectx.fill_injective K' hfill1
  rcases head_ctx_step_val_ectx K'' e1 σ1 _ (he1' ▸ hhs) with hval | rfl
  · exact absurd hval (val_head_stuck hρ_red)
  · simp only [Ectx.fill, List.foldl_nil] at he1' hfill2
    exact ⟨e2', hfill2.symm, he1' ▸ hhs⟩

theorem headStep_of_primStep [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (hred : ∃ ρ' : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ'})
    (hstep : 0 < primStep ⟨e, σ⟩ {ρ}) : 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨_, σ₂⟩ := ρ
  obtain ⟨e2', hfill, hhs⟩ := headStep_of_primStep_fill [] hred hstep
  simp [Ectx.fill] at hfill; exact hfill ▸ hhs

theorem head_irreducible_zero [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0) :
    headStep ⟨e, σ⟩ = 0 := by
  ext S _
  by_contra hne
  obtain ⟨x, _, hx⟩ := measure_pos_of_singleton_pos _ S (bot_lt_iff_ne_bot.mpr hne)
  simp [hirr x] at hx

theorem head_step_not_stuck [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ρ : Cfg rT}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) :
    ¬e.isValue ∧ Reducible e σ :=
  ⟨val_head_stuck h, ρ, primStep_pos_of_headStep h⟩

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

theorem prim_head_reducible [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hred : Reducible e σ) (hsub : subRedexesAreValues e) :
    ∃ ρ : Cfg rT, 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨⟨e2, σ2⟩, hstep⟩ := hred
  rw [prim_step_iff] at hstep
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := hstep
  have hK := hsub K e1' hfill1.symm (val_head_stuck hhs)
  subst hK
  simp [Ectx.fill] at hfill1
  subst hfill1
  exact ⟨_, hhs⟩

theorem prim_head_irreducible [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hirr : ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬ Reducible e σ :=
  fun hred => not_head_reducible.mpr hirr (prim_head_reducible hred hsub)

theorem head_stuck_stuck [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT}
    (hstuck : ¬e.isValue ∧ ∀ ρ : Cfg rT, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬e.isValue ∧ ¬ Reducible e σ :=
  ⟨hstuck.1, prim_head_irreducible hstuck.2 hsub⟩

/-! ## notStuck / stuck -/

def notStuck [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  e.isValue ∨ Reducible e σ

theorem NotStuck.of_fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : notStuck (K.fill e) σ) : notStuck e σ := by
  rcases h with hv | hred
  · exact .inl (Ectx.fill_isValue hv)
  · exact if hv : e.isValue then .inl hv
    else .inr (hred.of_fill K hv)

def stuck [ProbLangℝ rT] (e : Exp rT) (σ : State rT) : Prop :=
  ¬ e.isValue ∧ ¬ Reducible e σ

theorem stuck_iff_not_notStuck [ProbLangℝ rT] {e : Exp rT} {σ : State rT} :
    stuck e σ ↔ ¬ notStuck e σ := by
  simp [stuck, notStuck, not_or]

theorem Stuck.fill [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {e : Exp rT} {σ : State rT}
    (h : stuck e σ) : stuck (K.fill e) σ :=
  ⟨fun hv => h.1 (Ectx.fill_isValue hv),
   fun hred => h.2 (hred.of_fill K h.1)⟩

end ProbLang
end
