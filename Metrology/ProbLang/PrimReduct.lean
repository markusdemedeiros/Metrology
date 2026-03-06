import Metrology.ProbLang.Measure
import Metrology.ProbLang.Opsem

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

@[simp] def Ectx.fillCfg (K : Ectx) (ρ : Cfg) : Cfg := ⟨K.fill ρ.expr, ρ.state⟩

theorem Ectx.fillCfg_comp (K1 K2 : Ectx) : (K1.comp K2).fillCfg = K1.fillCfg ∘ K2.fillCfg := by
  funext ⟨e, σ⟩; simp [Ectx.fill_comp]

theorem Ectx.fillCfg_empty : Ectx.fillCfg [] = id := by
  funext ⟨e, σ⟩; simp [Ectx.fillCfg, Ectx.fill]

theorem Ectx.fillCfg_injective (K : Ectx) : Function.Injective K.fillCfg := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simpa [Cfg.mk.injEq, Ectx.fill_injective K |>.eq_iff] using h

def primStep (cfg : Cfg) : Measure Cfg :=
  let (K, e') := cfg.expr.decomp
  (headStep ⟨e', cfg.state⟩).map K.fillCfg

def primStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := primStep

abbrev Reducible (e : Exp) (σ : State) : Prop :=
  ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}

/-! ## Values can't step -/

theorem val_stuck (h : 0 < primStep ⟨e, σ⟩ {ρ}) : ¬e.isValue := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  exact Ectx.fill_noVal (val_head_stuck (map_singleton_pos h).choose_spec.2)

/-! ## Bridge: headStep ↔ primStep -/

theorem primStep_eq_headStep (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by
    simp only [primStep, hd, Ectx.fillCfg_empty, Measure.map_id]
  rw [e.decomp_unfold]
  rcases hm : e.decompItem with _ | ⟨Ki, e'⟩
  · simp
  · obtain ⟨hfill, hne⟩ := Exp.decompItem_fill hm
    obtain ⟨ρ, hρ⟩ := hred
    rw [← hfill] at hρ
    exact (hne (head_ctx_step_val hρ)).elim

theorem primStep_pos_of_headStep {e : Exp} {σ : State} {ρ : Cfg}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : 0 < primStep ⟨e, σ⟩ {ρ} :=
  primStep_eq_headStep ⟨ρ, h⟩ ▸ h

/-! ## Context fill interaction with primStep -/

theorem primStep_fill {K : Ectx} (hv : ¬e.isValue) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [Measure.map_map .of_discrete .of_discrete]
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_app]

theorem primStep_fill_singleton {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (hv : ¬e1.isValue) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [primStep_fill hv, Measure.map_apply .of_discrete .of_discrete]
  congr 1
  ext ⟨e', σ'⟩
  simp [(Ectx.fill_injective K).eq_iff]

theorem primStep_fill_pos {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (h : 0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩}) :
    0 < primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rwa [← primStep_fill_singleton (val_stuck h)]

theorem primStep_fill_inv {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (hv : ¬e1.isValue)
    (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [primStep_fill hv] at h
  obtain ⟨⟨e2', σ2'⟩, heq, hpos⟩ := map_singleton_pos h
  simp [Cfg.mk.injEq] at heq
  exact ⟨e2', heq.1.symm, heq.2 ▸ hpos⟩

/-! ## Reducible: fill interaction -/

theorem Reducible.fill (K : Ectx) {e : Exp} {σ : State}
    (hred : Reducible e σ) : Reducible (K.fill e) σ :=
  let ⟨⟨e2, σ2⟩, hρ⟩ := hred; ⟨⟨K.fill e2, σ2⟩, primStep_fill_pos hρ⟩

theorem Reducible.of_fill (K : Ectx) {e : Exp} {σ : State}
    (hv : ¬e.isValue) (hred : Reducible (K.fill e) σ) : Reducible e σ :=
  let ⟨⟨_, σ2⟩, hρ⟩ := hred; let ⟨e2', _, hρ'⟩ := primStep_fill_inv hv hρ; ⟨⟨e2', σ2⟩, hρ'⟩

theorem Reducible.of_head {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Reducible e σ :=
  let ⟨ρ, hρ⟩ := hred; ⟨ρ, primStep_pos_of_headStep hρ⟩

theorem Reducible.of_head_fill (K : Ectx) {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    Reducible (K.fill e) σ :=
  (Reducible.of_head hred).fill K

/-! ## Irreducible: contrapositives -/

theorem irreducible_fill (K : Ectx) {e : Exp} {σ : State}
    (hv : ¬e.isValue) (hirr : ¬ Reducible e σ) : ¬ Reducible (K.fill e) σ :=
  fun hred => hirr (hred.of_fill K hv)

theorem irreducible_fill_inv (K : Ectx) {e : Exp} {σ : State}
    (hirr : ¬ Reducible (K.fill e) σ) : ¬ Reducible e σ :=
  fun hred => hirr (hred.fill K)

theorem Reducible.headStep_zero {e : Exp} {σ : State}
    (hirr : ¬ Reducible e σ) :
    ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0 :=
  fun ρ => by
    by_contra h
    exact hirr ⟨ρ, primStep_pos_of_headStep (pos_iff_ne_zero.mpr h)⟩

/-! ## Context decomposition -/

theorem head_ctx_step_val_ectx (K : Ectx) (e : Exp) (σ : State) (ρ : Cfg)
    (hstep : 0 < headStep ⟨K.fill e, σ⟩ {ρ}) :
    e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · exact .inr rfl
  · simp only [Ectx.fill_snoc] at hstep
    exact .inl (Ectx.fill_isValue (head_ctx_step_val hstep))

theorem step_by_val (K' K_redex : Ectx) (e1' e1_redex : Exp) (σ : State) (ρ : Cfg)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : ¬e1'.isValue)
    (hstep : 0 < headStep ⟨e1_redex, σ⟩ {ρ}) :
    ∃ K'' : Ectx, K_redex = K'.comp K'' := by
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

theorem not_head_reducible {e : Exp} {σ : State} :
    (¬ ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) ↔ (∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0) := by
  push_neg; exact forall_congr' fun _ => nonpos_iff_eq_zero

theorem head_redex_unique (K K' : Ectx) (e e' : Exp) (σ : State)
    (hfill : K.fill e = K'.fill e')
    (hred  : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ})
    (hred' : ∃ ρ : Cfg, 0 < headStep ⟨e', σ⟩ {ρ}) :
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

theorem prim_step_iff {e1 e2 : Exp} {σ1 σ2 : State} :
    0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} ↔
    ∃ (K : Ectx) (e1' e2' : Exp),
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

theorem prim_step_iff' {e : Exp} {σ : State}
    (hstep : Reducible e σ) :
    ∃ (K : Ectx) (e' : Exp), K.fill e' = e ∧
      (∃ ρ : Cfg, 0 < headStep ⟨e', σ⟩ {ρ}) ∧
      primStep ⟨e, σ⟩ = (headStep ⟨e', σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  obtain ⟨⟨e2, σ2⟩, h⟩ := hstep
  rw [prim_step_iff] at h
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := h
  exact ⟨K, e1', hfill1, ⟨_, hhs⟩, by
    rw [← hfill1, primStep_fill (val_head_stuck hhs), primStep_eq_headStep ⟨_, hhs⟩]⟩

theorem prim_step_mass (cfg : Cfg) :
    Reducible cfg.expr cfg.state → IsProbabilityMeasure (primStep cfg) := by
  intro hred
  obtain ⟨_, e'', _, hhead_red, hps_eq⟩ := prim_step_iff' hred
  rw [hps_eq]
  haveI := head_step_mass e'' cfg.state hhead_red
  exact Measure.isProbabilityMeasure_map .of_discrete

/-! ## headStep ↔ primStep in context -/

theorem headStep_of_primStep_fill (K : Ectx) {e1 : Exp} {σ1 : State} {e2 : Exp} {σ2 : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e1, σ1⟩ {ρ})
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

theorem headStep_of_primStep {e : Exp} {σ : State} {ρ : Cfg}
    (hred : ∃ ρ' : Cfg, 0 < headStep ⟨e, σ⟩ {ρ'})
    (hstep : 0 < primStep ⟨e, σ⟩ {ρ}) : 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨_, σ₂⟩ := ρ
  obtain ⟨e2', hfill, hhs⟩ := headStep_of_primStep_fill [] hred hstep
  simp [Ectx.fill] at hfill; exact hfill ▸ hhs

theorem head_irreducible_zero {e : Exp} {σ : State}
    (hirr : ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0) :
    headStep ⟨e, σ⟩ = 0 := by
  ext S _
  by_contra hne
  obtain ⟨x, _, hx⟩ := measure_pos_of_singleton_pos _ S (bot_lt_iff_ne_bot.mpr hne)
  simp [hirr x] at hx

theorem head_step_not_stuck {e : Exp} {σ : State} {ρ : Cfg}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) :
    ¬e.isValue ∧ Reducible e σ :=
  ⟨val_head_stuck h, ρ, primStep_pos_of_headStep h⟩

/-! ## subRedexesAreValues -/

def subRedexesAreValues (e : Exp) : Prop :=
  ∀ (K : Ectx) (e' : Exp), e = K.fill e' → ¬e'.isValue → K = []

theorem ectxi_language_subRedexesAreValues {e : Exp}
    (h : ∀ (Ki : EctxItem) (e' : Exp), e = Ki.fillItem e' → e'.isValue) :
    subRedexesAreValues e := by
  intro K e' hfill hv
  rcases List.eq_nil_or_snoc K with rfl | ⟨K'', Ki, rfl⟩
  · rfl
  · simp only [Ectx.fill_snoc] at hfill
    exact absurd (Ectx.fill_isValue (h Ki _ hfill)) hv

theorem prim_head_reducible {e : Exp} {σ : State}
    (hred : Reducible e σ) (hsub : subRedexesAreValues e) :
    ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨⟨e2, σ2⟩, hstep⟩ := hred
  rw [prim_step_iff] at hstep
  obtain ⟨K, e1', e2', hfill1, _, hhs⟩ := hstep
  have hK := hsub K e1' hfill1.symm (val_head_stuck hhs)
  subst hK
  simp [Ectx.fill] at hfill1
  subst hfill1
  exact ⟨_, hhs⟩

theorem prim_head_irreducible {e : Exp} {σ : State}
    (hirr : ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬ Reducible e σ :=
  fun hred => not_head_reducible.mpr hirr (prim_head_reducible hred hsub)

theorem head_stuck_stuck {e : Exp} {σ : State}
    (hstuck : ¬e.isValue ∧ ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬e.isValue ∧ ¬ Reducible e σ :=
  ⟨hstuck.1, prim_head_irreducible hstuck.2 hsub⟩

/-! ## notStuck / stuck -/

def notStuck (e : Exp) (σ : State) : Prop :=
  e.isValue ∨ Reducible e σ

theorem NotStuck.of_fill (K : Ectx) {e : Exp} {σ : State}
    (h : notStuck (K.fill e) σ) : notStuck e σ := by
  rcases h with hv | hred
  · exact .inl (Ectx.fill_isValue hv)
  · exact if hv : e.isValue then .inl hv
    else .inr (hred.of_fill K hv)

def stuck (e : Exp) (σ : State) : Prop :=
  ¬ e.isValue ∧ ¬ Reducible e σ

theorem stuck_iff_not_notStuck : stuck e σ ↔ ¬ notStuck e σ := by
  simp [stuck, notStuck, not_or]

theorem Stuck.fill (K : Ectx) {e : Exp} {σ : State}
    (h : stuck e σ) : stuck (K.fill e) σ :=
  ⟨fun hv => h.1 (Ectx.fill_isValue hv),
   fun hred => h.2 (hred.of_fill K h.1)⟩

end ProbLang
end
