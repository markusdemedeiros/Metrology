import Metrology.ProbLang.Measure
import Metrology.ProbLang.Opsem

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

@[simp]
def fillLift (K : Ectx) (ρ : Cfg) : Cfg := ⟨K.fill ρ.expr, ρ.state⟩

theorem fillLift_comp (K1 K2 : Ectx) : fillLift (K1.comp K2) = fillLift K1 ∘ fillLift K2 := by
  funext ⟨e, σ⟩; simp [Ectx.fill_comp]

theorem fillLift_empty : fillLift [] = id := by
  funext ⟨e, σ⟩; simp [fillLift, Ectx.fill]

theorem fillLift_injective (K : Ectx) : Function.Injective (fillLift K) := by
  rintro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simp only [fillLift, Cfg.mk.injEq] at h
  exact Cfg.mk.injEq .. ▸ ⟨Ectx.fill_injective K h.1, h.2⟩

def primStep (cfg : Cfg) : Measure Cfg :=
  let (K, e') := cfg.expr.decomp
  (headStep ⟨e', cfg.state⟩).map (fillLift K)

def primStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := primStep

theorem Ectx.fill_noVal' {K : Ectx} {e : Exp} (hv : e.toVal? = none) :
    (K.fill e).toVal? = none := by
  simp [Exp.toVal?] at *
  exact Ectx.fill_noVal (by grind)

theorem val_stuck (h : 0 < primStep ⟨e, σ⟩ {ρ}) : e.toVal? = none := by
  simp only [primStep] at h
  set d := e.decomp with hd
  rw [← Exp.decomp_fill hd.symm]
  refine Ectx.fill_noVal' ?_
  rw [Measure.map_apply .of_discrete .of_discrete] at h
  obtain ⟨_, _, hρ'⟩ := measure_pos_of_singleton_pos _ _ h
  exact val_head_stuck hρ'

theorem head_prim_step_eq (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  suffices hd : e.decomp = ([], e) by rw [primStep]; unfold fillLift; simp [Ectx.fill, hd]
  rw [e.decomp_unfold]
  rcases hm : e.decompItem with _ | ⟨Ki, e'⟩
  · simp
  · obtain ⟨hfill, hne⟩ := Exp.decompItem_fill hm
    obtain ⟨ρ, hρ⟩ := hred
    rw [← hfill] at hρ
    exact (hne (head_ctx_step_val hρ)).elim

theorem head_prim_step {e : Exp} {σ : State} {ρ : Cfg}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) : 0 < primStep ⟨e, σ⟩ {ρ} := by
  rw [head_prim_step_eq ⟨ρ, h⟩]; exact h

-- TODO: Cleanup
theorem fill_prim_step_map {K : Ectx} (hv : e.toVal? = none) :
    primStep ⟨K.fill e, σ⟩ = (primStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [primStep]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  have hne : ¬e.isValue := by simp [Exp.toVal?] at hv; exact hv
  have hd' : (K.fill e).decomp = (K' ++ K, e'') := Exp.decomp_fill_comp hne hd.symm
  simp only [hd']
  unfold fillLift
  rw [Measure.map_map .of_discrete .of_discrete]
  congr
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_app]

theorem fill_prim_step {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State} (hv : e1.toVal? = none) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [fill_prim_step_map hv, Measure.map_apply .of_discrete .of_discrete]
  congr 1
  ext ⟨e', σ'⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Cfg.mk.injEq,
             (Ectx.fill_injective K).eq_iff]

theorem fill_step {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (h : 0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩}) :
    0 < primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rwa [← fill_prim_step (val_stuck h)]

theorem fill_step_inv {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (hv : e1.toVal? = none)
    (h : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < primStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [fill_prim_step_map hv, Measure.map_apply .of_discrete .of_discrete] at h
  obtain ⟨⟨e2', σ2'⟩, hmem, hpos⟩ := measure_pos_of_singleton_pos _ _ h
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Cfg.mk.injEq] at hmem
  obtain ⟨hfill, hσ⟩ := hmem
  subst hσ
  exact ⟨e2', hfill.symm, hpos⟩

theorem fill_step_prob {K : Ectx} {e1 e2 : Exp} {σ1 σ2 : State}
    (hv : e1.toVal? = none) :
    primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = primStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} :=
  fill_prim_step hv

theorem reducible_fill (K : Ectx) {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, primStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, primStep ⟨K.fill e, σ⟩ {ρ} > 0 := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  exact ⟨⟨K.fill e2, σ2⟩, fill_step hρ⟩

theorem head_ctx_step_val_ectx (K : Ectx) (e : Exp) (σ : State) (ρ : Cfg)
    (hstep : 0 < headStep ⟨K.fill e, σ⟩ {ρ}) :
    e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_concat K with rfl | ⟨K'', Ki, rfl⟩
  · exact Or.inr rfl
  · rw [List.concat_eq_append, fill_app] at hstep
    simp only [Ectx.fill, List.foldl_cons, List.foldl_nil, flip] at hstep
    exact Or.inl (Ectx.fill_isValue (head_ctx_step_val hstep))

theorem step_by_val (K' K_redex : Ectx) (e1' e1_redex : Exp) (σ : State) (ρ : Cfg)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : e1'.toVal? = none)
    (hstep : 0 < headStep ⟨e1_redex, σ⟩ {ρ}) :
    ∃ K'' : Ectx, K_redex = K'.comp K'' := by
  -- Induction on K' from the right
  induction K' using List.reverseRecOn generalizing K_redex e1_redex with
  | nil =>
    exact ⟨K_redex, (List.append_nil K_redex).symm⟩
  | append_singleton K'_rest Ki' ih =>
    rcases List.eq_nil_or_concat K_redex with rfl | ⟨K_redex_rest, Ki_redex, rfl⟩
    · simp only [Ectx.fill, List.foldl_nil] at hfill
      subst hfill
      have hstep' : headStep ⟨Ki'.fillItem (Ectx.fill K'_rest e1'), σ⟩ {ρ} > 0 := by
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hstep; exact hstep
      have hval := head_ctx_step_val (Ki := Ki') hstep'
      have hv' : ¬e1'.isValue := by simp [Exp.toVal?] at hv; exact hv
      exact absurd (Ectx.fill_isValue hval) hv'
    · simp only [List.concat_eq_append] at hfill ⊢
      have hfill' : Ki'.fillItem (Ectx.fill K'_rest e1') =
          Ki_redex.fillItem (Ectx.fill K_redex_rest e1_redex) := by
        have h1 : (K'_rest ++ [Ki']).foldl (flip EctxItem.fillItem) e1' =
          Ki'.fillItem (K'_rest.foldl (flip EctxItem.fillItem) e1') := List.foldl_append
        have h2 : (K_redex_rest ++ [Ki_redex]).foldl (flip EctxItem.fillItem) e1_redex =
          Ki_redex.fillItem (K_redex_rest.foldl (flip EctxItem.fillItem) e1_redex) := List.foldl_append
        rw [show (K'_rest ++ [Ki']).foldl (flip EctxItem.fillItem) e1' =
          (K_redex_rest ++ [Ki_redex]).foldl (flip EctxItem.fillItem) e1_redex from hfill] at h1
        exact h1.symm.trans h2
      have hv_inner : ¬(Ectx.fill K'_rest e1').isValue := by
        have hv' : ¬e1'.isValue := by simp [Exp.toVal?] at hv; exact hv
        exact Ectx.fill_noVal hv'
      have hv_redex : ¬(Ectx.fill K_redex_rest e1_redex).isValue := by
        have := val_head_stuck hstep
        have hv' : ¬e1_redex.isValue := by simp [Exp.toVal?] at this; exact this
        exact Ectx.fill_noVal hv'
      have hKi := EctxItem.fillItem_noVal_inj hv_inner hv_redex hfill'
      subst hKi
      have he : Ectx.fill K'_rest e1' = Ectx.fill K_redex_rest e1_redex :=
        Ectx.fillItem_injective hfill'
      obtain ⟨K'', hK''⟩ := ih K_redex_rest e1_redex he hstep
      exact ⟨K'', by rw [hK'']; simp [Ectx.comp, List.append_assoc]⟩

theorem not_head_reducible {e : Exp} {σ : State} :
    (¬ ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) ↔ (∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0) := by
  constructor
  · intro h ρ
    by_contra hne
    exact h ⟨ρ, bot_lt_iff_ne_bot.mpr hne⟩
  · rintro h ⟨ρ, hρ⟩
    simp [h ρ] at hρ

theorem head_redex_unique (K K' : Ectx) (e e' : Exp) (σ : State)
    (hfill : K.fill e = K'.fill e')
    (hred  : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ})
    (hred' : ∃ ρ : Cfg, 0 < headStep ⟨e', σ⟩ {ρ}) :
    K = K'.comp [] ∧ e = e' := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  obtain ⟨⟨e2', σ2'⟩, hρ'⟩ := hred'
  obtain ⟨K'', hK⟩ := step_by_val K' K e' e σ ⟨e2, σ2⟩ hfill.symm (val_head_stuck hρ') hρ
  subst hK
  rw [← Ectx.fill_comp] at hfill
  have he : K''.fill e = e' := Ectx.fill_injective K' hfill
  rcases head_ctx_step_val_ectx K'' e σ ⟨e2', σ2'⟩ (he ▸ hρ') with hval | hnil
  · have := val_head_stuck hρ
    simp [Exp.toVal?, hval] at this
  · subst hnil
    simp [Ectx.fill] at he
    exact ⟨rfl, he⟩

theorem prim_step_iff {e1 e2 : Exp} {σ1 σ2 : State} :
    0 < primStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} ↔
    ∃ (K : Ectx) (e1' e2' : Exp),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      0 < headStep ⟨e1', σ1⟩ {⟨e2', σ2⟩} := by
  constructor
  · intro h
    simp only [primStep] at h
    set d := e1.decomp with hd
    obtain ⟨K, e1'⟩ := d
    rw [Measure.map_apply (.of_discrete) (.of_discrete)] at h
    obtain ⟨⟨e2', σ2'⟩, hmem, hpos⟩ := measure_pos_of_singleton_pos _ _ h
    unfold fillLift at hmem
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Cfg.mk.injEq] at hmem
    obtain ⟨hfill2, hσ⟩ := hmem
    subst hσ
    exact ⟨K, e1', e2', Exp.decomp_fill hd.symm, hfill2, hpos⟩
  · rintro ⟨K, e1', e2', rfl, rfl, hhs⟩
    rw [← fill_prim_step (val_head_stuck hhs)]
    exact head_prim_step hhs

theorem prim_step_iff' {e : Exp} {σ : State}
    (hstep : ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}) :
    ∃ (K : Ectx) (e' : Exp), K.fill e' = e ∧
      (∃ ρ : Cfg, 0 < headStep ⟨e', σ⟩ {ρ}) ∧
      primStep ⟨e, σ⟩ = (headStep ⟨e', σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  obtain ⟨⟨e2, σ2⟩, h⟩ := hstep
  rw [prim_step_iff] at h
  obtain ⟨K, e1', e2', hfill1, hfill2, hhs⟩ := h
  refine ⟨K, e1', hfill1, ⟨⟨e2', σ2⟩, hhs⟩, ?_⟩
  rw [← hfill1, fill_prim_step_map (val_head_stuck hhs), head_prim_step_eq ⟨⟨e2', σ2⟩, hhs⟩]

theorem prim_step_mass (cfg : Cfg) :
    (∃ ρ : Cfg, 0 < primStep cfg {ρ}) → IsProbabilityMeasure (primStep cfg) := by
  intro hred
  obtain ⟨K', e'', hfill, hhead_red, hps_eq⟩ := prim_step_iff' hred
  rw [hps_eq]
  haveI := head_step_mass e'' cfg.state hhead_red
  exact Measure.isProbabilityMeasure_map (.of_discrete)

theorem head_reducible_prim_step_ctx (K : Ectx) {e1 : Exp} {σ1 : State} {e2 : Exp} {σ2 : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e1, σ1⟩ {ρ})
    (hstep : 0 < primStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩}) :
    ∃ e2', e2 = K.fill e2' ∧ 0 < headStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} := by
  rw [prim_step_iff] at hstep
  obtain ⟨K', e1', e2', hfill1, hfill2, hhs⟩ := hstep
  obtain ⟨ρ_red, hρ_red⟩ := hred
  obtain ⟨K'', hK''⟩ := step_by_val K' K e1' e1 σ1 ρ_red hfill1 (val_head_stuck hhs) hρ_red
  subst hK''
  simp only [Ectx.comp, fill_app] at hfill1
  have he1' : e1' = Ectx.fill K'' e1 := Ectx.fill_injective K' hfill1
  have hK''nil : K'' = [] := by
    rcases head_ctx_step_val_ectx K'' e1 σ1 ⟨e2', σ2⟩ (he1' ▸ hhs) with hval | hnil
    · have hne : e1.toVal? = none := val_head_stuck hρ_red
      simp [Exp.toVal?, hval] at hne
    · exact hnil
  subst hK''nil
  simp only [Ectx.fill, List.foldl_nil] at he1' hfill2
  exact ⟨e2', hfill2.symm, he1' ▸ hhs⟩

theorem head_reducible_prim_step {e : Exp} {σ : State} {ρ : Cfg}
    (hred : ∃ ρ' : Cfg, 0 < headStep ⟨e, σ⟩ {ρ'})
    (hstep : 0 < primStep ⟨e, σ⟩ {ρ}) : 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨e2, σ2⟩ := ρ
  obtain ⟨e2', hfill, hhs⟩ := head_reducible_prim_step_ctx [] hred hstep
  simp [Ectx.fill] at hfill
  exact hfill ▸ hhs

theorem head_irreducible_zero {e : Exp} {σ : State}
    (hirr : ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0) :
    headStep ⟨e, σ⟩ = 0 := by
  ext S _
  by_contra hne
  have hpos : headStep ⟨e, σ⟩ S > 0 := bot_lt_iff_ne_bot.mpr hne
  obtain ⟨x, _, hx⟩ := measure_pos_of_singleton_pos _ S hpos
  simp [hirr x] at hx

theorem head_step_not_stuck {e : Exp} {σ : State} {ρ : Cfg}
    (h : 0 < headStep ⟨e, σ⟩ {ρ}) :
    e.toVal? = none ∧ ∃ ρ' : Cfg, primStep ⟨e, σ⟩ {ρ'} > 0 :=
  ⟨val_head_stuck h, ρ, head_prim_step h⟩

theorem fill_reducible (K : Ectx) {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}) :
    ∃ ρ : Cfg, primStep ⟨K.fill e, σ⟩ {ρ} > 0 :=
  reducible_fill K hred

theorem head_prim_reducible {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ} :=
  let ⟨ρ, hρ⟩ := hred; ⟨ρ, head_prim_step hρ⟩

theorem head_prim_fill_reducible (K : Ectx) {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ}) :
    ∃ ρ : Cfg, 0 < primStep ⟨K.fill e, σ⟩ {ρ} :=
  fill_reducible K (head_prim_reducible hred)

theorem head_prim_irreducible {e : Exp} {σ : State}
    (hirr : ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}) :
    ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0 :=
  not_head_reducible.mp (fun hred => hirr (head_prim_reducible hred))

def subRedexesAreValues (e : Exp) : Prop :=
  ∀ (K : Ectx) (e' : Exp), e = K.fill e' → e'.toVal? = none → K = []

theorem ectxi_language_subRedexesAreValues {e : Exp}
    (h : ∀ (Ki : EctxItem) (e' : Exp), e = Ki.fillItem e' → e'.isValue) :
    subRedexesAreValues e := by
  intro K e' hfill hv
  rcases List.eq_nil_or_concat K with rfl | ⟨K'', Ki, rfl⟩
  · rfl
  · exfalso
    rw [List.concat_eq_append, fill_app] at hfill
    simp only [Ectx.fill, List.foldl_cons, List.foldl_nil, flip] at hfill
    have hval : (Ectx.fill K'' e').isValue := h Ki (Ectx.fill K'' e') hfill
    have hval' : e'.isValue := Ectx.fill_isValue hval
    simp [Exp.toVal?, hval'] at hv

theorem prim_head_reducible {e : Exp} {σ : State}
    (hred : ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ})
    (hsub : subRedexesAreValues e) :
    ∃ ρ : Cfg, 0 < headStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨⟨e2, σ2⟩, hstep⟩ := hred
  rw [prim_step_iff] at hstep
  obtain ⟨K, e1', e2', hfill1, hfill2, hhs⟩ := hstep
  have hK : K = [] := hsub K e1' hfill1.symm (val_head_stuck hhs)
  subst hK
  simp [Ectx.fill] at hfill1 hfill2
  subst hfill1
  exact ⟨⟨e2', σ2⟩, hhs⟩

theorem prim_head_irreducible {e : Exp} {σ : State}
    (hirr : ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ} :=
  fun hred => not_head_reducible.mpr hirr (prim_head_reducible hred hsub)

theorem head_stuck_stuck {e : Exp} {σ : State}
    (hstuck : e.toVal? = none ∧ ∀ ρ : Cfg, headStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : subRedexesAreValues e) :
    e.toVal? = none ∧ ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ} :=
  ⟨hstuck.1, prim_head_irreducible hstuck.2 hsub⟩

theorem reducible_fill_inv (K : Ectx) {e : Exp} {σ : State}
    (hv : e.toVal? = none)
    (hred : ∃ ρ : Cfg, 0 < primStep ⟨K.fill e, σ⟩ {ρ}) :
    ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ} := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  obtain ⟨e2', _, hρ'⟩ := fill_step_inv hv hρ
  exact ⟨⟨e2', σ2⟩, hρ'⟩

theorem irreducible_fill (K : Ectx) {e : Exp} {σ : State}
    (hv   : e.toVal? = none)
    (hirr : ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}) :
    ¬ ∃ ρ : Cfg, 0 < primStep ⟨K.fill e, σ⟩ {ρ} :=
  fun hred => hirr (reducible_fill_inv K hv hred)

theorem irreducible_fill_inv (K : Ectx) {e : Exp} {σ : State}
    (hirr : ¬ ∃ ρ : Cfg, 0 < primStep ⟨K.fill e, σ⟩ {ρ}) :
    ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ} :=
  fun hred => hirr (reducible_fill K hred)

def notStuck (e : Exp) (σ : State) : Prop :=
  e.isValue ∨ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}

theorem notStuck_fill_inv (K : Ectx) {e : Exp} {σ : State}
    (h : notStuck (K.fill e) σ) : notStuck e σ := by
  rcases h with hv | hred
  · exact Or.inl (Ectx.fill_isValue hv)
  · by_cases hv : e.isValue
    · exact Or.inl hv
    · have hv' : e.toVal? = none := by simp [Exp.toVal?, hv]
      exact Or.inr (reducible_fill_inv K hv' hred)

def stuck (e : Exp) (σ : State) : Prop :=
  ¬ e.isValue ∧ ¬ ∃ ρ : Cfg, 0 < primStep ⟨e, σ⟩ {ρ}

theorem stuck_fill (K : Ectx) {e : Exp} {σ : State}
    (h : stuck e σ) : stuck (K.fill e) σ := by
  refine ⟨fun hv => h.1 (Ectx.fill_isValue hv), fun hred => h.2 ?_⟩
  have hv : e.toVal? = none := by simp [Exp.toVal?, h.1]
  exact reducible_fill_inv K hv hred

end ProbLang
end
