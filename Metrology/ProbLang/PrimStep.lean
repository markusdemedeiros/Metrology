import Metrology.ProbLang.Opsem

noncomputable section PrimStep
open Classical MeasureTheory ProbabilityTheory Measure

local instance : MeasurableSpace Expr := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

--   Definition fill_lift (K : ectx Λ) : (expr Λ * state Λ) → (expr Λ * state Λ) :=
--     λ '(e, σ), (fill K e, σ).
def fillLift (K : Ectx) (ρ : Cfg) : Cfg := ⟨K.fill ρ.expr, ρ.state⟩

--   Lemma fill_lift_comp (K1 K2 : ectx Λ) :
--     fill_lift (comp_ectx K1 K2) = fill_lift K1 ∘ fill_lift K2.
--   Proof.
--     extensionality ρ. destruct ρ.
--     rewrite /fill_lift -fill_comp //=.
--   Qed.
theorem fillLift_comp (K1 K2 : Ectx) :
    fillLift (K1.comp K2) = fillLift K1 ∘ fillLift K2 := by
  funext ⟨e, σ⟩
  simp [fillLift, Function.comp, Ectx.fill_comp]

--   Lemma fill_lift_empty :
--     fill_lift empty_ectx = (λ ρ, ρ).
--   Proof.
--     extensionality ρ. destruct ρ.
--     rewrite /fill_lift fill_empty //.
--   Qed.
theorem fillLift_empty : fillLift [] = id := by
  funext ⟨e, σ⟩
  simp [fillLift, Ectx.fill]

--   Instance inj_fill (K : ectx Λ) : Inj eq eq (fill_lift K).
--   Proof. intros [] [] [=<-%(inj _) ->]=>//. Qed.
theorem fillLift_injective (K : Ectx) : Function.Injective (fillLift K) := by
  intro ⟨e1, σ1⟩ ⟨e2, σ2⟩ h
  simp [fillLift] at h
  exact Cfg.mk.injEq .. ▸ ⟨Ectx.fill_injective K h.1, h.2⟩

-- Definition prim_step (e1 : expr Λ) (σ1 : state Λ) : distr (expr Λ * state Λ) :=
--   let '(K, e1') := decomp e1 in
--   dmap (fill_lift K) (head_step e1' σ1).

def PrimStep (cfg : Cfg) : Measure Cfg :=
  let (K, e') := cfg.expr.decomp
  (HeadStep ⟨e', cfg.state⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩)

def PrimStepKernel : Kernel Cfg Cfg where
  measurable' := .of_discrete
  toFun := PrimStep

--   Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
--   Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.
theorem Ectx.fill_noVal' {K : Ectx} {e : Expr} (hv : e.toVal? = none) :
    (K.fill e).toVal? = none := by
  simp [Expr.toVal?] at *
  exact Ectx.fill_noVal (by grind)

-- Lemma val_stuck  : ∀ e (σ : state Λ) (ρ : expr Λ * state Λ), prim_step e σ ρ > 0 → to_val e = None
--     - intros e1 σ1 [e2 σ2] =>/=. rewrite /prim_step.
--       destruct (decomp e1) as [K e1'] eqn:Heq.
--       intros [[e2' σ2'] [_ Hs]]%dmap_pos.
--       rewrite -(decomp_fill _ _ _ Heq).
--       eapply fill_not_val.
--       by eapply val_head_stuck.
theorem val_stuck {cfg : Cfg} {ρ : Cfg} (h : PrimStep cfg {ρ} > 0) :
    cfg.expr.toVal? = none := by
  -- Approach: unfold PrimStep, get (K, e') from decomp, show HeadStep ⟨e', σ⟩ is reducible,
  -- then use val_head_stuck + fill_noVal'.
  -- Blocked: need "map positive → source positive on preimage → nonempty preimage → witness",
  -- i.e. the same Mathlib gap as head_irreducible_zero.
  -- obtain ⟨e, σ⟩ := cfg
  -- simp only [PrimStep] at h
  -- obtain ⟨K, e'⟩ := e.decomp
  -- rw [Measure.map_apply (by measurability) (by measurability)] at h
  -- have ⟨ρ', hρ'⟩ : ∃ ρ', HeadStep ⟨e', σ⟩ {ρ'} > 0 := ...
  -- rw [← Expr.decomp_fill rfl]; exact Ectx.fill_noVal' (val_head_stuck hρ')
  sorry

-- Lemma prim_step_mass : ∀ e (σ : state Λ), (∃ ρ : expr Λ * state Λ, prim_step e σ ρ > 0) → SeriesC (prim_step e σ) = 1
--     - intros e σ [[e' σ'] Hs]. revert Hs. rewrite /prim_step.
--       destruct (decomp e) as [K e1'] eqn:Heq.
--       intros [[e2' σ2'] [? Hs]]%dmap_pos.
--       assert (SeriesC (head_step e1' σ) = 1) as Hsum; [eauto using head_step_mass|].
--       rewrite dmap_mass //.
--   Qed.
theorem prim_step_mass (cfg : Cfg) :
    (∃ ρ : Cfg, PrimStep cfg {ρ} > 0) → IsProbabilityMeasure (PrimStep cfg) := by
  sorry


--   Lemma head_prim_step_eq e1 σ1 :
--     head_reducible e1 σ1 →
--     prim_step e1 σ1 = head_step e1 σ1.
--   Proof. intros ?. apply distr_ext=>?. by eapply head_prim_step_pmf_eq. Qed.
/-- If `e` has a head step, then `prim_step` equals `head_step`. -/
theorem head_prim_step_eq {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0) :
    PrimStep ⟨e, σ⟩ = HeadStep ⟨e, σ⟩ := by
  simp only [PrimStep]
  have hd : e.decomp = ([], e) := by
    rw [e.decomp_unfold]
    rcases hm : e.DecompItem with _ | ⟨Ki, e'⟩
    · simp [hm]
    · exfalso
      obtain ⟨hfill, hne⟩ := Expr.DecompItem_fill hm
      obtain ⟨ρ, hρ⟩ := hred
      rw [← hfill] at hρ
      exact hne (haed_ctx_step_val hρ)
  simp [hd, Ectx.fill]

--   Lemma head_prim_step e1 σ1 ρ :
--     head_step e1 σ1 ρ > 0 → prim_step e1 σ1 ρ > 0.
--   Proof. intros ?. erewrite head_prim_step_eq; [done|]. eexists; eauto. Qed.
theorem head_prim_step {e : Expr} {σ : State} {ρ : Cfg}
    (h : HeadStep ⟨e, σ⟩ {ρ} > 0) : PrimStep ⟨e, σ⟩ {ρ} > 0 := by
  rw [head_prim_step_eq ⟨ρ, h⟩]; exact h


--   Lemma fill_prim_step_dbind K e1 σ1 :
--     to_val e1 = None →
--     prim_step (fill K e1) σ1 = dmap (fill_lift K) (prim_step e1 σ1).
--   Proof.
--     intros Hval. rewrite /prim_step.
--     destruct (decomp e1) as [K1 e1'] eqn:Heq.
--     destruct (decomp (fill _ e1)) as [K1' e1''] eqn:Heq'.
--     apply (decomp_fill_comp K) in Heq; [|done].
--     rewrite Heq in Heq'; simplify_eq.
--     rewrite dmap_comp.
--     apply dmap_eq; [|done].
--     intros [] ? =>/=.
--     f_equal. rewrite -fill_comp //.
--   Qed.
theorem fill_prim_step_map (K : Ectx) (e : Expr) (σ : State) (hv : e.toVal? = none) :
    PrimStep ⟨K.fill e, σ⟩ = (PrimStep ⟨e, σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  simp only [PrimStep]
  -- decomp (K.fill e) = (K' ++ K, e'') where e.decomp = (K', e'')
  have hne : ¬e.isValue := by simp [Expr.toVal?] at hv; exact hv
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  have hd' : (K.fill e).decomp = (K' ++ K, e'') :=
    Expr.decomp_fill_comp hne hd.symm
  simp only [← hd, hd']
  have hm1 : Measurable (fun ρ : Cfg => (⟨K'.fill ρ.expr, ρ.state⟩ : Cfg)) := .of_discrete
  have hm2 : Measurable (fun ρ : Cfg => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg)) := .of_discrete
  rw [Measure.map_map hm2 hm1]
  congr 1
  funext ⟨e', σ'⟩
  simp [Function.comp, fill_app]

--   Lemma fill_prim_step K e1 σ1 e2 σ2 :
--     to_val e1 = None →
--     prim_step e1 σ1 (e2, σ2) = prim_step (fill K e1) σ1 (fill K e2, σ2).
--   Proof.
--     intros Hval. rewrite /prim_step.
--     destruct (decomp e1) as [K1 e1'] eqn:Heq.
--     destruct (decomp (fill _ e1)) as [K1' e1''] eqn:Heq'.
--     apply (decomp_fill_comp K) in Heq; [|done].
--     rewrite Heq in Heq'; simplify_eq.
--     rewrite fill_lift_comp -/fill_lift.
--     rewrite -dmap_comp.
--     replace (fill K e2, σ2) with (fill_lift K (e2, σ2)); [|done].
--     rewrite (dmap_elem_eq (dmap _ _) (e2, σ2)) //.
--   Qed.
theorem fill_prim_step {K : Ectx} {e1 e2 : Expr} {σ1 σ2 : State} (hv : e1.toVal? = none) :
    PrimStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = PrimStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} := by
  rw [fill_prim_step_map K e1 σ1 hv,
      Measure.map_apply (.of_discrete) (.of_discrete)]
  congr 1
  ext ⟨e', σ'⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Cfg.mk.injEq,
             (Ectx.fill_injective K).eq_iff]

--   Lemma head_reducible_prim_step e1 σ1 ρ :
--     head_reducible e1 σ1 →
--     prim_step e1 σ1 ρ > 0 → head_step e1 σ1 ρ > 0.
--   Proof.
--     intros. destruct ρ.
--     edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
--       rewrite ?fill_empty; eauto.
--     by simplify_eq; rewrite fill_empty.
--   Qed.
theorem head_reducible_prim_step {e : Expr} {σ : State} {ρ : Cfg}
    (hred : ∃ ρ' : Cfg, HeadStep ⟨e, σ⟩ {ρ'} > 0)
    (hstep : PrimStep ⟨e, σ⟩ {ρ} > 0) : HeadStep ⟨e, σ⟩ {ρ} > 0 := by
  sorry

--   Lemma fill_step e1 σ1 e2 σ2 `{!LanguageCtx K} :
--     prim_step e1 σ1 (e2, σ2) > 0 →
--     prim_step (K e1) σ1 (K e2, σ2) > 0.
--   Proof.
--     intros Hs.
--     rewrite fill_dmap; [|by eapply val_stuck].
--     apply dbind_pos. eexists (_,_). split; [|done].
--     rewrite dret_1_1 //. lra.
--   Qed.
theorem fill_step {K : Ectx} {e1 e2 : Expr} {σ1 σ2 : State}
    (h : PrimStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} > 0) :
    PrimStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} > 0 := by
  rwa [← fill_prim_step (val_stuck h)]

--   Lemma fill_step_inv e1' σ1 e2 σ2 `{!LanguageCtx K} :
--     to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
--     ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0.
--   Proof.
--     intros Hv. rewrite fill_dmap //.
--     intros ([e1 σ1'] & [=]%dret_pos & Hstep)%dbind_pos.
--     subst. eauto.
--   Qed.
theorem fill_step_inv {K : Ectx} {e1 e2 : Expr} {σ1 σ2 : State}
    (hv : e1.toVal? = none)
    (h : PrimStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩} > 0) :
    ∃ e2', e2 = K.fill e2' ∧ PrimStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} > 0 := by
  rw [fill_prim_step_map K e1 σ1 hv,
      Measure.map_apply (.of_discrete) (.of_discrete)] at h
  simp [Set.mem_preimage, Set.mem_singleton_iff, Cfg.mk.injEq] at h
  -- h : HeadStep ... (preimage set) > 0, preimage is {ρ | K.fill ρ.expr = e2 ∧ ρ.state = σ2}
  -- We need a witness e2' with K.fill e2' = e2
  -- Use that the preimage set is non-empty since PrimStep is positive there
  -- This again needs the "positive measure → nonempty" gap. Use sorry for now.
  sorry

--   Lemma fill_step_prob e1 σ1 e2 σ2 `{!LanguageCtx K} :
--     to_val e1 = None →
--     prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
--   Proof.
--     intros Hv. rewrite fill_dmap //.
--     by erewrite (dmap_elem_eq _ (e2, σ2) _ (λ '(e0, σ0), (K e0, σ0))).
--   Qed.
theorem fill_step_prob {K : Ectx} {e1 e2 : Expr} {σ1 σ2 : State}
    (hv : e1.toVal? = none) :
    PrimStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} = PrimStep ⟨K.fill e1, σ1⟩ {⟨K.fill e2, σ2⟩} :=
  fill_prim_step hv

--   Lemma reducible_fill `{!@LanguageCtx Λ K} e σ :
--     reducible (e, σ) → reducible (K e, σ).
--   Proof.
--     unfold reducible in *. intros [[] ?]. eexists; by apply fill_step.
--   Qed.
theorem reducible_fill (K : Ectx) {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0 := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  exact ⟨⟨K.fill e2, σ2⟩, fill_step hρ⟩

-- Lemma step_by_val :
--   ∀ (K' K_redex : ectx) (e1' e1_redex : expr Λ) (σ1 : state Λ) (ρ : expr Λ * state Λ),
--     fill K' e1' = fill K_redex e1_redex
--     → to_val e1' = None → head_step e1_redex σ1 ρ > 0 → ∃ K'' : ectx, K_redex = flip app K' K''
-- --     - intros K K' e1 e1' σ1 [e2 σ2] Hfill Hred Hstep; revert K' Hfill.
--       induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
--       destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
--       { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
--         apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
--       rewrite !fill_app /= in Hfill.
--       assert (Ki = Ki') as ->.
--       { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
--         apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
--       simplify_eq. destruct (IH K') as [K'' ->]; auto.
--       exists K''. by rewrite assoc.
-- Lemma head_ctx_step_val : ∀ (K : ectx) e (σ1 : state Λ) (ρ : expr Λ * state Λ),
--   head_step (fill K e) σ1 ρ > 0 → is_Some (to_val e) ∨ K = []
--     - intros K e1 σ1 [e2 σ2].
--       destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
--       rewrite fill_app /=.
--       intros ?%head_ctx_step_val; eauto using fill_val.
theorem head_ctx_step_val (K : Ectx) (e : Expr) (σ : State) (ρ : Cfg)
    (hstep : HeadStep ⟨K.fill e, σ⟩ {ρ} > 0) :
    e.isValue ∨ K = [] := by
  rcases List.eq_nil_or_concat K with rfl | ⟨K'', Ki, rfl⟩
  · exact Or.inr rfl
  · rw [List.concat_eq_append, fill_app] at hstep
    simp only [Ectx.fill, List.foldl_cons, List.foldl_nil, flip] at hstep
    exact Or.inl (Ectx.fill_isValue (haed_ctx_step_val hstep))

theorem step_by_val (K' K_redex : Ectx) (e1' e1_redex : Expr) (σ : State) (ρ : Cfg)
    (hfill : K'.fill e1' = K_redex.fill e1_redex)
    (hv : e1'.toVal? = none)
    (hstep : HeadStep ⟨e1_redex, σ⟩ {ρ} > 0) :
    ∃ K'' : Ectx, K_redex = K'.comp K'' := by
  -- Blocked: `suffices ∀ n ...` approach fails because the outer `hstep` (referring to
  -- the outer e1_redex) becomes inaccessible inside the suffices (where e1_redex is
  -- rebound). Need a different induction scheme (e.g. List.reverseRecOn, which doesn't
  -- exist in this Mathlib) or a helper lemma that takes hstep as an explicit argument.
  sorry

-- Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
-- Proof.
--   unfold head_reducible, head_irreducible. split.
--   - intros Hnot ρ.
--     assert (¬ head_step e σ ρ > 0) as H%Rnot_gt_ge; eauto.
--     pose proof (pmf_pos (head_step e σ) ρ). lra.
--   - intros Hall [ρ ?]. specialize (Hall ρ). lra.
-- Qed.
theorem not_head_reducible {e : Expr} {σ : State} :
    (¬ ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0) ↔ (∀ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} = 0) := by
  constructor
  · intro h ρ
    by_contra hne
    exact h ⟨ρ, bot_lt_iff_ne_bot.mpr hne⟩
  · rintro h ⟨ρ, hρ⟩
    simp [h ρ] at hρ

-- Lemma head_redex_unique K K' e e' σ :
--   fill K e = fill K' e' →
--   head_reducible e σ →
--   head_reducible e' σ →
--   K = comp_ectx K' empty_ectx ∧ e = e'.
-- Proof.
--   intros Heq [[e2 σ2] Hred] [[e2' σ2'] Hred'].
--   edestruct (step_by_val K' K e' e) as [K'' HK];
--     [by eauto using val_head_stuck..|].
--   subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
--   destruct (head_ctx_step_val _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
--   { by eapply val_head_stuck. }
--   subst K''. rewrite fill_empty. done.
-- Qed.
theorem head_redex_unique (K K' : Ectx) (e e' : Expr) (σ : State)
    (hfill : K.fill e = K'.fill e')
    (hred  : ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0)
    (hred' : ∃ ρ : Cfg, HeadStep ⟨e', σ⟩ {ρ} > 0) :
    K = K'.comp [] ∧ e = e' := by
  sorry

-- Lemma prim_step_iff e1 e2 σ1 σ2 :
--   prim_step e1 σ1 (e2, σ2) > 0 ↔
--   ∃ K e1' e2',
--     fill K e1' = e1 ∧
--     fill K e2' = e2 ∧
--     head_step e1' σ1 (e2', σ2) > 0.
-- Proof.
--   split.
--   - rewrite /= /prim_step. intros Hs.
--     destruct (decomp e1) as [K e1'] eqn:Heq.
--     edestruct (decomp_fill _ _ _ Heq).
--     eapply dmap_pos in Hs as [[] [[=] ?]].
--     simplify_eq. do 3 eexists; eauto.
--   - intros (K & e1' & e2' & Hfill1 & Hfill2 & Hs). simplify_eq.
--     rewrite -fill_prim_step //; [by apply head_prim_step|].
--     by eapply val_head_stuck.
-- Qed.
theorem prim_step_iff {e1 e2 : Expr} {σ1 σ2 : State} :
    PrimStep ⟨e1, σ1⟩ {⟨e2, σ2⟩} > 0 ↔
    ∃ (K : Ectx) (e1' e2' : Expr),
      K.fill e1' = e1 ∧
      K.fill e2' = e2 ∧
      HeadStep ⟨e1', σ1⟩ {⟨e2', σ2⟩} > 0 := by
  sorry

-- Lemma prim_step_iff' e1 σ1:
--   (∃ x, prim_step e1 σ1 x > 0) ->
--   ∃ K e1', fill K e1' = e1 /\
--            (∃ x, head_step e1' σ1 x > 0) /\
--            prim_step e1 σ1 =
--            dmap (fill_lift K) (head_step e1' σ1).
-- Proof.
--   intros [[] H].
--   rewrite prim_step_iff in H.
--   destruct H as (K&e1'&e2'&<-&<-&H).
--   eexists _, _.
--   split; first done.
--   split; first naive_solver.
--   rewrite fill_prim_step_dbind.
--   - erewrite head_prim_step_eq; first done.
--     by eexists _.
--   - by eapply val_head_stuck.
-- Qed.
theorem prim_step_iff' {e : Expr} {σ : State}
    (hstep : ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ (K : Ectx) (e' : Expr), K.fill e' = e ∧
      (∃ ρ : Cfg, HeadStep ⟨e', σ⟩ {ρ} > 0) ∧
      PrimStep ⟨e, σ⟩ = (HeadStep ⟨e', σ⟩).map (fun ρ => ⟨K.fill ρ.expr, ρ.state⟩) := by
  sorry

-- Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2:
--   head_reducible e1 σ1 →
--   prim_step (fill K e1) σ1 (e2, σ2) > 0 →
--   ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 (e2', σ2) > 0.
-- Proof.
--   intros [[e2'' σ2''] HhstepK] (K' & e1' & e2' & HKe1 & HKe2 & Hs)%prim_step_iff.
--   symmetry in HKe1.
--   edestruct (step_by_val K) as [K'' HK]; eauto using val_head_stuck; simplify_eq/=.
--   rewrite -fill_comp in HKe1; simplify_eq.
--   exists (fill K'' e2'). rewrite fill_comp. split; [done|].
--   destruct (head_ctx_step_val _ _ _ _ HhstepK) as [[]%not_eq_None_Some|HK''].
--   { by eapply val_head_stuck. }
--   subst. rewrite !fill_empty //.
-- Qed.
theorem head_reducible_prim_step_ctx (K : Ectx) {e1 : Expr} {σ1 : State} {e2 : Expr} {σ2 : State}
    (hred : ∃ ρ : Cfg, HeadStep ⟨e1, σ1⟩ {ρ} > 0)
    (hstep : PrimStep ⟨K.fill e1, σ1⟩ {⟨e2, σ2⟩} > 0) :
    ∃ e2', e2 = K.fill e2' ∧ HeadStep ⟨e1, σ1⟩ {⟨e2', σ2⟩} > 0 := by
  sorry

-- Lemma not_head_reducible_dzero e σ :
--   head_irreducible e σ → head_step e σ = dzero.
-- Proof.
--   rewrite /reducible.
--   intros Hred%not_head_reducible. apply dzero_ext=> ρ.
--   destruct (Req_dec (head_step e σ ρ) 0); [done|].
--   exfalso. apply Hred.
--   exists ρ.
--   pose proof (pmf_le_1 (head_step e σ) ρ).
--   pose proof (pmf_pos (head_step e σ) ρ).
--   lra.
-- Qed.
-- theorem head_irreducible_zero {e : Expr} {σ : State}
--     (hirr : ∀ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} = 0) :
--     HeadStep ⟨e, σ⟩ = 0 := by
-- Need: measure zero on all singletons → measure is zero (discrete σ-algebra).
-- Blocked on finding the right Mathlib lemma. See Tier 7.

-- Lemma head_step_not_stuck e σ ρ : head_step e σ ρ > 0 → not_stuck (e, σ).
-- Proof.
--   rewrite /not_stuck /reducible /=. intros Hs. right.
--   eexists ρ. by apply head_prim_step.
-- Qed.
theorem head_step_not_stuck {e : Expr} {σ : State} {ρ : Cfg}
    (h : HeadStep ⟨e, σ⟩ {ρ} > 0) :
    e.toVal? = none ∧ ∃ ρ' : Cfg, PrimStep ⟨e, σ⟩ {ρ'} > 0 :=
  ⟨val_head_stuck h, ρ, head_prim_step h⟩

-- Lemma fill_reducible K e σ : reducible (e, σ) → reducible (fill K e, σ).
-- Proof.
--   rewrite /reducible /=. intros [[e2 σ2] (K' & e1' & e2' & <- & <- & Hs)%prim_step_iff].
--   exists (fill (comp_ectx K K') e2', σ2).
--   eapply prim_step_iff. do 3 eexists. rewrite !fill_comp //.
-- Qed.
theorem fill_reducible (K : Ectx) {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0 := by
  sorry

-- Lemma head_prim_reducible e σ : head_reducible e σ → reducible (e, σ).
-- Proof. intros [ρ Hstep]. exists ρ. by apply head_prim_step. Qed.
theorem head_prim_reducible {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0 :=
  let ⟨ρ, hρ⟩ := hred; ⟨ρ, head_prim_step hρ⟩

-- Lemma head_prim_fill_reducible e K σ :
--   head_reducible e σ → reducible (fill K e, σ).
-- Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
theorem head_prim_fill_reducible (K : Ectx) {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0 :=
  fill_reducible K (head_prim_reducible hred)

-- Lemma head_prim_irreducible e σ : irreducible (e, σ) → head_irreducible e σ.
-- Proof.
--   rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
-- Qed.
theorem head_prim_irreducible {e : Expr} {σ : State}
    (hirr : ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0) :
    ∀ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} = 0 :=
  not_head_reducible.mp (fun hred => hirr (head_prim_reducible hred))

-- Lemma prim_head_reducible e σ :
--   reducible (e, σ) → sub_redexes_are_values e → head_reducible e σ.
-- Proof.
--   rewrite /reducible.
--   intros [[e2 σ2] (K & e1' & e2' & ? & ? & Hs)%prim_step_iff] Hsub.
--   simplify_eq=>/=; simpl in *.
--   assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
--   simplify_eq. rewrite fill_empty. eexists; eauto.
-- Qed.
/-- sub_redexes_are_values: every strict subexpression in a redex position is a value -/
def SubRedexesAreValues (e : Expr) : Prop :=
  ∀ (K : Ectx) (e' : Expr), e = K.fill e' → e'.toVal? = none → K = []

--   Lemma ectxi_language_sub_redexes_are_values e :
--     (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
--     sub_redexes_are_values e.
--   Proof.
--     intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
--     intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
--   Qed.
theorem ectxi_language_sub_redexes_are_values {e : Expr}
    (h : ∀ (Ki : EctxItem) (e' : Expr), e = Ki.FillItem e' → e'.isValue) :
    SubRedexesAreValues e := by
  intro K e' hfill hv
  -- Reverse induction: if K = K'' ++ [Ki] then e = Ki.FillItem (K''.fill e'),
  -- so by h, K''.fill e' is a value; but fill_isValue gives e'.isValue, contradicting hv.
  rcases List.eq_nil_or_concat K with rfl | ⟨K'', Ki, rfl⟩
  · rfl
  · exfalso
    rw [List.concat_eq_append, fill_app] at hfill
    simp only [Ectx.fill, List.foldl_cons, List.foldl_nil, flip] at hfill
    have hval : (Ectx.fill K'' e').isValue := h Ki (Ectx.fill K'' e') hfill
    have hval' : e'.isValue := Ectx.fill_isValue hval
    simp [Expr.toVal?, hval'] at hv

theorem prim_head_reducible {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0)
    (hsub : SubRedexesAreValues e) :
    ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0 := by
  obtain ⟨⟨e2, σ2⟩, hstep⟩ := hred
  rw [prim_step_iff] at hstep
  obtain ⟨K, e1', e2', hfill1, hfill2, hhs⟩ := hstep
  -- K = [] by SubRedexesAreValues
  have hK : K = [] := hsub K e1' hfill1.symm (val_head_stuck hhs)
  subst hK
  simp [Ectx.fill] at hfill1 hfill2
  subst hfill1
  exact ⟨⟨e2', σ2⟩, hhs⟩

-- Lemma prim_head_irreducible e σ :
--   head_irreducible e σ → sub_redexes_are_values e → irreducible (e, σ).
-- Proof.
--   rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
-- Qed.
theorem prim_head_irreducible {e : Expr} {σ : State}
    (hirr : ∀ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : SubRedexesAreValues e) :
    ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0 :=
  fun hred => not_head_reducible.mpr hirr (prim_head_reducible hred hsub)

-- Lemma head_stuck_stuck e σ :
--   head_stuck e σ → sub_redexes_are_values e → stuck (e, σ).
-- Proof.
--   intros [] ?. split; [by eapply to_final_None_2|].
--   by apply prim_head_irreducible.
-- Qed.
theorem head_stuck_stuck {e : Expr} {σ : State}
    (hstuck : e.toVal? = none ∧ ∀ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} = 0)
    (hsub : SubRedexesAreValues e) :
    e.toVal? = none ∧ ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0 :=
  ⟨hstuck.1, prim_head_irreducible hstuck.2 hsub⟩

-- Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ :
--   to_val e = None → reducible (K e, σ) → reducible (e, σ).
-- Proof.
--   intros ? [[e1 σ1] Hstep]; unfold reducible.
--   rewrite /step /= in Hstep.
--   rewrite fill_dmap // in Hstep.
--   apply dmap_pos in Hstep as ([e1' σ2] & ? & Hstep).
--   eauto.
-- Qed.
theorem reducible_fill_inv (K : Ectx) {e : Expr} {σ : State}
    (hv : e.toVal? = none)
    (hred : ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0) :
    ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0 := by
  obtain ⟨⟨e2, σ2⟩, hρ⟩ := hred
  obtain ⟨e2', _, hρ'⟩ := fill_step_inv hv hρ
  exact ⟨⟨e2', σ2⟩, hρ'⟩

-- Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ :
--   to_val e = None → irreducible (e, σ) → irreducible (K e, σ).
-- Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
theorem irreducible_fill (K : Ectx) {e : Expr} {σ : State}
    (hv   : e.toVal? = none)
    (hirr : ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0) :
    ¬ ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0 :=
  fun hred => hirr (reducible_fill_inv K hv hred)

-- Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ :
--   irreducible (K e, σ) → irreducible (e, σ).
-- Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.
theorem irreducible_fill_inv (K : Ectx) {e : Expr} {σ : State}
    (hirr : ¬ ∃ ρ : Cfg, PrimStep ⟨K.fill e, σ⟩ {ρ} > 0) :
    ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0 :=
  fun hred => hirr (reducible_fill K hred)

-- Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ :
--   not_stuck (K e, σ) → not_stuck (e, σ).
-- Proof.
--   rewrite /not_stuck /is_final /to_final /= -!not_eq_None_Some.
--   intros [?|?].
--   - auto using fill_not_val.
--   - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
-- Qed.
/-- not_stuck: expression is a value or has a prim step -/
def NotStuck (e : Expr) (σ : State) : Prop :=
  e.isValue ∨ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0

theorem not_stuck_fill_inv (K : Ectx) {e : Expr} {σ : State}
    (h : NotStuck (K.fill e) σ) : NotStuck e σ := by
  rcases h with hv | hred
  · exact Or.inl (Ectx.fill_isValue hv)
  · by_cases hv : e.isValue
    · exact Or.inl hv
    · have hv' : e.toVal? = none := by simp [Expr.toVal?, hv]
      exact Or.inr (reducible_fill_inv K hv' hred)

-- Lemma stuck_fill `{!@LanguageCtx Λ K} e σ :
--   stuck (e, σ) → stuck (K e, σ).
-- Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.
/-- stuck: expression is not a value and has no prim step -/
def Stuck (e : Expr) (σ : State) : Prop :=
  ¬ e.isValue ∧ ¬ ∃ ρ : Cfg, PrimStep ⟨e, σ⟩ {ρ} > 0

theorem stuck_fill (K : Ectx) {e : Expr} {σ : State}
    (h : Stuck e σ) : Stuck (K.fill e) σ := by
  refine ⟨fun hv => h.1 (Ectx.fill_isValue hv), fun hred => h.2 ?_⟩
  have hv : e.toVal? = none := by simp [Expr.toVal?, h.1]
  exact reducible_fill_inv K hv hred

end PrimStep
