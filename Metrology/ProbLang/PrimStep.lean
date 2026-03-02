import Metrology.ProbLang.Opsem

noncomputable section PrimStep
open Classical MeasureTheory ProbabilityTheory Measure

local instance : MeasurableSpace Expr := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

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


--   Lemma head_prim_step e1 σ1 ρ :
--     head_step e1 σ1 ρ > 0 → prim_step e1 σ1 ρ > 0.
--   Proof. intros ?. erewrite head_prim_step_eq; [done|]. eexists; eauto. Qed.
theorem head_prim_step {e : Expr} {σ : State} {ρ : Cfg}
    (h : HeadStep ⟨e, σ⟩ {ρ} > 0) : PrimStep ⟨e, σ⟩ {ρ} > 0 := by
  sorry


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
  sorry

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
  sorry

--   Lemma head_prim_step_eq e1 σ1 :
--     head_reducible e1 σ1 →
--     prim_step e1 σ1 = head_step e1 σ1.
--   Proof. intros ?. apply distr_ext=>?. by eapply head_prim_step_pmf_eq. Qed.
/-- If `e` has a head step, then `prim_step` equals `head_step`. -/
theorem head_prim_step_eq {e : Expr} {σ : State}
    (hred : ∃ ρ : Cfg, HeadStep ⟨e, σ⟩ {ρ} > 0) :
    PrimStep ⟨e, σ⟩ = HeadStep ⟨e, σ⟩ := by
  sorry

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

end PrimStep
