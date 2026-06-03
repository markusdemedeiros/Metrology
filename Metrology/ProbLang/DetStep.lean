module

public import Metrology.ProbLang.CtxStep
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

def nsteps (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

structure PureStep (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ, Reducible e1 σ
  det  : ∀ σ, primStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

class PureExec (φ : Prop) (n : ℕ) (e1 e2 : Exp rT) : Prop where
  pure_exec : φ → nsteps PureStep n e1 e2

structure PureHeadStep (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ : State rT, ∃ ρ : Cfg rT, headStep ⟨e1, σ⟩ {ρ} > 0
  det  : ∀ σ : State rT, headStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

theorem PureHeadStep.toPureStep {e1 e2 : Exp rT} (h : PureHeadStep e1 e2) : PureStep e1 e2 :=
  ⟨fun σ => Reducible.of_head (h.safe σ), fun σ => primStep_eq_headStep (h.safe σ) ▸ h.det σ⟩

theorem PureStep.fill (K : Ectx rT) {e1 e2 : Exp rT} (h : PureStep e1 e2) :
    PureStep (K.fill e1) (K.fill e2) := by
  constructor
  · intro σ
    obtain ⟨⟨e2', σ2⟩, hρ⟩ := h.safe σ
    exact ⟨⟨K.fill e2', σ2⟩, primStep_fill_pos hρ⟩
  · intro σ
    rw [← primStep_fill_singleton (val_stuck (h.safe σ).choose_spec)]
    exact h.det σ

theorem PureStep.fill_nsteps (K : Ectx rT) {n : ℕ} {e1 e2 : Exp rT}
    (h : nsteps PureStep n e1 e2) :
    nsteps PureStep n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => simp [nsteps] at h; subst h; simp [nsteps]
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

theorem PureExec.fill (K : Ectx rT) {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec φ n e1 e2] : PureExec φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := PureStep.fill_nsteps K (h.pure_exec hφ)

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem PureExec.reducible {σ : State rT} {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    Reducible e1 σ := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact hstep.safe σ

theorem PureExec.not_val {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    ¬e1.isValue := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  obtain ⟨ρ, hρ⟩ := hstep.safe default
  exact val_stuck hρ

theorem rtc_pure_step_val {n : ℕ} {v : Val rT} {e : Exp rT}
    (h : nsteps PureStep n v.1 e) :
    e.toVal? = some v := by
  induction n generalizing e with
  | zero =>
    simp [nsteps] at h
    subst h
    exact Exp.toVal?_ofVal v
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    obtain ⟨ρ, hρ⟩ := hstep.safe default
    exact absurd v.2.toIsValue (val_stuck hρ)

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem as_val_isSome {e : Exp rT} (h : ∃ v : Val rT, v.1 = e) : e.isValue := by
  obtain ⟨⟨_, hv⟩, rfl⟩ := h
  exact hv.toIsValue


/-- Build a `PureHeadStep e1 e2` from a proof that `headStep` always maps
    omit [Countable rT] [MeasurableSingletonClass rT] in
    `⟨e1, σ⟩` to `dirac ⟨e2, σ⟩`. The `safe` field is derived automatically. -/
theorem PureHeadStep.of_det (e1 e2 : Exp rT)
    (hdet : ∀ σ, headStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1) :
    PureHeadStep e1 e2 := by
  refine ⟨fun σ => ⟨⟨e2, σ⟩, ?_⟩, hdet⟩
  have h1 := hdet σ; positivity

/-- One step followed by n steps gives n+1 steps. -/
theorem nsteps_succ_intro {r : α → α → Prop} {n : ℕ} {a c b : α}
    (h1 : r a c) (h2 : nsteps r n c b) : nsteps r (n + 1) a b :=
  ⟨c, h1, h2⟩

/-- A single deterministic head step at a fixed state `σ`.
    Weaker than `PureHeadStep` (which requires all states); useful when
    the next expression may depend on `σ` (e.g. heap operations). -/
structure DetHeadStep (cfg1 cfg2 : Cfg rT) : Prop where
  safe : ∃ ρ : Cfg rT, 0 < headStep cfg1 {ρ}
  det  : headStep cfg1 {cfg2} = 1

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetHeadStep.pos {cfg1 cfg2 : Cfg rT} (h : DetHeadStep cfg1 cfg2) : 0 < headStep cfg1 {cfg2} :=
  h.det ▸ one_pos

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetHeadStep.of_det (cfg1 cfg2 : Cfg rT)
    (hdet : headStep cfg1 {cfg2} = 1) : DetHeadStep cfg1 cfg2 :=
  ⟨⟨cfg2, hdet ▸ one_pos⟩, hdet⟩

-- TODO: This should not be stated in terms of atoms, so that it can be generalized to the measurable case.
structure DetStep (cfg1 cfg2 : Cfg rT) : Prop where
  safe : Reducible cfg1.expr cfg1.state
  det  : primStep cfg1 {cfg2} = 1

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetStep.pos {cfg1 cfg2 : Cfg rT} (h : DetStep cfg1 cfg2) : 0 < primStep cfg1 {cfg2} :=
  h.det ▸ one_pos

theorem DetHeadStep.toDetStep {cfg1 cfg2 : Cfg rT} (h : DetHeadStep cfg1 cfg2) : DetStep cfg1 cfg2 where
  safe := ⟨_, primStep_pos_of_headStep h.pos⟩
  det := by obtain ⟨e1, σ1⟩ := cfg1; rw [primStep_eq_headStep h.safe]; exact h.det

class DetExec (n : ℕ) (cfg1 cfg2 : Cfg rT) : Prop where
  det_exec : nsteps DetStep n cfg1 cfg2

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetExec.succ {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

theorem DetHeadStep.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

theorem DetHeadStep.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

theorem DetHeadStep.cond_true (et ef : Exp rT) (σ : State rT) :
    DetHeadStep ⟨.cond (.lit (.bool true)) et ef, σ⟩ ⟨et, σ⟩ :=
  .of_det _ _ (by simp [headStep])

theorem DetHeadStep.cond_false (et ef : Exp rT) (σ : State rT) :
    DetHeadStep ⟨.cond (.lit (.bool false)) et ef, σ⟩ ⟨ef, σ⟩ :=
  .of_det _ _ (by simp [headStep])

theorem DetHeadStep.app_lam {body v : Exp rT}
    (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.app (.lam body) v, σ⟩ ⟨Exp.open' body v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

/-- `PureHeadStep` for `(λ. body) v` when `v` is a value. -/
theorem PureHeadStep.app_lam {body v : Exp rT} (hv : IsVal v) :
    PureHeadStep (.app (.lam body) v) (Exp.open' body v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

/-- `PureExec` instance: `(λ. body) v` beta-reduces in 1 step when `v` is a value. -/
instance pureExec_app_lam {body v : Exp rT} :
    PureExec (v.isValue) 1 (.app (.lam body) v) (Exp.open' body v) where
  pure_exec hv := ⟨_, (PureHeadStep.app_lam hv.some).toPureStep, rfl⟩

/-- `PureHeadStep` for `if true then et else ef → et`. -/
theorem PureHeadStep.cond_true (et ef : Exp rT) :
    PureHeadStep (.cond (.lit (.bool true)) et ef) et :=
  .of_det _ _ fun σ => by simp [headStep]

/-- `PureHeadStep` for `if false then et else ef → ef`. -/
theorem PureHeadStep.cond_false (et ef : Exp rT) :
    PureHeadStep (.cond (.lit (.bool false)) et ef) ef :=
  .of_det _ _ fun σ => by simp [headStep]

instance pureExec_cond_true {et ef : Exp rT} :
    PureExec True 1 (.cond (.lit (.bool true)) et ef) et where
  pure_exec _ := ⟨_, (PureHeadStep.cond_true et ef).toPureStep, rfl⟩

instance pureExec_cond_false {et ef : Exp rT} :
    PureExec True 1 (.cond (.lit (.bool false)) et ef) ef where
  pure_exec _ := ⟨_, (PureHeadStep.cond_false et ef).toPureStep, rfl⟩

/-- `PureHeadStep` for `fst (v1, v2) → v1` when both are values. -/
theorem PureHeadStep.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.fst (.pair e1 e2)) e1 :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

/-- `PureHeadStep` for `snd (v1, v2) → v2`. -/
theorem PureHeadStep.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep (.snd (.pair e1 e2)) e2 :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

instance pureExec_fst_pair {e1 e2 : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.fst (.pair e1 e2)) e1 where
  pure_exec h := ⟨_, (PureHeadStep.fst_pair h.1.some h.2.some).toPureStep, rfl⟩

instance pureExec_snd_pair {e1 e2 : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue) 1 (.snd (.pair e1 e2)) e2 where
  pure_exec h := ⟨_, (PureHeadStep.snd_pair h.1.some h.2.some).toPureStep, rfl⟩

/-- `PureHeadStep` for `case (inl v) el er → el v`. -/
theorem PureHeadStep.case_inl {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep (.case (.inl v) el er) (el.app v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

theorem PureHeadStep.case_inr {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep (.case (.inr v) el er) (er.app v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

instance pureExec_case_inl {v el er : Exp rT} :
    PureExec v.isValue 1 (.case (.inl v) el er) (el.app v) where
  pure_exec hv := ⟨_, (PureHeadStep.case_inl hv.some).toPureStep, rfl⟩

instance pureExec_case_inr {v el er : Exp rT} :
    PureExec v.isValue 1 (.case (.inr v) el er) (er.app v) where
  pure_exec hv := ⟨_, (PureHeadStep.case_inr hv.some).toPureStep, rfl⟩

/-- `PureHeadStep` for `binop op v1 v2 → r` when both are values and eval succeeds. -/
theorem PureHeadStep.binop {op : BinOp} {e1 e2 r : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2) (heval : op.eval e1 e2 = some r) :
    PureHeadStep (.binop op e1 e2) r :=
  .of_det _ _ fun σ => by
    simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval]

instance pureExec_binop {op : BinOp} {e1 e2 r : Exp rT} :
    PureExec (e1.isValue ∧ e2.isValue ∧ op.eval e1 e2 = some r) 1
      (.binop op e1 e2) r where
  pure_exec h := ⟨_, (PureHeadStep.binop h.1.some h.2.1.some h.2.2).toPureStep, rfl⟩

/-- `PureHeadStep` for `unop op v → r`. -/
theorem PureHeadStep.unop {op : UnOp} {e r : Exp rT}
    (hv : IsVal e) (heval : op.eval e = some r) :
    PureHeadStep (.unop op e) r :=
  .of_det _ _ fun σ => by
    simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval]

instance pureExec_unop {op : UnOp} {e r : Exp rT} :
    PureExec (e.isValue ∧ op.eval e = some r) 1 (.unop op e) r where
  pure_exec h := ⟨_, (PureHeadStep.unop h.1.some h.2).toPureStep, rfl⟩

/-- `PureHeadStep` for `(fix body) v → (open' body (fix body)) v`. -/
theorem PureHeadStep.app_fix {body v : Exp rT} (hv : IsVal v) :
    PureHeadStep (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

instance pureExec_app_fix {body v : Exp rT} :
    PureExec v.isValue 1 (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) where
  pure_exec hv := ⟨_, (PureHeadStep.app_fix hv.some).toPureStep, rfl⟩

/-- `PureHeadStep` for `scrut v p` when match succeeds. -/
theorem PureHeadStep.scrut_some {v : Exp rT} {p : Pat rT} {b : Exp rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = some b) :
    PureHeadStep (.scrut v p) (.inl b) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv, hmatch]

/-- `PureHeadStep` for `scrut v p` when match fails. -/
theorem PureHeadStep.scrut_none {v : Exp rT} {p : Pat rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = none) :
    PureHeadStep (.scrut v p) (.inr (.lit .unit)) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv, hmatch]

instance pureExec_scrut_some {v : Exp rT} {p : Pat rT} {b : Exp rT} :
    PureExec (v.isValue ∧ Pat.tryMatch p v = some b) 1 (.scrut v p) (.inl b) where
  pure_exec h := ⟨_, (PureHeadStep.scrut_some h.1.some h.2).toPureStep, rfl⟩

instance pureExec_scrut_none {v : Exp rT} {p : Pat rT} :
    PureExec (v.isValue ∧ Pat.tryMatch p v = none) 1 (.scrut v p) (.inr (.lit .unit)) where
  pure_exec h := ⟨_, (PureHeadStep.scrut_none h.1.some h.2).toPureStep, rfl⟩

theorem DetHeadStep.app_fix {body v : Exp rT}
    (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.app (.fix body) v, σ⟩
      ⟨Exp.app (Exp.open' body (.fix body)) v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.unop {op : UnOp} {e result : Exp rT}
    (hv : IsVal e)
    (heval : UnOp.eval op e = some result) (σ : State rT) :
    DetHeadStep ⟨.unop op e, σ⟩ ⟨result, σ⟩ :=
  .of_det _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval])

theorem DetHeadStep.binop {op : BinOp} {e1 e2 result : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2)
    (heval : BinOp.eval op e1 e2 = some result) (σ : State rT) :
    DetHeadStep ⟨.binop op e1 e2, σ⟩ ⟨result, σ⟩ :=
  .of_det _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval])

theorem DetHeadStep.case_inl {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.case (.inl v) el er, σ⟩ ⟨el.app v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.case_inr {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.case (.inr v) el er, σ⟩ ⟨er.app v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.alloc {v : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep ⟨.alloc v, σ⟩ ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv⟩)⟩ := by
  obtain ⟨w, hw⟩ := hv.check?_some
  exact .of_det _ _ (by simp [headStep, Exp.asValM, Exp.toVal?, hw, IsVal.subsingleton hv w])

theorem DetHeadStep.load {ℓ : Loc} {v : Val rT} (σ : State rT) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨.ofVal v, σ⟩ :=
  .of_det _ _ (by simp [headStep, hlookup])

theorem DetHeadStep.store {ℓ : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (_hv : IsVal e) (σ : State rT)
    (hlookup : σ.heap[ℓ]? = some v_old)
    (hnew : e.toVal? = some v_new) :
    DetHeadStep ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ.update_heap (·.insert ℓ v_new)⟩ :=
  .of_det _ _ (by simp [headStep, Exp.asValM, hnew, hlookup])

theorem DetStep.fill (K : Ectx rT) {cfg1 cfg2 : Cfg rT} (h : DetStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := h.safe.fill K
  det := by rw [← primStep_fill_singleton (val_stuck h.pos)]; exact h.det

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetExec.refl (cfg : Cfg rT) : DetExec 0 cfg cfg where
  det_exec := rfl

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem DetExec.cons {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) (hrest : DetExec n cfg2 cfg3) :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

end ProbLang
end
