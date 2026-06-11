module

public import Metrology.ProbLang.CtxStep
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

def nsteps (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

@[discrete]
structure PureStep_discrete (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ, Discrete.Reducible e1 σ
  det  : ∀ σ, primStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

@[discrete]
class PureExec_discrete (φ : Prop) (n : ℕ) (e1 e2 : Exp rT) : Prop where
  pure_exec : φ → nsteps PureStep_discrete n e1 e2

@[discrete]
structure PureHeadStep_discrete (e1 e2 : Exp rT) : Prop where
  safe : ∀ σ : State rT, ∃ ρ : Cfg rT, headStep ⟨e1, σ⟩ {ρ} > 0
  det  : ∀ σ : State rT, headStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

@[discrete]
theorem PureHeadStep_discrete.toPureStep {e1 e2 : Exp rT} (h : PureHeadStep_discrete e1 e2) : PureStep_discrete e1 e2 :=
  ⟨fun σ => Discrete.Reducible.of_head (h.safe σ), fun σ => primStep_eq_headStep_discrete (h.safe σ) ▸ h.det σ⟩

@[discrete]
theorem PureStep_discrete.fill [Countable rT] [MeasurableSingletonClass rT]
  (K : Ectx rT) {e1 e2 : Exp rT} (h : PureStep_discrete e1 e2) :
    PureStep_discrete (K.fill e1) (K.fill e2) := by
  constructor
  · intro σ
    obtain ⟨⟨e2', σ2⟩, hρ⟩ := h.safe σ
    exact ⟨⟨K.fill e2', σ2⟩, primStep_fill_pos_discrete hρ⟩
  · intro σ
    rw [← primStep_fill_singleton (Discrete.val_stuck (h.safe σ).choose_spec)]
    exact h.det σ

@[discrete]
theorem PureStep_discrete.fill_nsteps [Countable rT] [MeasurableSingletonClass rT]
  (K : Ectx rT) {n : ℕ} {e1 e2 : Exp rT}
    (h : nsteps PureStep_discrete n e1 e2) :
    nsteps PureStep_discrete n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => simp [nsteps] at h; subst h; simp [nsteps]
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

@[discrete]
theorem PureExec_discrete.fill [Countable rT] [MeasurableSingletonClass rT]
  (K : Ectx rT) {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    [h : PureExec_discrete φ n e1 e2] : PureExec_discrete φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := PureStep_discrete.fill_nsteps K (h.pure_exec hφ)

@[discrete]
theorem PureExec_discrete.reducible {σ : State rT} {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec_discrete φ (n + 1) e1 e2] :
    Discrete.Reducible e1 σ := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact hstep.safe σ

@[discrete]
theorem PureExec_discrete.not_val [Countable rT] [MeasurableSingletonClass rT] {φ : Prop} {n : ℕ} {e1 e2 : Exp rT}
    (hφ : φ) [h : PureExec_discrete φ (n + 1) e1 e2] :
    ¬e1.isValue := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  obtain ⟨ρ, hρ⟩ := hstep.safe default
  exact Discrete.val_stuck hρ

@[discrete]
theorem rtc_pure_step_val_discrete [Countable rT] [MeasurableSingletonClass rT] {n : ℕ} {v : Val rT} {e : Exp rT}
    (h : nsteps PureStep_discrete n v.1 e) :
    e.toVal? = some v := by
  induction n generalizing e with
  | zero =>
    simp [nsteps] at h
    subst h
    exact Exp.toVal?_ofVal v
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    obtain ⟨ρ, hρ⟩ := hstep.safe default
    exact absurd v.2.toIsValue (Discrete.val_stuck hρ)

@[discrete]
theorem as_val_isSome_discrete {e : Exp α} (h : ∃ v : Val α, v.1 = e) : e.isValue := by
  obtain ⟨⟨_, hv⟩, rfl⟩ := h
  exact hv.toIsValue


/-- Build a `PureHeadStep_discrete e1 e2` from a proof that `headStep` always maps
    omit [Countable rT] [MeasurableSingletonClass rT] in
    `⟨e1, σ⟩` to `dirac ⟨e2, σ⟩`. The `safe` field is derived automatically. -/
@[discrete]
theorem PureHeadStep_discrete.of_det (e1 e2 : Exp rT)
    (hdet : ∀ σ, headStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1) :
    PureHeadStep_discrete e1 e2 := by
  refine ⟨fun σ => ⟨⟨e2, σ⟩, ?_⟩, hdet⟩
  have h1 := hdet σ; positivity

/-- One step followed by n steps gives n+1 steps. -/
@[discrete]
theorem nsteps_succ_intro_discrete {r : α → α → Prop} {n : ℕ} {a c b : α}
    (h1 : r a c) (h2 : nsteps r n c b) : nsteps r (n + 1) a b :=
  ⟨c, h1, h2⟩

/-- A single deterministic head step at a fixed state `σ`.
    Weaker than `PureHeadStep_discrete` (which requires all states); useful when
    the next expression may depend on `σ` (e.g. heap operations). -/
@[discrete]
structure DetHeadStep_discrete (cfg1 cfg2 : Cfg rT) : Prop where
  safe : ∃ ρ : Cfg rT, 0 < headStep cfg1 {ρ}
  det  : headStep cfg1 {cfg2} = 1

@[discrete]
theorem DetHeadStep_discrete.pos_discrete {cfg1 cfg2 : Cfg rT} (h : DetHeadStep_discrete cfg1 cfg2) : 0 < headStep cfg1 {cfg2} :=
  h.det ▸ one_pos

@[discrete]
theorem DetHeadStep_discrete.of_det_discrete (cfg1 cfg2 : Cfg rT)
    (hdet : headStep cfg1 {cfg2} = 1) : DetHeadStep_discrete cfg1 cfg2 :=
  ⟨⟨cfg2, hdet ▸ one_pos⟩, hdet⟩

-- TODO: This should not be stated in terms of atoms, so that it can be generalized to the measurable case.
@[discrete]
structure DetStep_discrete (cfg1 cfg2 : Cfg rT) : Prop where
  safe : Discrete.Reducible cfg1.expr cfg1.state
  det  : primStep cfg1 {cfg2} = 1

@[discrete]
theorem DetStep_discrete.pos_discrete {cfg1 cfg2 : Cfg rT} (h : DetStep_discrete cfg1 cfg2) : 0 < primStep cfg1 {cfg2} :=
  h.det ▸ one_pos

@[discrete]
theorem DetHeadStep_discrete.toDetStep {cfg1 cfg2 : Cfg rT} (h : DetHeadStep_discrete cfg1 cfg2) : DetStep_discrete cfg1 cfg2 where
  safe := ⟨_, primStep_pos_of_headStep_discrete h.pos_discrete⟩
  det := by obtain ⟨e1, σ1⟩ := cfg1; rw [primStep_eq_headStep_discrete h.safe]; exact h.det

@[discrete]
class DetExec_discrete (n : ℕ) (cfg1 cfg2 : Cfg rT) : Prop where
  det_exec : nsteps DetStep_discrete n cfg1 cfg2

@[discrete]
theorem DetExec_discrete.succ {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep_discrete cfg1 cfg2) [hrest : DetExec_discrete n cfg2 cfg3] :
    DetExec_discrete (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

@[discrete]
theorem DetHeadStep_discrete.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep_discrete ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

@[discrete]
theorem DetHeadStep_discrete.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State rT) :
    DetHeadStep_discrete ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

@[discrete]
theorem DetHeadStep_discrete.cond_true (et ef : Exp rT) (σ : State rT) :
    DetHeadStep_discrete ⟨.cond (.lit (.bool true)) et ef, σ⟩ ⟨et, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep])

@[discrete]
theorem DetHeadStep_discrete.cond_false (et ef : Exp rT) (σ : State rT) :
    DetHeadStep_discrete ⟨.cond (.lit (.bool false)) et ef, σ⟩ ⟨ef, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep])

@[discrete]
theorem DetHeadStep_discrete.app_lam {body v : Exp rT}
    (hv : IsVal v) (σ : State rT) :
    DetHeadStep_discrete ⟨.app (.lam body) v, σ⟩ ⟨Exp.open' body v, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' hv])

/-- `PureHeadStep_discrete` for `(λ. body) v` when `v` is a value. -/
@[discrete]
theorem PureHeadStep_discrete.app_lam {body v : Exp rT} (hv : IsVal v) :
    PureHeadStep_discrete (.app (.lam body) v) (Exp.open' body v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

/-- `PureExec_discrete` instance: `(λ. body) v` beta-reduces in 1 step when `v` is a value. -/
@[discrete]
instance pureExec_app_lam_discrete {body v : Exp rT} :
    PureExec_discrete (v.isValue) 1 (.app (.lam body) v) (Exp.open' body v) where
  pure_exec hv := ⟨_, (PureHeadStep_discrete.app_lam hv.some).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `if true then et else ef → et`. -/
@[discrete]
theorem PureHeadStep_discrete.cond_true (et ef : Exp rT) :
    PureHeadStep_discrete (.cond (.lit (.bool true)) et ef) et :=
  .of_det _ _ fun σ => by simp [headStep]

/-- `PureHeadStep_discrete` for `if false then et else ef → ef`. -/
@[discrete]
theorem PureHeadStep_discrete.cond_false (et ef : Exp rT) :
    PureHeadStep_discrete (.cond (.lit (.bool false)) et ef) ef :=
  .of_det _ _ fun σ => by simp [headStep]

@[discrete]
instance pureExec_cond_true_discrete {et ef : Exp rT} :
    PureExec_discrete True 1 (.cond (.lit (.bool true)) et ef) et where
  pure_exec _ := ⟨_, (PureHeadStep_discrete.cond_true et ef).toPureStep, rfl⟩

@[discrete]
instance pureExec_cond_false_discrete {et ef : Exp rT} :
    PureExec_discrete True 1 (.cond (.lit (.bool false)) et ef) ef where
  pure_exec _ := ⟨_, (PureHeadStep_discrete.cond_false et ef).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `fst (v1, v2) → v1` when both are values. -/
@[discrete]
theorem PureHeadStep_discrete.fst_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep_discrete (.fst (.pair e1 e2)) e1 :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

/-- `PureHeadStep_discrete` for `snd (v1, v2) → v2`. -/
@[discrete]
theorem PureHeadStep_discrete.snd_pair {e1 e2 : Exp rT} (h1 : IsVal e1) (h2 : IsVal e2) :
    PureHeadStep_discrete (.snd (.pair e1 e2)) e2 :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2]

@[discrete]
instance pureExec_fst_pair_discrete {e1 e2 : Exp rT} :
    PureExec_discrete (e1.isValue ∧ e2.isValue) 1 (.fst (.pair e1 e2)) e1 where
  pure_exec h := ⟨_, (PureHeadStep_discrete.fst_pair h.1.some h.2.some).toPureStep, rfl⟩

@[discrete]
instance pureExec_snd_pair_discrete {e1 e2 : Exp rT} :
    PureExec_discrete (e1.isValue ∧ e2.isValue) 1 (.snd (.pair e1 e2)) e2 where
  pure_exec h := ⟨_, (PureHeadStep_discrete.snd_pair h.1.some h.2.some).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `case (inl v) el er → el v`. -/
@[discrete]
theorem PureHeadStep_discrete.case_inl {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep_discrete (.case (.inl v) el er) (el.app v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

@[discrete]
theorem PureHeadStep_discrete.case_inr {v el er : Exp rT} (hv : IsVal v) :
    PureHeadStep_discrete (.case (.inr v) el er) (er.app v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

@[discrete]
instance pureExec_case_inl_discrete {v el er : Exp rT} :
    PureExec_discrete v.isValue 1 (.case (.inl v) el er) (el.app v) where
  pure_exec hv := ⟨_, (PureHeadStep_discrete.case_inl hv.some).toPureStep, rfl⟩

@[discrete]
instance pureExec_case_inr_discrete {v el er : Exp rT} :
    PureExec_discrete v.isValue 1 (.case (.inr v) el er) (er.app v) where
  pure_exec hv := ⟨_, (PureHeadStep_discrete.case_inr hv.some).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `binop op v1 v2 → r` when both are values and eval succeeds. -/
@[discrete]
theorem PureHeadStep_discrete.binop {op : BinOp} {e1 e2 r : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2) (heval : op.eval e1 e2 = some r) :
    PureHeadStep_discrete (.binop op e1 e2) r :=
  .of_det _ _ fun σ => by
    simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval]

@[discrete]
instance pureExec_binop_discrete {op : BinOp} {e1 e2 r : Exp rT} :
    PureExec_discrete (e1.isValue ∧ e2.isValue ∧ op.eval e1 e2 = some r) 1
      (.binop op e1 e2) r where
  pure_exec h := ⟨_, (PureHeadStep_discrete.binop h.1.some h.2.1.some h.2.2).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `unop op v → r`. -/
@[discrete]
theorem PureHeadStep_discrete.unop {op : UnOp} {e r : Exp rT}
    (hv : IsVal e) (heval : op.eval e = some r) :
    PureHeadStep_discrete (.unop op e) r :=
  .of_det _ _ fun σ => by
    simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval]

@[discrete]
instance pureExec_unop_discrete {op : UnOp} {e r : Exp rT} :
    PureExec_discrete (e.isValue ∧ op.eval e = some r) 1 (.unop op e) r where
  pure_exec h := ⟨_, (PureHeadStep_discrete.unop h.1.some h.2).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `(fix body) v → (open' body (fix body)) v`. -/
@[discrete]
theorem PureHeadStep_discrete.app_fix {body v : Exp rT} (hv : IsVal v) :
    PureHeadStep_discrete (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv]

@[discrete]
instance pureExec_app_fix_discrete {body v : Exp rT} :
    PureExec_discrete v.isValue 1 (.app (.fix body) v) (Exp.app (Exp.open' body (.fix body)) v) where
  pure_exec hv := ⟨_, (PureHeadStep_discrete.app_fix hv.some).toPureStep, rfl⟩

/-- `PureHeadStep_discrete` for `scrut v p` when match succeeds. -/
@[discrete]
theorem PureHeadStep_discrete.scrut_some {v : Exp rT} {p : Pat rT} {b : Exp rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = some b) :
    PureHeadStep_discrete (.scrut v p) (.inl b) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv, hmatch]

/-- `PureHeadStep_discrete` for `scrut v p` when match fails. -/
@[discrete]
theorem PureHeadStep_discrete.scrut_none {v : Exp rT} {p : Pat rT}
    (hv : IsVal v) (hmatch : Pat.tryMatch p v = none) :
    PureHeadStep_discrete (.scrut v p) (.inr (.lit .unit)) :=
  .of_det _ _ fun σ => by simp [headStep, Exp.isValM_some' hv, hmatch]

@[discrete]
instance pureExec_scrut_some_discrete {v : Exp rT} {p : Pat rT} {b : Exp rT} :
    PureExec_discrete (v.isValue ∧ Pat.tryMatch p v = some b) 1 (.scrut v p) (.inl b) where
  pure_exec h := ⟨_, (PureHeadStep_discrete.scrut_some h.1.some h.2).toPureStep, rfl⟩

@[discrete]
instance pureExec_scrut_none_discrete {v : Exp rT} {p : Pat rT} :
    PureExec_discrete (v.isValue ∧ Pat.tryMatch p v = none) 1 (.scrut v p) (.inr (.lit .unit)) where
  pure_exec h := ⟨_, (PureHeadStep_discrete.scrut_none h.1.some h.2).toPureStep, rfl⟩

@[discrete]
theorem DetHeadStep_discrete.app_fix {body v : Exp rT}
    (hv : IsVal v) (σ : State rT) :
    DetHeadStep_discrete ⟨.app (.fix body) v, σ⟩
      ⟨Exp.app (Exp.open' body (.fix body)) v, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' hv])

@[discrete]
theorem DetHeadStep_discrete.unop {op : UnOp} {e result : Exp rT}
    (hv : IsVal e)
    (heval : UnOp.eval op e = some result) (σ : State rT) :
    DetHeadStep_discrete ⟨.unop op e, σ⟩ ⟨result, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval])

@[discrete]
theorem DetHeadStep_discrete.binop {op : BinOp} {e1 e2 result : Exp rT}
    (h1 : IsVal e1) (h2 : IsVal e2)
    (heval : BinOp.eval op e1 e2 = some result) (σ : State rT) :
    DetHeadStep_discrete ⟨.binop op e1 e2, σ⟩ ⟨result, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval])

@[discrete]
theorem DetHeadStep_discrete.case_inl {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep_discrete ⟨.case (.inl v) el er, σ⟩ ⟨el.app v, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' hv])

@[discrete]
theorem DetHeadStep_discrete.case_inr {v el er : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep_discrete ⟨.case (.inr v) el er, σ⟩ ⟨er.app v, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.isValM_some' hv])

@[discrete]
theorem DetHeadStep_discrete.alloc {v : Exp rT} (hv : IsVal v) (σ : State rT) :
    DetHeadStep_discrete ⟨.alloc v, σ⟩ ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv⟩)⟩ := by
  obtain ⟨w, hw⟩ := hv.check?_some
  exact .of_det_discrete _ _ (by simp [headStep, Exp.asValM, Exp.toVal?, hw, IsVal.subsingleton hv w])

@[discrete]
theorem DetHeadStep_discrete.load {ℓ : Loc} {v : Val rT} (σ : State rT) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep_discrete ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨.ofVal v, σ⟩ :=
  .of_det_discrete _ _ (by simp [headStep, hlookup])

@[discrete]
theorem DetHeadStep_discrete.store {ℓ : Loc} {e : Exp rT} {v_old v_new : Val rT}
    (_hv : IsVal e) (σ : State rT)
    (hlookup : σ.heap[ℓ]? = some v_old)
    (hnew : e.toVal? = some v_new) :
    DetHeadStep_discrete ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ.update_heap (·.insert ℓ v_new)⟩ :=
  .of_det_discrete _ _ (by simp [headStep, Exp.asValM, hnew, hlookup])

@[discrete]
theorem DetStep_discrete.fill [Countable rT] [MeasurableSingletonClass rT]
    (K : Ectx rT) {cfg1 cfg2 : Cfg rT} (h : DetStep_discrete cfg1 cfg2) :
    DetStep_discrete ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := h.safe.fill K
  det := by rw [← primStep_fill_singleton (Discrete.val_stuck h.pos_discrete)]; exact h.det

@[discrete]
theorem DetExec_discrete.refl (cfg : Cfg rT) : DetExec_discrete 0 cfg cfg where
  det_exec := rfl

@[discrete]
theorem DetExec_discrete.cons {cfg1 cfg2 cfg3 : Cfg rT} {n : ℕ}
    (hstep : DetStep_discrete cfg1 cfg2) (hrest : DetExec_discrete n cfg2 cfg3) :
    DetExec_discrete (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

end ProbLang
end
