import Metrology.ProbLang.CtxStep
import Mathlib.Order.Defs.PartialOrder

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

namespace ProbLang

def nsteps (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

structure PureStep (e1 e2 : Exp) : Prop where
  safe : ∀ σ, Reducible e1 σ
  det  : ∀ σ, primStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

class PureExec (φ : Prop) (n : ℕ) (e1 e2 : Exp) : Prop where
  pure_exec : φ → nsteps PureStep n e1 e2

structure PureHeadStep (e1 e2 : Exp) : Prop where
  safe : ∀ σ, ∃ ρ : Cfg, headStep ⟨e1, σ⟩ {ρ} > 0
  det  : ∀ σ, headStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

theorem PureHeadStep.toPureStep {e1 e2 : Exp} (h : PureHeadStep e1 e2) : PureStep e1 e2 :=
  ⟨fun σ => Reducible.of_head (h.safe σ), fun σ => primStep_eq_headStep (h.safe σ) ▸ h.det σ⟩

theorem PureStep.fill (K : Ectx) {e1 e2 : Exp} (h : PureStep e1 e2) :
    PureStep (K.fill e1) (K.fill e2) := by
  constructor
  · intro σ
    obtain ⟨⟨e2', σ2⟩, hρ⟩ := h.safe σ
    exact ⟨⟨K.fill e2', σ2⟩, primStep_fill_pos hρ⟩
  · intro σ
    rw [← primStep_fill_singleton (val_stuck (h.safe σ).choose_spec)]
    exact h.det σ

theorem PureStep.fill_nsteps (K : Ectx) {n : ℕ} {e1 e2 : Exp}
    (h : nsteps PureStep n e1 e2) :
    nsteps PureStep n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => simp [nsteps] at h; subst h; simp [nsteps]
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

theorem PureExec.fill (K : Ectx) {φ : Prop} {n : ℕ} {e1 e2 : Exp}
    [h : PureExec φ n e1 e2] : PureExec φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := PureStep.fill_nsteps K (h.pure_exec hφ)

theorem PureExec.reducible {σ : State} {φ : Prop} {n : ℕ} {e1 e2 : Exp}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    Reducible e1 σ := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact hstep.safe σ

theorem PureExec.not_val {φ : Prop} {n : ℕ} {e1 e2 : Exp}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    ¬e1.isValue := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  obtain ⟨ρ, hρ⟩ := hstep.safe default
  exact val_stuck hρ

theorem rtc_pure_step_val {n : ℕ} {v : Val} {e : Exp}
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

theorem as_val_isSome {e : Exp} (h : ∃ v : Val, v.1 = e) : e.isValue := by
  obtain ⟨⟨_, hv⟩, rfl⟩ := h
  exact hv.toIsValue


/-- Build a `PureHeadStep e1 e2` from a proof that `headStep` always maps
    `⟨e1, σ⟩` to `dirac ⟨e2, σ⟩`. The `safe` field is derived automatically. -/
theorem PureHeadStep.of_det (e1 e2 : Exp)
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
structure DetHeadStep (cfg1 cfg2 : Cfg) : Prop where
  safe : ∃ ρ : Cfg, 0 < headStep cfg1 {ρ}
  det  : headStep cfg1 {cfg2} = 1

theorem DetHeadStep.pos (h : DetHeadStep cfg1 cfg2) : 0 < headStep cfg1 {cfg2} :=
  h.det ▸ one_pos

theorem DetHeadStep.of_det (cfg1 cfg2 : Cfg)
    (hdet : headStep cfg1 {cfg2} = 1) : DetHeadStep cfg1 cfg2 :=
  ⟨⟨cfg2, hdet ▸ one_pos⟩, hdet⟩

structure DetStep (cfg1 cfg2 : Cfg) : Prop where
  safe : Reducible cfg1.expr cfg1.state
  det  : primStep cfg1 {cfg2} = 1

theorem DetStep.pos (h : DetStep cfg1 cfg2) : 0 < primStep cfg1 {cfg2} :=
  h.det ▸ one_pos

theorem DetHeadStep.toDetStep {cfg1 cfg2 : Cfg} (h : DetHeadStep cfg1 cfg2) : DetStep cfg1 cfg2 where
  safe := ⟨_, primStep_pos_of_headStep h.pos⟩
  det := by obtain ⟨e1, σ1⟩ := cfg1; rw [primStep_eq_headStep h.safe]; exact h.det

class DetExec (n : ℕ) (cfg1 cfg2 : Cfg) : Prop where
  det_exec : nsteps DetStep n cfg1 cfg2

theorem DetExec.succ {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

theorem DetHeadStep.fst_pair {e1 e2 : Exp} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State) :
    DetHeadStep ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

theorem DetHeadStep.snd_pair {e1 e2 : Exp} (h1 : IsVal e1) (h2 : IsVal e2) (σ : State) :
    DetHeadStep ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' h1, Exp.isValM_some' h2])

theorem DetHeadStep.cond_true (et ef : Exp) (σ : State) :
    DetHeadStep ⟨.cond (.lit (.bool true)) et ef, σ⟩ ⟨et, σ⟩ :=
  .of_det _ _ (by simp [headStep])

theorem DetHeadStep.cond_false (et ef : Exp) (σ : State) :
    DetHeadStep ⟨.cond (.lit (.bool false)) et ef, σ⟩ ⟨ef, σ⟩ :=
  .of_det _ _ (by simp [headStep])

theorem DetHeadStep.app_letrec {f x : Binder} {body v : Exp}
    (hv : IsVal v) (σ : State) :
    DetHeadStep ⟨.app (.letrec f x body) v, σ⟩ ⟨Exp.subst x v (Exp.subst f (.letrec f x body) body), σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.unop {op : UnOp} {e result : Exp}
    (hv : IsVal e)
    (heval : UnOp.eval op e = some result) (σ : State) :
    DetHeadStep ⟨.unop op e, σ⟩ ⟨result, σ⟩ :=
  .of_det _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' hv, heval])

theorem DetHeadStep.binop {op : BinOp} {e1 e2 result : Exp}
    (h1 : IsVal e1) (h2 : IsVal e2)
    (heval : BinOp.eval op e1 e2 = some result) (σ : State) :
    DetHeadStep ⟨.binop op e1 e2, σ⟩ ⟨result, σ⟩ :=
  .of_det _ _ (by simp [headStep, Option.unwrapM, Exp.isValM_some' h1, Exp.isValM_some' h2, heval])

theorem DetHeadStep.case_inl {v el er : Exp} (hv : IsVal v) (σ : State) :
    DetHeadStep ⟨.case (.inl v) el er, σ⟩ ⟨el.app v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.case_inr {v el er : Exp} (hv : IsVal v) (σ : State) :
    DetHeadStep ⟨.case (.inr v) el er, σ⟩ ⟨er.app v, σ⟩ :=
  .of_det _ _ (by simp [headStep, Exp.isValM_some' hv])

theorem DetHeadStep.alloc {v : Exp} (hv : IsVal v) (σ : State) :
    DetHeadStep ⟨.alloc v, σ⟩ ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv⟩)⟩ := by
  obtain ⟨w, hw⟩ := hv.check?_some
  exact .of_det _ _ (by simp [headStep, Exp.asValM, Exp.toVal?, hw, IsVal.subsingleton hv w])

theorem DetHeadStep.load {ℓ : Loc} {v : Val} (σ : State) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨.ofVal v, σ⟩ :=
  .of_det _ _ (by simp [headStep, hlookup])

theorem DetHeadStep.store {ℓ : Loc} {e : Exp} {v_old v_new : Val}
    (_hv : IsVal e) (σ : State)
    (hlookup : σ.heap[ℓ]? = some v_old)
    (hnew : e.toVal? = some v_new) :
    DetHeadStep ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ.update_heap (·.insert ℓ v_new)⟩ :=
  .of_det _ _ (by simp [headStep, Exp.asValM, hnew, hlookup])

theorem DetStep.fill (K : Ectx) {cfg1 cfg2 : Cfg} (h : DetStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := h.safe.fill K
  det := by rw [← primStep_fill_singleton (val_stuck h.pos)]; exact h.det

theorem DetExec.refl (cfg : Cfg) : DetExec 0 cfg cfg where
  det_exec := rfl

theorem DetExec.cons {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) (hrest : DetExec n cfg2 cfg3) :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

end ProbLang
end
