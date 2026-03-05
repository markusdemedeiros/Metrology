import Metrology.ProbLang.PureStep

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

/-- Build a `PureHeadStep e1 e2` from a proof that `HeadStep` always maps
    `⟨e1, σ⟩` to `dirac ⟨e2, σ⟩`. The `safe` field is derived automatically. -/
theorem PureHeadStep.of_det (e1 e2 : Exp)
    (hdet : ∀ σ, HeadStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1) :
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
  safe : ∃ ρ : Cfg, 0 < HeadStep cfg1 {ρ}
  det  : HeadStep cfg1 {cfg2} = 1

structure DetStep (cfg1 cfg2 : Cfg) : Prop where
  safe : ∃ ρ : Cfg, 0 < PrimStep cfg1 {ρ}
  det  : PrimStep cfg1 {cfg2} = 1

theorem DetHeadStep.toDetStep {cfg1 cfg2 : Cfg} (h : DetHeadStep cfg1 cfg2) : DetStep cfg1 cfg2 := by
  constructor
  · obtain ⟨ρ, hρ⟩ := h.safe
    exact ⟨ρ, head_prim_step hρ⟩
  · obtain ⟨e1, σ1⟩ := cfg1
    rw [head_prim_step_eq h.safe]
    exact h.det

class DetExec (n : ℕ) (cfg1 cfg2 : Cfg) : Prop where
  det_exec : nsteps DetStep n cfg1 cfg2

theorem DetExec.succ {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

theorem DetHeadStep.fst_pair {e1 e2 : Exp} (h1 : e1.isValueB = true) (h2 : e2.isValueB = true) (σ : State) :
    DetHeadStep ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ := by
  have hv1 := e1.isValueB_iff.mp h1
  have hv2 := e2.isValueB_iff.mp h2
  exact ⟨⟨⟨e1, σ⟩, by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩,
         by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩

theorem DetHeadStep.snd_pair {e1 e2 : Exp} (h1 : e1.isValueB = true) (h2 : e2.isValueB = true) (σ : State) :
    DetHeadStep ⟨.snd (.pair e1 e2), σ⟩ ⟨e2, σ⟩ := by
  have hv1 := e1.isValueB_iff.mp h1
  have hv2 := e2.isValueB_iff.mp h2
  exact ⟨⟨⟨e2, σ⟩, by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩,
         by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩

theorem DetHeadStep.cond_true (et ef : Exp) (σ : State) :
    DetHeadStep ⟨.cond (.lit (.bool true)) et ef, σ⟩ ⟨et, σ⟩ :=
  ⟨⟨⟨et, σ⟩, by simp [HeadStep]⟩, by simp [HeadStep]⟩

theorem DetHeadStep.cond_false (et ef : Exp) (σ : State) :
    DetHeadStep ⟨.cond (.lit (.bool false)) et ef, σ⟩ ⟨ef, σ⟩ :=
  ⟨⟨⟨ef, σ⟩, by simp [HeadStep]⟩, by simp [HeadStep]⟩

theorem DetHeadStep.app_letrec {f x : Binder} {body v : Exp}
    (hv : v.isValueB = true) (σ : State) :
    DetHeadStep ⟨.app (.letrec f x body) v, σ⟩ ⟨body.subst f (.letrec f x body) |>.subst x v, σ⟩ := by
  have hv' := v.isValueB_iff.mp hv
  exact ⟨⟨⟨body.subst f (.letrec f x body) |>.subst x v, σ⟩,
          by simp [HeadStep, Exp.isValM_some hv']⟩,
         by simp [HeadStep, Exp.isValM_some hv']⟩

theorem DetHeadStep.unop {op : UnOp} {e result : Exp}
    (hv : e.isValueB = true)
    (heval : UnOp.eval op e = some result) (σ : State) :
    DetHeadStep ⟨.unop op e, σ⟩ ⟨result, σ⟩ := by
  have hv' := e.isValueB_iff.mp hv
  exact ⟨⟨⟨result, σ⟩, by simp [HeadStep, Option.unwrapM, Exp.isValM_some hv', heval]⟩,
         by simp [HeadStep, Option.unwrapM, Exp.isValM_some hv', heval]⟩

theorem DetHeadStep.binop {op : BinOp} {e1 e2 result : Exp}
    (h1 : e1.isValueB = true) (h2 : e2.isValueB = true)
    (heval : BinOp.eval op e1 e2 = some result) (σ : State) :
    DetHeadStep ⟨.binop op e1 e2, σ⟩ ⟨result, σ⟩ := by
  have hv1 := e1.isValueB_iff.mp h1
  have hv2 := e2.isValueB_iff.mp h2
  exact ⟨⟨⟨result, σ⟩, by simp [HeadStep, Option.unwrapM, Exp.isValM_some hv1, Exp.isValM_some hv2, heval]⟩,
         by simp [HeadStep, Option.unwrapM, Exp.isValM_some hv1, Exp.isValM_some hv2, heval]⟩

theorem DetHeadStep.case_inl {v el er : Exp} (hv : v.isValueB = true) (σ : State) :
    DetHeadStep ⟨.case (.inl v) el er, σ⟩ ⟨el.app v, σ⟩ := by
  have hv' := v.isValueB_iff.mp hv
  exact ⟨⟨⟨el.app v, σ⟩, by simp [HeadStep, Exp.isValM_some hv']⟩,
         by simp [HeadStep, Exp.isValM_some hv']⟩

theorem DetHeadStep.case_inr {v el er : Exp} (hv : v.isValueB = true) (σ : State) :
    DetHeadStep ⟨.case (.inr v) el er, σ⟩ ⟨er.app v, σ⟩ := by
  have hv' := v.isValueB_iff.mp hv
  exact ⟨⟨⟨er.app v, σ⟩, by simp [HeadStep, Exp.isValM_some hv']⟩,
         by simp [HeadStep, Exp.isValM_some hv']⟩

theorem DetHeadStep.alloc {v : Exp} (hv : v.isValueB = true) (σ : State) :
    DetHeadStep ⟨.alloc v, σ⟩ ⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, v.isValueB_iff.mp hv⟩)⟩ := by
  have hv' := v.isValueB_iff.mp hv
  have hdet : HeadStep ⟨.alloc v, σ⟩ {⟨.lit (.loc σ.heap.fresh), σ.update_heap (·.insert σ.heap.fresh ⟨v, hv'⟩)⟩} = 1 := by
    simp [HeadStep, Exp.asValM, Exp.toVal?, hv']
  exact ⟨⟨_, by rw [hdet]; norm_num⟩, hdet⟩

theorem DetHeadStep.load {ℓ : Loc} {v : Val} (σ : State) (hlookup : σ.heap[ℓ]? = some v) :
    DetHeadStep ⟨.load (.lit (.loc ℓ)), σ⟩ ⟨.ofVal v, σ⟩ := by
  have hdet : HeadStep ⟨.load (.lit (.loc ℓ)), σ⟩ {⟨.ofVal v, σ⟩} = 1 := by
    simp [HeadStep, hlookup]
  exact ⟨⟨_, by rw [hdet]; norm_num⟩, hdet⟩

theorem DetHeadStep.store {ℓ : Loc} {e : Exp} {v_old v_new : Val}
    (hv : e.isValueB = true) (σ : State)
    (hlookup : σ.heap[ℓ]? = some v_old)
    (hnew : e.toValB? = some v_new) :
    DetHeadStep ⟨.store (.lit (.loc ℓ)) e, σ⟩ ⟨.lit .unit, σ.update_heap (·.insert ℓ v_new)⟩ := by
  have hv' := e.isValueB_iff.mp hv
  have htoVal : e.toVal? = some v_new := by rwa [← Exp.toValB?_eq_toVal?]
  have hdet : HeadStep ⟨.store (.lit (.loc ℓ)) e, σ⟩
      {⟨.lit .unit, σ.update_heap (·.insert ℓ v_new)⟩} = 1 := by
    simp [HeadStep, Exp.asValM, htoVal, hlookup]
  exact ⟨⟨_, by rw [hdet]; norm_num⟩, hdet⟩

theorem DetExec.refl (cfg : Cfg) : DetExec 0 cfg cfg where
  det_exec := rfl

theorem DetExec.cons {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) (hrest : DetExec n cfg2 cfg3) :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩
