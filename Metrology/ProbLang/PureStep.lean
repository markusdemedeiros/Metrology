import Metrology.ProbLang.PrimReduct
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

end ProbLang
end
