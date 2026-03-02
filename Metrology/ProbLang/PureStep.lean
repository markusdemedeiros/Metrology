import Metrology.ProbLang.PrimStep
import Mathlib.Order.Defs.PartialOrder

def nsteps (r : α → α → Prop) : ℕ → α → α → Prop
  | 0,   a, b => a = b
  | n+1, a, b => ∃ c, r a c ∧ nsteps r n c b

noncomputable section PureStep
open Classical MeasureTheory ProbabilityTheory Measure

local instance : MeasurableSpace Expr := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

-- Record pure_step (e1 e2 : expr Λ) := {
--   pure_step_safe σ1 : reducible (e1, σ1);
--   pure_step_det σ : prim_step e1 σ (e2, σ) = 1;
-- }.
structure PureStep (e1 e2 : Expr) : Prop where
  safe : ∀ σ, ∃ ρ : Cfg, PrimStep ⟨e1, σ⟩ {ρ} > 0
  det  : ∀ σ, PrimStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

-- Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
--   pure_exec : φ → relations.nsteps pure_step n e1 e2.
class PureExec (φ : Prop) (n : ℕ) (e1 e2 : Expr) : Prop where
  pure_exec : φ → nsteps PureStep n e1 e2

-- Record pure_head_step (e1 e2 : expr Λ) := {
--   pure_head_step_safe σ1 : head_reducible e1 σ1;
--   pure_head_step_det σ1 : head_step e1 σ1 (e2, σ1) = 1;
-- }.
structure PureHeadStep (e1 e2 : Expr) : Prop where
  safe : ∀ σ, ∃ ρ : Cfg, HeadStep ⟨e1, σ⟩ {ρ} > 0
  det  : ∀ σ, HeadStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1

-- Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
-- Proof.
--   intros [Hp1 Hp2]. split.
--   - intros σ. destruct (Hp1 σ) as ([e2' σ2] & ?).
--     eexists (e2', σ2). by apply head_prim_step.
--   - intros σ1. rewrite /= head_prim_step_eq //.
-- Qed.
theorem PureHeadStep.toPureStep {e1 e2 : Expr} (h : PureHeadStep e1 e2) : PureStep e1 e2 := by
  sorry

-- Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
--   pure_step e1 e2 → pure_step (K e1) (K e2).
-- Proof.
--   intros [Hred Hstep]. split.
--   - unfold reducible in *. intros σ1.
--     destruct (Hred σ1) as [[]].
--     eexists. by eapply fill_step.
--   - intros σ.
--     rewrite -fill_step_prob //.
--     eapply (to_final_None_1 (_, σ)).
--     by eapply reducible_not_final.
-- Qed.
theorem PureStep.fill (K : Ectx) {e1 e2 : Expr} (h : PureStep e1 e2) :
    PureStep (K.fill e1) (K.fill e2) := by
  sorry

-- Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
--   relations.nsteps pure_step n e1 e2 →
--   relations.nsteps pure_step n (K e1) (K e2).
-- Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.
theorem PureStep.fill_nsteps (K : Ectx) {n : ℕ} {e1 e2 : Expr}
    (h : nsteps PureStep n e1 e2) :
    nsteps PureStep n (K.fill e1) (K.fill e2) := by
  induction n generalizing e1 e2 with
  | zero => simp [nsteps] at h; subst h; simp [nsteps]
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := h
    exact ⟨K.fill c, hstep.fill K, ih hrest⟩

-- Lemma pure_exec_fill K φ n e1 e2 :
--   PureExec φ n e1 e2 →
--   PureExec φ n (fill K e1) (fill K e2).
-- Proof. apply: pure_exec_ctx. Qed.
-- Lemma pure_exec_fill K φ n e1 e2 :
--   PureExec φ n e1 e2 →
--   PureExec φ n (fill K e1) (fill K e2).
-- Proof. apply: pure_exec_ctx. Qed.
theorem PureExec.fill (K : Ectx) {φ : Prop} {n : ℕ} {e1 e2 : Expr}
    [h : PureExec φ n e1 e2] : PureExec φ n (K.fill e1) (K.fill e2) where
  pure_exec hφ := PureStep.fill_nsteps K (h.pure_exec hφ)

-- Lemma PureExec_reducible σ1 φ n e1 e2 :
--   φ → PureExec φ (S n) e1 e2 → reducible (e1, σ1).
-- Proof. move => Hφ /(_ Hφ). inversion_clear 1. apply H. Qed.
theorem PureExec.reducible {σ : State} {φ : Prop} {n : ℕ} {e1 e2 : Expr}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    ∃ ρ : Cfg, PrimStep ⟨e1, σ⟩ {ρ} > 0 := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  exact hstep.safe σ

-- Lemma PureExec_not_val `{Inhabited (language.state Λ)} φ n e1 e2 :
--   φ → PureExec φ (S n) e1 e2 → to_val e1 = None.
-- Proof.
--   intros Hφ Hex.
--   destruct (PureExec_reducible inhabitant _ _ _ _ Hφ Hex) => /=.
--   simpl in *.
--   by eapply val_stuck.
-- Qed.
theorem PureExec.not_val {φ : Prop} {n : ℕ} {e1 e2 : Expr}
    (hφ : φ) [h : PureExec φ (n + 1) e1 e2] :
    e1.toVal? = none := by
  obtain ⟨_, hstep, _⟩ := h.pure_exec hφ
  obtain ⟨ρ, hρ⟩ := hstep.safe default
  exact val_stuck hρ

-- Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
--   rtc pure_step (of_val v) e → to_val e = Some v.
-- Proof.
--   intros ?; rewrite <- to_of_val.
--   f_equal; symmetry; eapply rtc_nf; first done.
--   intros [e' [Hstep _]].
--   specialize (Hstep inhabitant) as [? Hval%val_stuck].
--   by rewrite to_of_val in Hval.
-- Qed.
theorem rtc_pure_step_val {n : ℕ} {v : Val} {e : Expr}
    (h : nsteps PureStep n v.1 e) :
    e.toVal? = some v := by
  sorry

--   (* This is a family of frequent assumptions for PureExec *)
--   Class IntoVal (e : expr Λ) (v : val Λ) :=
--     into_val : of_val v = e.
class IntoVal (e : Expr) (v : Val) : Prop where
  into_val : v.1 = e

--   Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e.
class AsVal (e : Expr) : Prop where
  as_val : ∃ v : Val, v.1 = e

--   Lemma as_val_is_Some e :
--     (∃ v, of_val v = e) → is_Some (to_val e).
--   Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.
theorem as_val_is_Some {e : Expr} (h : ∃ v : Val, v.1 = e) : e.isValue := by
  obtain ⟨⟨_, hv⟩, rfl⟩ := h
  exact hv

--   Lemma fill_is_val e K `{@LanguageCtx Λ K} :
--     is_Some (to_val (K e)) → is_Some (to_val e).
--   Proof. rewrite -!not_eq_None_Some. eauto using fill_not_val. Qed.
theorem fill_is_val {K : Ectx} {e : Expr} (h : (K.fill e).isValue) : e.isValue :=
  Ectx.fill_isValue h

end PureStep
