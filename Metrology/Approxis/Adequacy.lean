module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Erasure

@[expose] public section

/-! # Adequacy: WP entailments imply `AddCoupl` between execution distributions. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
  ProbLang.ApproxisWpGS ProbLang.Cfg
open scoped AppGS

namespace ProbLang.AdequacyHelpers

section FupdPlainForall

variable {GF : BundledGFunctors} [InvGS_gen false GF]

open Iris Iris.BI Iris.BI.BIBase Iris.ProofMode

theorem stepFupdN_mono' {E E' : CoPset} {n : Nat} {P Q : IProp GF}
    (HPQ : P ⊢@{IProp GF} Q) :
    iprop(|={E}[E']▷=>^[n] P) ⊢@{IProp GF} iprop(|={E}[E']▷=>^[n] Q) := by
  induction n with
  | zero => simp only [Nat.repeat]; exact HPQ
  | succ n ih =>
    simp only [Nat.repeat]
    exact BIFUpdate.mono (later_mono (BIFUpdate.mono ih))

theorem stepFupdN_intro' (E : CoPset) (n : Nat) {P : IProp GF} :
    P ⊢@{IProp GF} iprop(|={E}[E]▷=>^[n] P) := by
  induction n with
  | zero => simp only [Nat.repeat]; exact Entails.rfl
  | succ n ih =>
    simp only [Nat.repeat]
    refine Entails.trans ih ?_
    refine Entails.trans (fupd_intro (E := E)) ?_
    refine BIFUpdate.mono ?_
    refine Entails.trans later_intro ?_
    exact later_mono (fupd_intro (E := E))

theorem fupd_laterN_to_stepFupdN (E : CoPset) (n : Nat) (Q : IProp GF) :
    iprop(|={E}=> ▷^[n+1] Q) ⊢@{IProp GF} iprop(|={E}[E]▷=>^[n+1] Q) := by
  induction n with
  | zero =>
    simp only [Nat.repeat]
    refine BIFUpdate.mono ?_
    refine later_mono ?_
    exact fupd_intro (E := E)
  | succ n ih =>
    simp only [Nat.repeat] at ih ⊢
    refine BIFUpdate.mono ?_
    refine later_mono ?_
    refine Entails.trans (fupd_intro (E := E)) ?_
    refine Entails.trans ih ?_
    exact fupd_intro (E := E)

theorem fupd_plainly_forall_2 (E : CoPset) {A : Type _} (Φ : A → IProp GF) :
    iprop((∀ x, |={E}=> ■ Φ x) ⊢ |={E}=> ∀ x, Φ x) := by
  have step1 : iprop((∀ x, |={E}=> ■ Φ x) ⊢ |={E}=> (∀ x, ■ Φ x)) := by
    simp only [fupd, uPred_fupd, le_upd_if, Bool.false_eq_true, ↓reduceIte]
    iintro H ⟨Hwsat, HE⟩
    ihave #HP : ◇ (∀ x, ■ Φ x) $$ [H Hwsat HE]
    · iintro %x
      ihave H' := H $$ %x
      imod H' $$ [Hwsat HE] with ⟨_, _, H'⟩
      · isplitl [Hwsat] <;> iassumption
      iexact H'
    imodintro; imod HP; imodintro
    isplitl [Hwsat]; iassumption
    isplitl [HE]; iassumption
    iclear H
    iexact HP
  refine step1.trans (BIFUpdate.mono ?_)
  exact forall_mono (fun _ => plainly_elim)

theorem fupd_plain_forall_2 (E : CoPset) {A : Type _} (Φ : A → IProp GF)
    [∀ x, Plain (Φ x)] :
    iprop((∀ x, |={E}=> Φ x) ⊢ |={E}=> ∀ x, Φ x) := by
  refine Entails.trans ?_ (fupd_plainly_forall_2 E Φ)
  refine forall_mono (fun x => ?_)
  exact BIFUpdate.mono Plain.plain

theorem fupd_plain_forall' (E : CoPset) {A : Type _} (Φ : A → IProp GF)
    [∀ x, Plain (Φ x)] :
    iprop(|={E}=> ∀ x, Φ x) ⊣⊢@{IProp GF} iprop(∀ x, |={E}=> Φ x) :=
  ⟨fupd_forall, fupd_plain_forall_2 E Φ⟩

theorem fupd_except_0 (E1 E2 : CoPset) (P : IProp GF) :
    iprop(|={E1,E2}=> ◇ P) ⊢@{IProp GF} iprop(|={E1,E2}=> P) := by
  refine Entails.trans
    (BIFUpdate.mono (except0_mono (fupd_intro (E := E2) (P := P)))) ?_
  exact (BIFUpdate.mono BIFUpdate.except0).trans BIFUpdate.trans

theorem step_fupd_except_0 (E1 E2 : CoPset) (P : IProp GF) :
    iprop(|={E1}[E2]▷=> ◇ P) ⊢@{IProp GF} iprop(|={E1}[E2]▷=> P) :=
  BIFUpdate.mono (later_mono (fupd_except_0 E2 E1 P))

theorem step_fupdN_except_0 (E1 E2 : CoPset) (P : IProp GF) (n : Nat) :
    iprop(|={E1}[E2]▷=>^[n+1] ◇ P) ⊢@{IProp GF} iprop(|={E1}[E2]▷=>^[n+1] P) := by
  induction n with
  | zero =>
    simp only [Nat.repeat]
    exact step_fupd_except_0 E1 E2 P
  | succ n ih =>
    simp only [Nat.repeat] at ih ⊢
    refine BIFUpdate.mono (later_mono (BIFUpdate.mono ih))

theorem step_fupdN_plain_forall (E : CoPset) {A : Type _} (Φ : A → IProp GF)
    [∀ x, Plain (Φ x)] (n : Nat) :
    iprop(|={E}▷=>^[n] ∀ x, Φ x) ⊣⊢@{IProp GF} iprop(∀ x, |={E}▷=>^[n] Φ x) := by
  refine ⟨?_, ?_⟩
  · refine forall_intro (fun x => ?_)
    exact stepFupdN_mono' (forall_elim x)
  cases n with
  | zero => simp only [Nat.repeat]; exact forall_intro (forall_elim ·)
  | succ n =>
    have h1 : iprop(∀ x, |={E}▷=>^[n+1] Φ x) ⊢@{IProp GF}
              iprop(∀ x, |={E}=> ▷^[n+1] ◇ Φ x) :=
      forall_mono (fun _ => step_fupdN_plain)
    refine h1.trans ?_
    have h2 : iprop(∀ x, |={E}=> ▷^[n+1] ◇ Φ x) ⊢@{IProp GF}
              iprop(|={E}=> ∀ x, ▷^[n+1] ◇ Φ x) :=
      (fupd_plain_forall' E (fun x => iprop(▷^[n+1] ◇ Φ x))).mpr
    refine h2.trans ?_
    have h3 : iprop(∀ x, ▷^[n+1] ◇ Φ x) ⊢@{IProp GF}
              iprop(▷^[n+1] ◇ (∀ x, Φ x)) :=
      (laterN_forall (n+1)).mpr.trans (laterN_mono (n+1) except0_forall.mpr)
    refine (BIFUpdate.mono h3).trans ?_
    refine (fupd_laterN_to_stepFupdN (GF := GF) E n _).trans ?_
    exact step_fupdN_except_0 E E (iprop(∀ x, Φ x)) n

theorem stepFupdN_zero {E E' : CoPset} (P : IProp GF) :
    iprop(|={E}[E']▷=>^[0] P) ⊣⊢@{IProp GF} P := ⟨Entails.rfl, Entails.rfl⟩

theorem fupd_pure_wand_intro (p : Prop) (P : IProp GF) :
    iprop(⌜p⌝ -∗ |={∅}=> P) ⊢@{IProp GF} iprop(|={∅}=> (⌜p⌝ -∗ P)) := by
  iintro HwP
  by_cases hp : p
  · ihave HfP := HwP $$ %hp
    imod HfP
    imodintro
    iintro _
    iexact HfP
  · imodintro
    iintro %HS
    exact absurd HS hp

theorem fupd_stepFupdN_plain_forall_1
    {A : Type _} (Φ : A → IProp GF)
    [instP : ∀ x, Plain (Φ x)] (n : Nat) :
    iprop(∀ (x : A), |={∅}=> |={∅}[∅]▷=>^[n] Φ x) ⊢@{IProp GF}
      iprop(|={∅}=> |={∅}[∅]▷=>^[n] ∀ (x : A), Φ x) := by
  cases n with
  | zero =>
    simp only [Nat.repeat]
    exact (fupd_plain_forall' (GF := GF) ∅ Φ).mpr
  | succ n =>
    have step1 : ∀ x : A,
        (iprop(|={∅}=> |={∅}[∅]▷=>^[n+1] Φ x) : IProp GF) ⊢@{IProp GF}
          (iprop(|={∅}=> ▷^[n+1] ◇ Φ x) : IProp GF) := fun _ =>
      (BIFUpdate.mono step_fupdN_plain).trans BIFUpdate.trans
    refine (forall_mono (fun x => step1 x)).trans ?_
    refine (fupd_plain_forall' (GF := GF) ∅ (fun x => iprop(▷^[n+1] ◇ Φ x))).mpr.trans ?_
    refine BIFUpdate.mono ?_
    refine (laterN_forall (n+1)).mpr.trans ?_
    refine (laterN_mono (n+1) except0_forall.mpr).trans ?_
    refine (fupd_intro (E := ∅)).trans ?_
    refine (fupd_laterN_to_stepFupdN (GF := GF) ∅ n
      (iprop(◇ ∀ x, Φ x))).trans ?_
    exact step_fupdN_except_0 ∅ ∅ (iprop(∀ x, Φ x)) n

theorem fupd_stepFupdN_plain_forall_3
    (Ψ : State → Exp → State → IProp GF)
    [instP : ∀ a b c, Plain (Ψ a b c)] (n : Nat) :
    iprop(∀ (a : State) (b : Exp) (c : State),
        |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c) ⊢@{IProp GF}
      iprop(|={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : State) (b : Exp) (c : State), Ψ a b c) := by
  refine (forall_mono (fun a => forall_mono (fun b =>
    fupd_stepFupdN_plain_forall_1 (GF := GF) (fun c => Ψ a b c) n))).trans ?_
  refine (forall_mono (fun a =>
    fupd_stepFupdN_plain_forall_1 (GF := GF)
      (fun b => iprop(∀ c, Ψ a b c)) n)).trans ?_
  exact fupd_stepFupdN_plain_forall_1 (GF := GF)
    (fun a => iprop(∀ b c, Ψ a b c)) n

theorem fupd_stepFupdN_plain_forall_4
    (Ψ : Exp → State → Exp → State → IProp GF)
    [∀ a b c d, Plain (Ψ a b c d)] (n : Nat) :
    iprop(∀ (a : Exp) (b : State) (c : Exp) (d : State),
        |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c d) ⊢@{IProp GF}
      iprop(|={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : Exp) (b : State) (c : Exp) (d : State), Ψ a b c d) := by
  refine (forall_mono (fun a => forall_mono (fun b => forall_mono (fun c =>
    fupd_stepFupdN_plain_forall_1 (GF := GF) (fun d => Ψ a b c d) n)))).trans ?_
  refine (forall_mono (fun a => forall_mono (fun b =>
    fupd_stepFupdN_plain_forall_1 (GF := GF)
      (fun c => iprop(∀ d, Ψ a b c d)) n))).trans ?_
  refine (forall_mono (fun a =>
    fupd_stepFupdN_plain_forall_1 (GF := GF)
      (fun b => iprop(∀ c d, Ψ a b c d)) n)).trans ?_
  exact fupd_stepFupdN_plain_forall_1 (GF := GF)
    (fun a => iprop(∀ b c d, Ψ a b c d)) n

theorem stepFupdN_pure_wand_intro (E : CoPset) (n : Nat) (p q : Prop) :
    iprop(⌜p⌝ -∗ |={E}[E]▷=>^[n] ⌜q⌝) ⊢@{IProp GF}
      iprop(|={E}[E]▷=>^[n] (⌜p⌝ -∗ ⌜q⌝)) := by
  by_cases hp : p
  · refine Entails.trans ?step (stepFupdN_mono' (GF := GF) (E := E) (E' := E) (n := n)
      (P := iprop(⌜q⌝ : IProp GF))
      (Q := iprop(⌜p⌝ -∗ ⌜q⌝ : IProp GF))
      (wand_intro sep_elim_l))
    refine (sep_emp (P := iprop(⌜p⌝ -∗ |={E}[E]▷=>^[n] ⌜q⌝))).mpr.trans ?_
    refine (sep_mono_r (pure_intro (P := emp) hp)).trans ?_
    exact wand_elim_l
  · refine Entails.trans ?_ (stepFupdN_intro' (GF := GF) E n)
    exact wand_intro (sep_elim_r.trans (pure_elim' (fun h => absurd h hp)))

end FupdPlainForall

end ProbLang.AdequacyHelpers

namespace ProbLang

open ProbLang.AdequacyHelpers

def adequacyRel (φ : Val → Val → Prop) : Set (Exp × Exp) :=
  fun p => ∃ (v v' : Val), p.1.toVal? = some v ∧ p.2.toVal? = some v' ∧ φ v v'

section Adequacy

variable {GF : BundledGFunctors} [IA : ApproxisGS false GF]

theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp) (σ₁ : State)
    (e₁' : Exp) (σ₁' : State)
    (Z : State → Cfg → ENNReal → IProp GF)
    (φ : Val → Val → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (σ₂ : State) (e₂' : Exp) (σ₂' : State) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            ((execN m ⟨e₁, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          ((execN m ⟨e₁, σ₁⟩).map (·.expr))
          ((limExec ⟨e₁', σ₁'⟩).map (·.expr))⌝) := by
  set Ψ : State → Cfg → ENNReal → IProp GF :=
    fun σ₀ ⟨e₀', σ₀'⟩ ε₀ =>
      iprop((∀ (σ₂ : State) (e₂' : Exp) (σ₂' : State) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            ((execN m ⟨e₁, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) -∗
        |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε₀ (adequacyRel φ)
            ((execN m ⟨e₁, σ₀⟩).map (·.expr))
            ((limExec ⟨e₀', σ₀'⟩).map (·.expr))⌝))
  iintro Hspec HZ
  iapply (specCoupl_ind (Ψ := Ψ) (Z := Z) (E := ∅)) $$ [] %σ₁ %e₁' %σ₁' %ε Hspec HZ
  iintro !> %σ₀ %c₀ %ε₀ H
  obtain ⟨e₀', σ₀'⟩ := c₀
  simp only [Ψ]
  iintro HZ
  icases H with ⟨%HVac | HZApp | HCpl⟩
  ·
    imodintro
    iapply ProbLang.ApproxisWpGS.stepFupdN_intro Std.LawfulSet.empty_subset n
    ipure_intro
    exact AddCoupl.trivial_of_one_le HVac (by
      rw [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
      simpa using execN_univ_le_one m ⟨e₁, σ₀⟩)
  ·
    iapply HZ
    iexact HZApp
  ·
    icases HCpl with ⟨%S, %k, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HAC, %HX₂bnd, %HεBnd, %Herase1, %Herase1', HCont⟩
    have Himpl : (∀ σ₂ e₂' σ₂', S σ₂ ⟨e₂', σ₂'⟩ →
      AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
        ((execN m ⟨e₁, σ₂⟩).map (·.expr))
        ((limExec ⟨e₂', σ₂'⟩).map (·.expr))) →
      AddCoupl ε₀ (adequacyRel φ)
        ((execN m ⟨e₁, σ₀⟩).map (·.expr))
        ((limExec ⟨e₀', σ₀'⟩).map (·.expr)) := fun Hpure =>
      AddCoupl_erasure_erasable_exp_rhs
        (e₁ := e₁) (e₁' := e₀') (σ₁ := σ₀) (σ₁' := σ₀') (m := k) (n := m)
        (ε₂ := ∫⁻ ρ, X₂ ρ ∂(μ₁'.bind (fun σ => pexecN k ⟨e₀', σ⟩)))
        (hE₂meas := Measurable.of_discrete)
        (hCoupl := HAC)
        (hBoundSum := _root_.le_refl _)
        (hEpsSum := HεBnd)
        (hErase₁ := ErasableExpr.of_erasable Herase1)
        (hErase₁' := ErasableExpr.of_erasable Herase1')
        (hCont := fun σ₂ ρ' hR => by
          obtain ⟨e₂', σ₂'⟩ := ρ'
          exact Hpure σ₂ e₂' σ₂' hR)
    iapply BIFUpdate.mono
    · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
        (P := iprop(⌜∀ σ₂ e₂' σ₂', S σ₂ ⟨e₂', σ₂'⟩ →
          AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            ((execN m ⟨e₁, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF)) ?_
      iintro %Hpure
      ipure_intro
      exact Himpl Hpure
    iapply BIFUpdate.mono
    · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
        (P := iprop(∀ (σ₂ : State) (e₂' : Exp) (σ₂' : State),
          ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            ((execN m ⟨e₁, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF)) ?_
      refine Entails.trans (forall_mono fun _ => forall_mono fun _ =>
        forall_mono fun _ => pure_wand.mp) ?_
      refine Entails.trans (forall_mono fun _ => forall_mono fun _ => pure_forall.mpr) ?_
      refine Entails.trans (forall_mono fun _ => pure_forall.mpr) ?_
      exact pure_forall.mpr
    iapply (fupd_stepFupdN_plain_forall_3 (GF := GF) (n := n)
      (Ψ := fun σ₂ e₂' σ₂' => iprop(
        ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
          ((execN m ⟨e₁, σ₂⟩).map (·.expr))
          ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF)))
    iintro %σ₂ %e₂' %σ₂'
    ispecialize HCont $$ %σ₂ %e₂' %σ₂'
    iapply BIFUpdate.mono
    · exact stepFupdN_pure_wand_intro (GF := GF) (E := ∅) (n := n)
        (p := S σ₂ ⟨e₂', σ₂'⟩)
        (q := AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
          ((execN m ⟨e₁, σ₂⟩).map (·.expr))
          ((limExec ⟨e₂', σ₂'⟩).map (·.expr)))
    iapply (fupd_pure_wand_intro (GF := GF) (S σ₂ ⟨e₂', σ₂'⟩)
      iprop(|={∅}[∅]▷=>^[n] ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
        ((execN m ⟨e₁, σ₂⟩).map (·.expr))
        ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF))
    iintro %HS
    ispecialize HCont $$ %HS
    ihave HCont' : iprop(|={∅}=> (((∀ (σ₂ : State) (e₂' : Exp) (σ₂' : State) (ε' : ENNReal),
            Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
              (⌜AddCoupl ε' (adequacyRel φ)
                ((execN m ⟨e₁, σ₂⟩).map (·.expr))
                ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) -∗
            |={∅}=> |={∅}[∅]▷=>^[n]
              (⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
                ((execN m ⟨e₁, σ₂⟩).map (·.expr))
                ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) ∧
        specCoupl ∅ σ₂ e₂' σ₂' (X₂ ⟨e₂', σ₂'⟩) Z)) $$ [HCont]
    · iexact HCont
    imod HCont' with HCont''
    ihave HΨ := and_elim_l (P := _) (Q := _) $$ HCont''
    iapply HΨ
    iexact HZ

theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp) (σ₁ : State)
    (e₁' : Exp) (σ₁' : State)
    (Z : Exp → State → Exp → State → ENNReal → IProp GF)
    (φ : Val → Val → Prop) (ε : ENNReal)
    (Hnone : e₁.toVal? = none) :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State) (ε' : ENNReal),
        Z e₂ σ₂ e₂' σ₂' ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            ((execN m ⟨e₂, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          ((execN (m + 1) ⟨e₁, σ₁⟩).map (·.expr))
          ((limExec ⟨e₁', σ₁'⟩).map (·.expr))⌝) := by
  have Hnv : ¬ e₁.isValue := Exp.toVal?_eq_none.mp Hnone
  rw [execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) Hnv m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %X₂, %_Hred, %_Hbnd, %Hexp, %Herase', Hcnt⟩
  iapply BIFUpdate.mono
  ·
    refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
      (P := iprop(⌜∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State),
          AddCoupl (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            ((execN m ⟨e₂, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF)) ?_
    iintro %Hpure
    ipure_intro
    exact AddCoupl_erasure_erasable_exp_lhs_kanto
      (e₁ := e₁) (e₁' := e₁') (σ₁ := σ₁) (σ₁' := σ₁') (n := m) (m := k)
      (μ₁' := μ₁') (E₂ := X₂) (ε := ε)
      (hErase₁' := ErasableExpr.of_erasable Herase')
      (hExp := Hexp)
      (hCont := fun ρ ρ' => by
        obtain ⟨e₂, σ₂⟩ := ρ
        obtain ⟨e₂', σ₂'⟩ := ρ'
        exact Hpure e₂ σ₂ e₂' σ₂')
  iapply BIFUpdate.mono
  · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
      (P := iprop(∀ (e₂ : Exp) (σ₂ : State) (e₂' : Exp) (σ₂' : State),
          ⌜AddCoupl (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            ((execN m ⟨e₂, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝ : IProp GF)) ?_
    refine Entails.trans (forall_mono fun _ => forall_mono fun _ =>
      forall_mono fun _ => pure_forall.mpr) ?_
    refine Entails.trans (forall_mono fun _ => forall_mono fun _ => pure_forall.mpr) ?_
    refine Entails.trans (forall_mono fun _ => pure_forall.mpr) ?_
    exact pure_forall.mpr
  iapply fupd_stepFupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  ispecialize Hcnt $$ %e₂ %σ₂ %e₂' %σ₂'
  imod Hcnt
  iapply Hcoupl
  iexact Hcnt

theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp) (σ₁ : State)
    (e₁' : Exp) (σ₁' : State)
    (Z : State → Cfg → ENNReal → IProp GF)
    (φ : Val → Val → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (σ₂ : State) (e₂' : Exp) (σ₂' : State) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=>
          (⌜AddCoupl ε' (adequacyRel φ)
            ((execN m ⟨e₁, σ₂⟩).map (·.expr))
            ((limExec ⟨e₂', σ₂'⟩).map (·.expr))⌝)) -∗
      |={∅}=>
        (⌜AddCoupl ε (adequacyRel φ)
          ((execN m ⟨e₁, σ₁⟩).map (·.expr))
          ((limExec ⟨e₁', σ₁'⟩).map (·.expr))⌝) :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ ε

theorem wpPre_value_Z_eq {v : Val} {Φ : Val → IProp GF} (E : CoPset) :
    (fun (σ₂ : State) (ρ' : Cfg) (ε₂ : ENNReal) =>
      iprop(|={∅, E}=> stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
        errInterp ε₂ ∗ Φ v))
    = (fun (σ₂ : State) (ρ' : Cfg) (ε₂ : ENNReal) =>
      match (Exp.ofVal v).toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
            errInterp ε₂ ∗ Φ v)
      | none => iprop(progCoupl (Exp.ofVal v) σ₂ ρ'.expr ρ'.state ε₂
          (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E}=>
                stateInterp σ₄ ∗ SpecUpdateGS.specInterp ρ'' ∗
                  errInterp ε₄ ∗ wp (GF := GF) E e₃ Φ)))))) := by
  funext σ₂ ρ' ε₂
  rw [Exp.toVal?_ofVal]

theorem wpPre_match_eq (motive : Option Val → Sort u)
    (x : Option Val) (some_f : (v : Val) → motive (some v))
    (none_f : Unit → motive none) :
    ProbLang.wpPre_value_Z_eq.match_1 motive x some_f none_f =
    ProbLang.ApproxisWpGS.wpPre.match_1 motive x some_f none_f := by
  cases x <;> rfl

theorem wp_value_specCoupl_unfold {e : Exp} {v : Val} {Φ : Val → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp (GF := GF) E e Φ ⊢@{IProp GF}
      ∀ (σ₁ : State) (e₁' : Exp) (σ₁' : State) (ε₁ : ENNReal),
        (stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗ errInterp ε₁) -∗
          |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
            iprop(|={∅, E}=>
              stateInterp σ₂ ∗ SpecUpdateGS.specInterp ρ' ∗
                errInterp ε₂ ∗ Φ v)) := by
  have he_eq : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  subst he_eq
  rw [wpPre_value_Z_eq (E := E) (v := v) (Φ := Φ)]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave Hwp' := (BI.equiv_iff.mp wp_unfold).1 $$ Hwp
  ispecialize Hwp' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; iassumption
    isplitl [Hs]; iassumption
    iassumption
  iexact Hwp'

theorem wp_adequacy_val_fupd (e e' : Exp) (σ σ' : State) (n : Nat)
    (φ : Val → Val → Prop) (v : Val) (ε : ENNReal) (He : e.toVal? = some v) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=>
        (⌜AddCoupl ε (adequacyRel φ)
          ((execN n ⟨e, σ⟩).map (·.expr))
          ((limExec ⟨e', σ'⟩).map (·.expr))⌝) := by
  have he_eq : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  subst he_eq
  iintro ⟨Hσ, Hs, Hε, Hwp⟩
  ihave HspecPre := wp_value_specCoupl_unfold (GF := GF) (Φ := _) ⊤ He $$ Hwp
  ispecialize HspecPre $$ %σ %e' %σ' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; iassumption
    isplitl [Hs]; iassumption
    iassumption
  imod HspecPre with HspecC
  iapply (wp_adequacy_spec_coupl_zero (m := n) (e₁ := Exp.ofVal v) (σ₁ := σ)
    (e₁' := e') (σ₁' := σ') (φ := φ) (ε := ε)) $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %ε' HZ
  imod HZ with ⟨_, Hs', _, Hφ⟩
  icases Hφ with ⟨%v', Hv', %Hφrel⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hs' Hv'
  subst Heq
  imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
  imodintro
  ipure_intro
  cases n with
  | zero =>
    simp only [execN, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n =>
    have hv_is_val : (Exp.ofVal v).isValue := v.isValue
    rw [execN_succ_isValue (ρ := ⟨Exp.ofVal v, σ₂⟩) hv_is_val n,
        limExec_of_isVal (e := Exp.ofVal v') (σ := σ₂') v'.2,
        MeasureTheory.Measure.map_dirac'
          (Measurable.of_discrete (f := (·.expr : Cfg → Exp))),
        MeasureTheory.Measure.map_dirac'
          (Measurable.of_discrete (f := (·.expr : Cfg → Exp)))]
    exact AddCoupl.dirac (a := Exp.ofVal v) (b := Exp.ofVal v')
      (ε := ε') (adequacyRel φ)
      ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', Hφrel⟩

theorem wp_adequacy_step_fupdN (ε : ENNReal) (e e' : Exp) (σ σ' : State)
    (n : Nat) (φ : Val → Val → Prop) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          ((execN n ⟨e, σ⟩).map (·.expr))
          ((limExec ⟨e', σ'⟩).map (·.expr))⌝) := by
  revert e σ e' σ' ε
  induction n with
  | zero =>
    intro ε e e' σ σ'
    iintro _
    imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
    imodintro
    simp only [Nat.repeat]
    ipure_intro
    simp only [execN_zero, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n ih =>
    intro ε e e' σ σ'
    iintro ⟨Hσ, Hs, Hε, Hwp⟩
    by_cases He : e.isValue
    ·
      obtain ⟨w⟩ : Nonempty (IsVal e) := He
      obtain ⟨w', hw'⟩ := w.check?_some
      let v : Val := ⟨e, w'⟩
      have Hv : e.toVal? = some v := by simp [Exp.toVal?, hw', v]
      ihave HvF := wp_adequacy_val_fupd (GF := GF) e e' σ σ' (n+1) φ v ε Hv $$
        [Hσ Hs Hε Hwp]
      · isplitl [Hσ] <;> try iassumption
        isplitl [Hs] <;> try iassumption
        isplitl [Hε] <;> iassumption
      imod HvF with %Hpure
      imodintro
      iapply ProbLang.ApproxisWpGS.stepFupdN_intro
        (E := ∅) (E' := ∅) Std.LawfulSet.subset_refl (n+1)
      ipure_intro
      exact Hpure
    ·
      have Hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      ihave Hwp' := (BI.equiv_iff.mp wp_unfold).1 $$ Hwp
      ispecialize Hwp' $$ %σ %e' %σ' %ε [Hσ Hs Hε]
      · isplitl [Hσ] <;> try iassumption
        isplitl [Hs] <;> iassumption
      imod Hwp' with Hwp''
      iapply (wp_adequacy_spec_coupl (GF := GF) (n := n+1) (m := n+1)
        (e₁ := e) (σ₁ := σ) (e₁' := e') (σ₁' := σ') (φ := φ) (ε := ε)) $$ Hwp''
      rw [show e.toVal? = none from Hnone]
      iintro %σ₂ %e₂' %σ₂' %ε' Hprog
      iapply (wp_adequacy_prog_coupl (GF := GF) (n := n+1) (m := n)
        (e₁ := e) (σ₁ := σ₂) (e₁' := e₂') (σ₁' := σ₂') (φ := φ) (ε := ε')
        (Hnone := Hnone)) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ Hspec
      simp only [Nat.repeat]
      imodintro
      iintro !>
      imodintro
      iapply (wp_adequacy_spec_coupl (GF := GF) (n := n) (m := n)
        (e₁ := e₃) (σ₁ := σ₃) (e₁' := e₃') (σ₁' := σ₃') (φ := φ) (ε := ε₃)) $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %ε₄ HZ
      imod HZ with ⟨Hσ', Hs', Hε', Hcnt⟩
      iapply ih ε₄ e₃ e₄' σ₄ σ₄'
      isplitl [Hσ'] <;> try iassumption
      isplitl [Hs'] <;> try iassumption
      isplitl [Hε'] <;> iassumption

end Adequacy

theorem wp_adequacy_exec_n {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp) (σ σ' : State) (n : Nat) (φ : Val → Val → Prop)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS false GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) ((execN n ⟨e, σ⟩).map (·.expr))
        ((limExec ⟨e', σ'⟩).map (·.expr)) := by
  by_cases hε1 : (1 : ENNReal) ≤ ε
  ·
    refine AddCoupl.trivial_of_one_le hε1 ?_
    rw [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ⟨e, σ⟩
  have hε_lt : ε < 1 := lt_of_not_ge hε1
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness_no_lc (GF := GF) n 0 (fun Hinv => ?_)
  iintro _Hcreds
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (spec_ra_init (GF := GF) e' σ') with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod (ec_alloc (GF := GF) ε hε_lt) with ⟨%γec, HecAuth, HecFrag⟩
  let IAS : ApproxisGS false GF := {
    appGS  := IA
    specGS := ISpec
    ecGS   := { toECPreGS := IECPre, γec := γec }
    invGS  := Hinv }
  ihave Hwp' := Hwp IAS
  ispecialize Hwp' $$ HspecFrag HecFrag
  ihave Hstep := wp_adequacy_step_fupdN (GF := GF) (IA := IAS) ε e e' σ σ' n φ
  ispecialize Hstep $$ [HappAuth HspecAuth HecAuth Hwp']
  · isplitl [HappAuth] <;> try iassumption
    isplitl [HspecAuth] <;> try iassumption
    isplitl [HecAuth] <;> try iassumption
  iexact Hstep

theorem wp_adequacy {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp) (σ σ' : State) (ε : ENNReal) (φ : Val → Val → Prop)
    (Hwp : ∀ (_ : ApproxisGS false GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) ((limExec ⟨e, σ⟩).map (·.expr))
        ((limExec ⟨e', σ'⟩).map (·.expr)) := by
  have Hlifted : AddCoupl ε (fun (p : Cfg × Exp) => adequacyRel φ (p.1.expr, p.2))
      (limExec ⟨e, σ⟩) ((limExec ⟨e', σ'⟩).map (·.expr)) := by
    apply limExec_AddCoupl
    intro n
    have H := wp_adequacy_exec_n (GF := GF) e e' σ σ' n φ ε Hwp
    have Hmap_id :
        ((limExec (⟨e', σ'⟩ : Cfg)).map (·.expr)) =
          ((limExec (⟨e', σ'⟩ : Cfg)).map (·.expr)).map id := by
      rw [MeasureTheory.Measure.map_id]
    rw [Hmap_id] at H
    have := AddCoupl.map_inv (α' := Exp) (β' := Exp)
      (f := fun (c : Cfg) => c.expr) (g := id) Measurable.of_discrete measurable_id H
    exact this
  have Hmap_id :
      ((limExec (⟨e', σ'⟩ : Cfg)).map (·.expr)) =
        ((limExec (⟨e', σ'⟩ : Cfg)).map (·.expr)).map id := by
    rw [MeasureTheory.Measure.map_id]
  rw [Hmap_id] at Hlifted
  have H_pushed := AddCoupl.map (α' := Exp) (β' := Exp)
    (f := fun (c : Cfg) => c.expr) (g := id) Measurable.of_discrete measurable_id
    (S := fun (p : Cfg × Exp) => adequacyRel φ (p.1.expr, p.2))
    (R := adequacyRel φ)
    (fun {a b} h => h) Hlifted
  simp only [MeasureTheory.Measure.map_id] at H_pushed
  exact H_pushed

theorem wp_adequacy_error_lim {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp) (σ σ' : State) (ε : ENNReal) (φ : Val → Val → Prop)
    (Hwp : ∀ (_ : ApproxisGS false GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε' -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) ((limExec ⟨e, σ⟩).map (·.expr))
        ((limExec ⟨e', σ'⟩).map (·.expr)) := by
  by_cases hε_top : ε = (⊤ : ENNReal)
  · subst hε_top
    refine AddCoupl.trivial_of_one_le (by exact le_top (a := (1 : ENNReal))) ?_
    rw [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using limExec_leq_mass (r := 1) (fun n => execN_univ_le_one n ⟨e, σ⟩)
  apply AddCoupl.limit
  intro δ Hδ
  apply wp_adequacy (GF := GF) (ε := ε + δ)
  intro Hinst
  have Hlt : ε < ε + δ := ENNReal.lt_add_right hε_top (ne_of_gt Hδ)
  exact Hwp Hinst (ε + δ) Hlt

theorem wp_adequacy_mass {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp) (σ σ' : State) (φ : Val → Val → Prop)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS false GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    (limExec ⟨e, σ⟩).map (·.expr) Set.univ ≤
        (limExec ⟨e', σ'⟩).map (·.expr) Set.univ + ε := by
  have := AddCoupl.mass_leq (wp_adequacy e e' σ σ' ε φ Hwp)
  simpa using this

end ProbLang
