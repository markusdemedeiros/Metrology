module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Erasure

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS ProbLang.Cfg
open scoped AppGS

namespace ProbLang.AdequacyHelpers

section FupdPlainForall

variable {rT : Type _} [ProbLangℝ rT]
variable {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]

variable {E E' : CoPset}

open Iris Iris.BI Iris.BI.BIBase Iris.ProofMode

-- #check step_fupdN_intro

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

theorem fupd_plain_forall_2 (E : CoPset) {A : Type _} (Φ : A → IProp GF)
    [∀ x, Plain (Φ x)] :
    iprop((∀ x, |={E}=> Φ x) ⊢ |={E}=> ∀ x, Φ x) := by
  refine .trans ?_ Iris.fupd_plainly_forall_2
  refine forall_mono (fun x => ?_)
  exact BIFUpdate.mono Plain.plain

theorem fupd_plain_forall' (E : CoPset) {A : Type _} (Φ : A → IProp GF) [∀ x, Plain (Φ x)] : iprop%
    (|={E}=> ∀ x, Φ x) ⊣⊢@{IProp GF} ∀ x, |={E}=> Φ x := ⟨fupd_forall, fupd_plain_forall_2 E Φ⟩

theorem fupd_except_0 (E1 E2 : CoPset) (P : IProp GF) :
    iprop(|={E1,E2}=> ◇ P) ⊢@{IProp GF} iprop(|={E1,E2}=> P) := by
  refine .trans (BIFUpdate.mono (except0_mono (fupd_intro (E := E2)))) ?_
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
    exact step_fupdN_mono (forall_elim x)
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

omit [ProbLangℝ rT] in
theorem fupd_stepFupdN_plain_forall_3
    (Ψ : State rT → Exp rT → State rT → IProp GF)
    [instP : ∀ a b c, Plain (Ψ a b c)] (n : Nat) :
    iprop(∀ (a : State rT) (b : Exp rT) (c : State rT),
        |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c) ⊢@{IProp GF}
      iprop(|={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : State rT) (b : Exp rT) (c : State rT), Ψ a b c) := by
  refine (forall_mono (fun a => forall_mono (fun b =>
    fupd_stepFupdN_plain_forall_1 (GF := GF) (fun c => Ψ a b c) n))).trans ?_
  refine (forall_mono (fun a =>
    fupd_stepFupdN_plain_forall_1 (GF := GF)
      (fun b => iprop(∀ c, Ψ a b c)) n)).trans ?_
  exact fupd_stepFupdN_plain_forall_1 (GF := GF)
    (fun a => iprop(∀ b c, Ψ a b c)) n

omit [ProbLangℝ rT] in
theorem fupd_stepFupdN_plain_forall_4
    (Ψ : Exp rT → State rT → Exp rT → State rT → IProp GF)
    [∀ a b c d, Plain (Ψ a b c d)] (n : Nat) :
    iprop(∀ (a : Exp rT) (b : State rT) (c : Exp rT) (d : State rT),
        |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c d) ⊢@{IProp GF}
      iprop(|={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : Exp rT) (b : State rT) (c : Exp rT) (d : State rT), Ψ a b c d) := by
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
  · refine Entails.trans ?step (step_fupdN_mono (wand_intro sep_elim_left))
    refine (sep_emp (P := iprop(⌜p⌝ -∗ |={E}[E]▷=>^[n] ⌜q⌝))).mpr.trans ?_
    refine (sep_mono_right (pure_intro (P := emp) hp)).trans ?_
    exact wand_elim_left
  · refine Entails.trans ?_ ( step_fupdN_intro Std.LawfulSet.subset_refl)
    iintro H !> %H
    grind

end FupdPlainForall

end ProbLang.AdequacyHelpers

namespace ProbLang


open ProbLang.AdequacyHelpers

variable {rT : Type _} [ProbLangℝ rT]

def adequacyRel (φ : Val rT → Val rT → Prop) : Set ((Exp rT) × (Exp rT)) :=
  fun p => ∃ (v v' : Val rT), p.1.toVal? = some v ∧ p.2.toVal? = some v' ∧ φ v v'

section Adequacy

variable {GF : BundledGFunctors} [IA : ApproxisGS rT .hasNoLC GF]

theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          (asExpr (execN m ⟨e₁, σ₁⟩))
          (limExecV ⟨e₁', σ₁'⟩)⌝) := by
  set Ψ : State rT → Cfg rT → ENNReal → IProp GF :=
    fun σ₀ ⟨e₀', σ₀'⟩ ε₀ =>
      iprop((∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝)) -∗
        |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε₀ (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₀⟩))
            (limExecV ⟨e₀', σ₀'⟩)⌝))
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
    ipureintro
    exact AddCoupl.trivial_of_one_le HVac (by
      unfold asExpr
      rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
      simpa using execN_univ_le_one m ⟨e₁, σ₀⟩)
  ·
    iapply HZ
    iexact HZApp
  ·
    icases HCpl with ⟨%S, %k, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HAC, %HX₂meas, %HX₂bnd, %HεBnd, %Herase1, %Herase1', HCont⟩
    have Himpl : (∀ σ₂ e₂' σ₂', S σ₂ ⟨e₂', σ₂'⟩ →
      AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
        (asExpr (execN m ⟨e₁, σ₂⟩))
        (limExecV ⟨e₂', σ₂'⟩)) →
      AddCoupl ε₀ (adequacyRel φ)
        (asExpr (execN m ⟨e₁, σ₀⟩))
        (limExecV ⟨e₀', σ₀'⟩) := fun Hpure =>
      AddCoupl_erasure_erasable_exp_rhs
        (e₁ := e₁) (e₁' := e₀') (σ₁ := σ₀) (σ₁' := σ₀') (m := k) (n := m)
        (ε₂ := ∫⁻ ρ, X₂ ρ ∂(μ₁'.bind (fun σ => pexecN k ⟨e₀', σ⟩)))
        (hE₂meas := HX₂meas)
        (hCoupl := HAC)
        (hBoundSum := _root_.le_refl _)
        (hEpsSum := HεBnd)
        (hErase₁ := Herase1)
        (hErase₁' := Herase1')
        (hCont := fun σ₂ ρ' hR => by
          obtain ⟨e₂', σ₂'⟩ := ρ'
          exact Hpure σ₂ e₂' σ₂' hR)
    iapply BIFUpdate.mono
    · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
        (P := iprop(⌜∀ σ₂ e₂' σ₂', S σ₂ ⟨e₂', σ₂'⟩ →
          AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF)) ?_
      iintro %Hpure
      ipureintro
      exact Himpl Hpure
    iapply BIFUpdate.mono
    · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
        (P := iprop(∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
          ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF)) ?_
      refine Entails.trans (forall_mono fun _ => forall_mono fun _ =>
        forall_mono fun _ => pure_wand.mp) ?_
      refine Entails.trans (forall_mono fun _ => forall_mono fun _ => pure_forall.mpr) ?_
      refine Entails.trans (forall_mono fun _ => pure_forall.mpr) ?_
      exact pure_forall.mpr
    iapply (fupd_stepFupdN_plain_forall_3 (GF := GF) (n := n)
      (Ψ := fun σ₂ e₂' σ₂' => iprop(
        ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
          (asExpr (execN m ⟨e₁, σ₂⟩))
          (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF)))
    iintro %σ₂ %e₂' %σ₂'
    ispecialize HCont $$ %σ₂ %e₂' %σ₂'
    iapply BIFUpdate.mono
    · exact stepFupdN_pure_wand_intro (GF := GF) (E := ∅) (n := n)
        (p := S σ₂ ⟨e₂', σ₂'⟩)
        (q := AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
          (asExpr (execN m ⟨e₁, σ₂⟩))
          (limExecV ⟨e₂', σ₂'⟩))
    iapply (fupd_pure_wand_intro (GF := GF) (S σ₂ ⟨e₂', σ₂'⟩)
      iprop(|={∅}[∅]▷=>^[n] ⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
        (asExpr (execN m ⟨e₁, σ₂⟩))
        (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF))
    iintro %HS
    ispecialize HCont $$ %HS
    ihave HCont' : iprop(|={∅}=> (((∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT) (ε' : ENNReal),
            Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
              (⌜AddCoupl ε' (adequacyRel φ)
                (asExpr (execN m ⟨e₁, σ₂⟩))
                (limExecV ⟨e₂', σ₂'⟩)⌝)) -∗
            |={∅}=> |={∅}[∅]▷=>^[n]
              (⌜AddCoupl (X₂ ⟨e₂', σ₂'⟩) (adequacyRel φ)
                (asExpr (execN m ⟨e₁, σ₂⟩))
                (limExecV ⟨e₂', σ₂'⟩)⌝)) ∧
        specCoupl ∅ σ₂ e₂' σ₂' (X₂ ⟨e₂', σ₂'⟩) Z)) $$ [HCont]
    · iexact HCont
    imod HCont' with HCont''
    ihave HΨ := and_elim_l (P := _) (Q := _) $$ HCont''
    iapply HΨ
    iexact HZ

theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal)
    (Hnone : e₁.toVal? = none) :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT) (ε' : ENNReal),
        Z e₂ σ₂ e₂' σ₂' ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜AddCoupl ε' (adequacyRel φ)
            (asExpr (execN m ⟨e₂, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          (asExpr (execN (m + 1) ⟨e₁, σ₁⟩))
          (limExecV ⟨e₁', σ₁'⟩)⌝) := by
  have Hnv : ¬ e₁.isValue := Exp.toVal?_eq_none.mp Hnone
  rw [execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) Hnv m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %X₂, %_Hred, %_Hbnd, %Hexp, %Herase', Hcnt⟩
  iapply BIFUpdate.mono
  ·
    refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
      (P := iprop(⌜∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
          AddCoupl (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            (asExpr (execN m ⟨e₂, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF)) ?_
    iintro %Hpure
    ipureintro
    exact AddCoupl_erasure_erasable_exp_lhs_kanto
      (e₁ := e₁) (e₁' := e₁') (σ₁ := σ₁) (σ₁' := σ₁') (n := m) (m := k)
      (μ₁' := μ₁') (E₂ := X₂) (ε := ε)
      (hErase₁' := Herase')
      (hExp := Hexp)
      (hCont := fun ρ ρ' => by
        obtain ⟨e₂, σ₂⟩ := ρ
        obtain ⟨e₂', σ₂'⟩ := ρ'
        exact Hpure e₂ σ₂ e₂' σ₂')
  iapply BIFUpdate.mono
  · refine stepFupdN_mono (E := ∅) (E' := ∅) (n := n)
      (P := iprop(∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
          ⌜AddCoupl (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) (adequacyRel φ)
            (asExpr (execN m ⟨e₂, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝ : IProp GF)) ?_
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

theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT) (ε' : ENNReal),
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=>
          (⌜AddCoupl ε' (adequacyRel φ)
            (asExpr (execN m ⟨e₁, σ₂⟩))
            (limExecV ⟨e₂', σ₂'⟩)⌝)) -∗
      |={∅}=>
        (⌜AddCoupl ε (adequacyRel φ)
          (asExpr (execN m ⟨e₁, σ₁⟩))
          (limExecV ⟨e₁', σ₁'⟩)⌝) :=
  wp_adequacy_spec_coupl 0 m e₁ σ₁ e₁' σ₁' Z φ ε

theorem wpPre_value_Z_eq {v : Val rT} {Φ : Val rT → IProp GF} (E : CoPset) :
    (fun (σ₂ : State rT) (ρ' : Cfg rT) (ε₂ : ENNReal) =>
      iprop(|={∅, E}=> stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
        errInterp (rT := rT) ε₂ ∗ Φ v))
    = (fun (σ₂ : State rT) (ρ' : Cfg rT) (ε₂ : ENNReal) =>
      match (Exp.ofVal v).toVal? with
      | some v => iprop(|={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
            errInterp (rT := rT) ε₂ ∗ Φ v)
      | none => iprop(progCoupl (Exp.ofVal v) σ₂ ρ'.expr ρ'.state ε₂
          (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E}=>
                stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗
                  errInterp (rT := rT) ε₄ ∗ wp (GF := GF) E e₃ Φ)))))) := by
  funext σ₂ ρ' ε₂
  rw [Exp.toVal?_ofVal]

-- Bridging two match-compiler artifacts is the whole point of this lemma, so the
-- reference to `.match_1` is deliberate rather than an accident to be refactored away.
set_option linter.auxLemma false in
omit [ProbLangℝ rT] in
theorem wpPre_match_eq (motive : Option (Val rT) → Sort u)
    (x : Option (Val rT)) (some_f : (v : Val rT) → motive (some v))
    (none_f : Unit → motive none) :
    ProbLang.wpPre_value_Z_eq.match_1 (rT := rT) motive x some_f none_f =
    ProbLang.ApproxisWpGS.wpPre.match_1 (rT := rT) motive x some_f none_f := by
  cases x <;> rfl

theorem wp_value_specCoupl_unfold {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (E : CoPset) (He : e.toVal? = some v) :
    wp (GF := GF) E e Φ ⊢@{IProp GF}
      ∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
        (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
          |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
            iprop(|={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
                errInterp (rT := rT) ε₂ ∗ Φ v)) := by
  have he_eq : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  subst he_eq
  rw [wpPre_value_Z_eq (E := E) (v := v) (Φ := Φ)]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave Hwp' := (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ Hwp
  ispecialize Hwp' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; iassumption
    isplitl [Hs]; iassumption
    iassumption
  iexact Hwp'

theorem wp_adequacy_val_fupd (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (v : Val rT) (ε : ENNReal) (He : e.toVal? = some v) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=>
        (⌜AddCoupl ε (adequacyRel φ)
          (asExpr (execN n ⟨e, σ⟩))
          (limExecV ⟨e', σ'⟩)⌝) := by
  have he_eq : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  subst he_eq
  iintro ⟨Hσ, Hs, Hε, Hwp⟩
  ihave HspecPre := wp_value_specCoupl_unfold (GF := GF) (Φ := _) ⊤ He $$ Hwp
  ispecialize HspecPre $$ %σ %e' %σ' %ε [$]
  imod HspecPre with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %ε' HZ
  imod HZ with ⟨_, Hs', _, Hφ⟩
  icases Hφ with ⟨%v', Hv', %Hφrel⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) $$ Hs' Hv'
  subst Heq
  imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
  imodintro
  ipureintro
  unfold asExpr limExecV asExpr
  cases n with
  | zero =>
    simp only [execN, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n =>
    have hv_is_val : (Exp.ofVal v).isValue := v.isValue
    rw [execN_succ_isValue (ρ := ⟨Exp.ofVal v, σ₂⟩) hv_is_val n,
        limExec_of_isVal (e := Exp.ofVal v') (σ := σ₂') v'.2,
        MeasureTheory.Measure.map_dirac'
          (Cfg.measurable_expr (α := rT)),
        MeasureTheory.Measure.map_dirac'
          (Cfg.measurable_expr (α := rT))]
    exact AddCoupl.dirac (a := Exp.ofVal v) (b := Exp.ofVal v')
      (ε := ε') (adequacyRel φ)
      ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', Hφrel⟩

theorem wp_adequacy_step_fupdN (ε : ENNReal) (e e' : Exp rT) (σ σ' : State rT)
    (n : Nat) (φ : Val rT → Val rT → Prop) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=> |={∅}[∅]▷=>^[n]
        (⌜AddCoupl ε (adequacyRel φ)
          (asExpr (execN n ⟨e, σ⟩))
          (limExecV ⟨e', σ'⟩)⌝) := by
  revert e σ e' σ' ε
  induction n with
  | zero =>
    intro ε e e' σ σ'
    iintro _
    imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with _
    imodintro
    simp only [Nat.repeat]
    ipureintro
    unfold asExpr
    simp only [execN_zero, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n ih =>
    intro ε e e' σ σ'
    iintro ⟨Hσ, Hs, Hε, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      ihave HvF := wp_adequacy_val_fupd (GF := GF) e e' σ σ' (n+1) φ v ε Hv $$ [$]
      imod HvF with %Hpure
      imodintro
      iapply ProbLang.ApproxisWpGS.stepFupdN_intro Std.LawfulSet.subset_refl (n+1)
      ipureintro
      exact Hpure
    · have Hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      ihave Hwp' := (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ Hwp
      ispecialize Hwp' $$ %σ %e' %σ' %ε [$]
      imod Hwp' with Hwp''
      iapply wp_adequacy_spec_coupl $$ Hwp''
      rw [show e.toVal? = none from Hnone]
      iintro %σ₂ %e₂' %σ₂' %ε' Hprog
      iapply wp_adequacy_prog_coupl (Hnone := Hnone) $$ Hprog
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ Hspec
      simp only [Nat.repeat]
      iintro !> !> !>
      iapply wp_adequacy_spec_coupl $$ Hspec
      iintro %σ₄ %e₄' %σ₄' %ε₄ HZ
      imod HZ with ⟨Hσ', Hs', Hε', Hcnt⟩
      iapply ih ε₄ e₃ e₄' σ₄ σ₄'
      iframe

end Adequacy

variable {GF : BundledGFunctors}
variable [IPre : AppPreGS rT GF] [ISPre : SpecPreGS rT GF] [IECPre : ECPreGS GF]
variable [IInvPre : InvGpreS GF]

theorem wp_adequacy_exec_n
    (e e' : Exp rT) (σ σ' : State rT) (n : Nat) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) (asExpr (execN n ⟨e, σ⟩))
        (limExecV ⟨e', σ'⟩) := by
  by_cases hε1 : (1 : ENNReal) ≤ ε
  · refine AddCoupl.trivial_of_one_le hε1 ?_
    unfold asExpr
    rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
    simpa using execN_univ_le_one n ⟨e, σ⟩
  have hε_lt : ε < 1 := lt_of_not_ge hε1
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) (GF := GF) n 0 (fun Hinv => ?_)
  iintro _Hcreds
  imod (app_ra_init σ) with ⟨%IA, HappAuth⟩
  imod (spec_ra_init e' σ') with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod (ec_alloc ε hε_lt) with ⟨%γec, HecAuth, HecFrag⟩
  let IAS : ApproxisGS rT .hasNoLC GF := {
    appGS  := IA
    specGS := ISpec
    ecGS   := { toECPreGS := IECPre, γec := γec }
    invGS  := Hinv }
  ihave Hwp' := Hwp IAS
  ispecialize Hwp' $$ HspecFrag HecFrag
  iapply wp_adequacy_step_fupdN $$ [$]

theorem wp_adequacy {GF : BundledGFunctors}
    [IPre : AppPreGS rT GF] [ISPre : SpecPreGS rT GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩)
        (limExecV ⟨e', σ'⟩) := by
  -- `limExecV = asExpr ∘ limExec`, and `limExecV_AddCoupl` takes the limit *under*
  -- the `asExpr` pushforward (via `AddCoupl.iSup_left`). The old route pulled the
  -- coupling back along `Cfg.expr` with `AddCoupl.map_inv`, took the limit, then
  -- pushed it forward again with `AddCoupl.map`; `map_inv` is the one genuinely
  -- discrete step in the adequacy path, and this avoids it entirely.
  exact limExecV_AddCoupl fun n => wp_adequacy_exec_n (GF := GF) e e' σ σ' n φ ε Hwp

theorem wp_adequacy_error_lim {GF : BundledGFunctors}
    [IPre : AppPreGS rT GF] [ISPre : SpecPreGS rT GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε' -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩)
        (limExecV ⟨e', σ'⟩) := by
  by_cases hε_top : ε = (⊤ : ENNReal)
  · subst hε_top
    refine AddCoupl.trivial_of_one_le (by exact le_top (a := (1 : ENNReal))) ?_
    unfold limExecV asExpr
    rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
    simpa using limExec_leq_mass (r := 1) (fun n => execN_univ_le_one n ⟨e, σ⟩)
  apply AddCoupl.limit
  intro δ Hδ
  apply wp_adequacy (GF := GF) (ε := ε + δ)
  intro Hinst
  have Hlt : ε < ε + δ := ENNReal.lt_add_right hε_top (ne_of_gt Hδ)
  exact Hwp Hinst (ε + δ) Hlt

theorem wp_adequacy_mass {GF : BundledGFunctors}
    [IPre : AppPreGS rT GF] [ISPre : SpecPreGS rT GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF]
    (e e' : Exp rT) (σ σ' : State rT) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} iprop(⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))) :
    limExecV ⟨e, σ⟩ Set.univ ≤
        limExecV ⟨e', σ'⟩ Set.univ + ε := by
  have := AddCoupl.mass_leq (wp_adequacy e e' σ σ' ε φ Hwp)
  simpa using this

end ProbLang
