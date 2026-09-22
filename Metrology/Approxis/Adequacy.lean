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

theorem fupd_laterN_to_stepFupdN (E : CoPset) (n : Nat) {Q : IProp GF} : iprop%
    (|={E}=> ▷^[n+1] Q) ⊢@{IProp GF} |={E}[E]▷=>^[n+1] Q :=
  (BIFUpdate.mono (step_fupdN_intro Std.LawfulSet.subset_refl)).trans BIFUpdate.trans

theorem step_fupd_except_0 (E1 E2 : CoPset) {P : IProp GF} : iprop%
    (|={E1}[E2]▷=> ◇ P) ⊢@{IProp GF} |={E1}[E2]▷=> P :=
  BIFUpdate.mono (later_mono fupd_except0)

theorem step_fupdN_except_0 (E1 E2 : CoPset) {P : IProp GF} (n : Nat) : iprop%
    (|={E1}[E2]▷=>^[n+1] ◇ P) ⊢@{IProp GF} |={E1}[E2]▷=>^[n+1] P :=
  calc
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> ◇ P := (step_fupdN_add (n := n) (m := 1)).mp
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> P   := step_fupdN_mono (step_fupd_except_0 E1 E2)
    _ ⊢ |={E1}[E2]▷=>^[n+1] P               := (step_fupdN_add (n := n) (m := 1)).mpr

theorem step_fupdN_plain_forall (E : CoPset) {A : Type _} (Φ : A → IProp GF)
    [∀ x, Plain (Φ x)] (n : Nat) : iprop%
    (|={E}▷=>^[n] ∀ x, Φ x) ⊣⊢@{IProp GF} ∀ x, |={E}▷=>^[n] Φ x := by
  refine ⟨forall_intro (fun x => step_fupdN_mono (forall_elim x)), ?_⟩
  cases n with
  | zero => simp only [Nat.repeat]; exact forall_intro (forall_elim ·)
  | succ n =>
    calc
      _ ⊢ ∀ x, |={E}=> ▷^[n+1] ◇ Φ x := forall_mono fun _ => step_fupdN_plain
      _ ⊢ |={E}=> ∀ x, ▷^[n+1] ◇ Φ x := (fupd_plain_forall Std.LawfulSet.subset_refl).mpr
      _ ⊢ |={E}=> ▷^[n+1] ∀ x, ◇ Φ x := BIFUpdate.mono (laterN_forall (n+1)).mpr
      _ ⊢ |={E}=> ▷^[n+1] ◇ ∀ x, Φ x := BIFUpdate.mono (laterN_mono (n+1) except0_forall.mpr)
      _ ⊢ |={E}[E]▷=>^[n+1] ◇ ∀ x, Φ x := fupd_laterN_to_stepFupdN E n
      _ ⊢ |={E}[E]▷=>^[n+1] ∀ x, Φ x := step_fupdN_except_0 E E n

theorem stepFupdN_zero {E E' : CoPset} (P : IProp GF) : iprop%
    (|={E}[E']▷=>^[0] P) ⊣⊢@{IProp GF} P := ⟨Entails.rfl, Entails.rfl⟩

theorem fupd_pure_wand_intro {p : Prop} {P : IProp GF} : iprop%
    (⌜p⌝ -∗ |={∅}=> P) ⊢@{IProp GF} |={∅}=> (⌜p⌝ -∗ P) := by
  iintro HwP
  by_cases hp : p
  · imod HwP $$ %hp with HfP
    iintro !> -
    iexact HfP
  · iintro !> %HS
    exact absurd HS hp

theorem fupd_stepFupdN_plain_forall_1 (Φ : A → IProp GF) [∀ x, Plain (Φ x)] (n : Nat) : iprop%
    (∀ (x : A), |={∅}=> |={∅}[∅]▷=>^[n] Φ x) ⊢@{IProp GF}
      |={∅}=> |={∅}[∅]▷=>^[n] ∀ (x : A), Φ x := by
  cases n with
  | zero =>
    simp only [Nat.repeat]
    exact (fupd_plain_forall Std.LawfulSet.subset_refl).mpr
  | succ n =>
    calc
      _ ⊢ ∀ x, |={∅}=> ▷^[n+1] ◇ Φ x :=
          forall_mono fun _ => (BIFUpdate.mono step_fupdN_plain).trans BIFUpdate.trans
      _ ⊢ |={∅}=> ∀ x, ▷^[n+1] ◇ Φ x := (fupd_plain_forall Std.LawfulSet.subset_refl).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ∀ x, ◇ Φ x := BIFUpdate.mono (laterN_forall (n+1)).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ◇ ∀ x, Φ x := BIFUpdate.mono (laterN_mono (n+1) except0_forall.mpr)
      _ ⊢ |={∅}[∅]▷=>^[n+1] ◇ ∀ x, Φ x := fupd_laterN_to_stepFupdN ∅ n
      _ ⊢ |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := step_fupdN_except_0 ∅ ∅ n
      _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := fupd_intro

/-- Arity-2 version of `fupd_stepFupdN_plain_forall_1`: peel the leading binder with
`forall_mono`, then close with the arity-1 lemma.  `_3` and `_4` iterate the same step. -/
theorem fupd_stepFupdN_plain_forall_2 {A B : Type _} (Ψ : A → B → IProp GF)
    [∀ a b, Plain (Ψ a b)] (n : Nat) : iprop%
    (∀ (a : A) (b : B), |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b) ⊢@{IProp GF}
      |={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : A) (b : B), Ψ a b :=
  (forall_mono fun a => fupd_stepFupdN_plain_forall_1 (Ψ a) n).trans
    (fupd_stepFupdN_plain_forall_1 _ n)

theorem fupd_stepFupdN_plain_forall_3 {A B C : Type _} (Ψ : A → B → C → IProp GF)
    [∀ a b c, Plain (Ψ a b c)] (n : Nat) : iprop%
    (∀ (a : A) (b : B) (c : C), |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c) ⊢@{IProp GF}
      |={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : A) (b : B) (c : C), Ψ a b c :=
  (forall_mono fun a => fupd_stepFupdN_plain_forall_2 (Ψ a) n).trans
    (fupd_stepFupdN_plain_forall_1 _ n)

theorem fupd_stepFupdN_plain_forall_4 {A B C D : Type _} (Ψ : A → B → C → D → IProp GF)
    [∀ a b c d, Plain (Ψ a b c d)] (n : Nat) : iprop%
    (∀ (a : A) (b : B) (c : C) (d : D), |={∅}=> |={∅}[∅]▷=>^[n] Ψ a b c d) ⊢@{IProp GF}
      |={∅}=> |={∅}[∅]▷=>^[n] ∀ (a : A) (b : B) (c : C) (d : D), Ψ a b c d :=
  (forall_mono fun a => fupd_stepFupdN_plain_forall_3 (Ψ a) n).trans
    (fupd_stepFupdN_plain_forall_1 _ n)

theorem stepFupdN_pure_wand_intro (E : CoPset) (n : Nat) {p q : Prop} : iprop%
    (⌜p⌝ -∗ |={E}[E]▷=>^[n] ⌜q⌝) ⊢@{IProp GF}
      |={E}[E]▷=>^[n] (⌜p⌝ -∗ ⌜q⌝) := by
  by_cases hp : p
  · iintro H
    ispecialize H $$ %hp
    iapply step_fupdN_mono (wand_intro sep_elim_left) $$ [$]
  · iintro H
    iapply step_fupdN_intro Std.LawfulSet.subset_refl
    iintro !> %_
    grind

end FupdPlainForall
end ProbLang.AdequacyHelpers

namespace ProbLang


open ProbLang.AdequacyHelpers

variable {rT : Type _} [ProbLangℝ rT]

def adequacyRel (φ : Val rT → Val rT → Prop) : Set ((Exp rT) × (Exp rT)) :=
  fun p => ∃ (v v' : Val rT), p.1.toVal? = some v ∧ p.2.toVal? = some v' ∧ φ v v'

/-- The coupling adequacy propagates: running `ρ` for `n` steps couples, up to error `ε`, with
the *whole* limiting execution of `ρ'`, the two results related by `φ`.  Reducible so that the
`AddCoupl` API applies to it directly. -/
@[reducible] def execCoupl (φ : Val rT → Val rT → Prop) (ε : ENNReal) (n : Nat)
    (ρ ρ' : Cfg rT) : Prop :=
  AddCoupl ε (adequacyRel φ) (asExpr (execN n ρ)) (limExecV ρ')

/-- `execN` never creates mass, so its expression pushforward is a subprobability measure. -/
theorem asExpr_execN_univ_le_one (n : Nat) (ρ : Cfg rT) : asExpr (execN n ρ) Set.univ ≤ 1 := by
  unfold asExpr
  rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
  simpa using execN_univ_le_one n ρ

/-- The limiting execution is a subprobability measure too. -/
theorem limExecV_univ_le_one (ρ : Cfg rT) : limExecV ρ Set.univ ≤ 1 := by
  unfold limExecV asExpr
  rw [MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
  simpa using limExec_leq_mass (r := 1) (fun n => execN_univ_le_one n ρ)

section Adequacy

variable {GF : BundledGFunctors} [IA : ApproxisGS rT .hasNoLC GF]

theorem wp_adequacy_spec_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ σ₂ e₂' σ₂' ε',
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜execCoupl φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜execCoupl φ ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝) := by
  set Ψ : State rT → Cfg rT → ENNReal → IProp GF :=
    fun σ₀ ⟨e₀', σ₀'⟩ ε₀ =>
      iprop((∀ σ₂ e₂' σ₂' ε',
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜execCoupl φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) -∗
        |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜execCoupl φ ε₀ m ⟨e₁, σ₀⟩ ⟨e₀', σ₀'⟩⌝))
  iintro Hspec HZ
  iapply (specCoupl_ind (Ψ := Ψ)) $$ [] %σ₁ %e₁' %σ₁' %ε Hspec HZ
  iintro !> %σ₀ %c₀ %ε₀ H
  obtain ⟨e₀', σ₀'⟩ := c₀
  simp only [Ψ]
  iintro HZ
  icases H with ⟨%HVac | HZApp | HCpl⟩
  · imodintro
    iapply (laterN_intro n).trans (step_fupdN_intro Std.LawfulSet.empty_subset)
    ipureintro
    exact AddCoupl.trivial_of_one_le HVac (asExpr_execN_univ_le_one m ⟨e₁, σ₀⟩)
  · iapply HZ
    iexact HZApp
  · icases HCpl with ⟨%S, %k, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HAC, %HX₂meas, %HX₂bnd, %HεBnd, %Herase1, %Herase1', HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono
        (P := iprop(⌜∀ σ₂ e₂' σ₂', S σ₂ ⟨e₂', σ₂'⟩ →
          execCoupl φ (X₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
      iintro %Hpure !%
      exact AddCoupl_erasure_erasable_exp_rhs
        (m := k)
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
    · refine step_fupdN_mono
        (P := iprop(∀ σ₂ e₂' σ₂',
          ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ ⌜execCoupl φ (X₂ ⟨e₂', σ₂'⟩) m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
      iintro %H !%
      exact H
    iapply fupd_stepFupdN_plain_forall_3
    iintro %σ₂ %e₂' %σ₂'
    ispecialize HCont $$ %σ₂ %e₂' %σ₂'
    iapply BIFUpdate.mono
    · exact stepFupdN_pure_wand_intro ∅ n
    iapply fupd_pure_wand_intro
    iintro %HS
    imod HCont $$ %HS with ⟨HΨ, -⟩
    iapply HΨ
    iexact HZ

theorem wp_adequacy_prog_coupl (n m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal)
    (Hnone : e₁.toVal? = none) :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ e₂ σ₂ e₂' σ₂' ε',
        Z e₂ σ₂ e₂' σ₂' ε' -∗ |={∅}=> |={∅}[∅]▷=>^[n]
          (⌜execCoupl φ ε' m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) -∗
      |={∅}=> |={∅}[∅]▷=>^[n]
        (⌜execCoupl φ ε (m + 1) ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝) := by
  simp only [execCoupl, execN_succ_not_isValue (ρ := ⟨e₁, σ₁⟩) (Exp.toVal?_eq_none.mp Hnone) m]
  iintro HCpl Hcoupl
  icases HCpl with ⟨%k, %μ₁', %X₂, %_Hred, %_Hbnd, %Hexp, %Herase', Hcnt⟩
  iapply BIFUpdate.mono
  · refine step_fupdN_mono
      (P := iprop(⌜∀ e₂ σ₂ e₂' σ₂',
          execCoupl φ (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
    iintro %Hpure !%
    exact AddCoupl_erasure_erasable_exp_lhs_kanto
      (m := k) (μ₁' := μ₁') (E₂ := X₂)
      (hErase₁' := Herase')
      (hExp := Hexp)
      (hCont := fun ρ ρ' => by
        obtain ⟨e₂, σ₂⟩ := ρ
        obtain ⟨e₂', σ₂'⟩ := ρ'
        exact Hpure e₂ σ₂ e₂' σ₂')
  iapply BIFUpdate.mono
  · refine step_fupdN_mono
      (P := iprop(∀ e₂ σ₂ e₂' σ₂',
          ⌜execCoupl φ (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) m ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ : IProp GF)) ?_
    iintro %H !%
    exact H
  iapply fupd_stepFupdN_plain_forall_4
  iintro %e₂ %σ₂ %e₂' %σ₂'
  imod Hcnt $$ %e₂ %σ₂ %e₂' %σ₂' with Hcnt
  iapply Hcoupl
  iexact Hcnt

theorem wp_adequacy_spec_coupl_zero (m : Nat) (e₁ : Exp rT) (σ₁ : State rT)
    (e₁' : Exp rT) (σ₁' : State rT)
    (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (φ : Val rT → Val rT → Prop) (ε : ENNReal) :
    specCoupl ∅ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF}
      (∀ σ₂ e₂' σ₂' ε',
        Z σ₂ ⟨e₂', σ₂'⟩ ε' -∗ |={∅}=>
          (⌜execCoupl φ ε' m ⟨e₁, σ₂⟩ ⟨e₂', σ₂'⟩⌝)) -∗
      |={∅}=>
        (⌜execCoupl φ ε m ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩⌝) :=
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
      ∀ σ₁ e₁' σ₁' ε₁,
        (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
          |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
            iprop(|={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
                errInterp (rT := rT) ε₂ ∗ Φ v)) := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  rw [wpPre_value_Z_eq (E := E) (v := v) (Φ := Φ)]
  simp only [wpPre_match_eq]
  iintro Hwp %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  iapply (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ Hwp %σ₁ %e₁' %σ₁' %ε₁ [$]

theorem wp_adequacy_val_fupd (e e' : Exp rT) (σ σ' : State rT) (n : Nat)
    (φ : Val rT → Val rT → Prop) (v : Val rT) (ε : ENNReal) (He : e.toVal? = some v) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=>
        (⌜execCoupl φ ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝) := by
  obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some He).symm
  iintro ⟨Hσ, Hs, Hε, Hwp⟩
  imod wp_value_specCoupl_unfold ⊤ He $$ Hwp %σ %e' %σ' %ε [$]
    with HspecC
  iapply wp_adequacy_spec_coupl_zero $$ HspecC
  iintro %σ₂ %e₂' %σ₂' %ε' HZ
  imod HZ with ⟨-, Hs', -, %v', Hv', %Hφrel⟩
  ihave %Heq := specAuth_specFrag_agree $$ Hs' Hv'
  subst Heq
  imod (BIFUpdate.subset (E2 := ∅) Std.LawfulSet.empty_subset) with -
  iintro !%
  unfold execCoupl asExpr limExecV asExpr
  cases n with
  | zero =>
    simp only [execN, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n =>
    rw [execN_succ_isValue (ρ := ⟨Exp.ofVal v, σ₂⟩) v.isValue n,
        limExec_of_isVal (e := Exp.ofVal v') (σ := σ₂') v'.2]
    simp only [MeasureTheory.Measure.map_dirac' (Cfg.measurable_expr (α := rT))]
    exact AddCoupl.dirac (a := Exp.ofVal v) (b := Exp.ofVal v') (ε := ε') (adequacyRel φ)
      ⟨v, v', Exp.toVal?_ofVal v, Exp.toVal?_ofVal v', Hφrel⟩

theorem wp_adequacy_step_fupdN (ε : ENNReal) (e e' : Exp rT) (σ σ' : State rT)
    (n : Nat) (φ : Val rT → Val rT → Prop) :
    (appStateAuth σ ∗ specAuth ⟨e', σ'⟩ ∗ ecAuth ε ∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
      ⊢@{IProp GF} |={⊤, ∅}=> |={∅}[∅]▷=>^[n]
        (⌜execCoupl φ ε n ⟨e, σ⟩ ⟨e', σ'⟩⌝) := by
  revert e σ e' σ' ε
  induction n with
  | zero =>
    intro ε e e' σ σ'
    iintro -
    imod (BIFUpdate.subset (E2 := ∅) Std.LawfulSet.empty_subset) with -
    imodintro
    simp only [Nat.repeat]
    ipureintro
    unfold execCoupl asExpr
    simp only [execN_zero, MeasureTheory.Measure.map_zero]
    exact AddCoupl.zero_left _ _
  | succ n ih =>
    intro ε e e' σ σ'
    iintro ⟨Hσ, Hs, Hε, Hwp⟩
    by_cases He : e.isValue
    · obtain ⟨v, Hv⟩ := Exp.toVal?_eq_some_of_isValue He
      imod wp_adequacy_val_fupd e e' σ σ' (n+1) φ v ε Hv $$ [$] with %Hpure
      imodintro
      iapply (laterN_intro (n+1)).trans (step_fupdN_intro Std.LawfulSet.subset_refl)
      ipureintro
      exact Hpure
    · have Hnone : e.toVal? = none := Exp.toVal?_eq_none.mpr He
      imod (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ Hwp %σ %e' %σ' %ε [$] with Hwp''
      iapply wp_adequacy_spec_coupl $$ Hwp''
      rw [Hnone]
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
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    execCoupl φ ε n ⟨e, σ⟩ ⟨e', σ'⟩ := by
  by_cases hε1 : (1 : ENNReal) ≤ ε
  · exact AddCoupl.trivial_of_one_le hε1 (asExpr_execN_univ_le_one n ⟨e, σ⟩)
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 (fun Hinv => ?_)
  iintro -
  imod (app_ra_init σ) with ⟨%IA, HappAuth⟩
  imod (spec_ra_init e' σ') with ⟨%ISpec, HspecAuth, HspecFrag⟩
  imod (ec_alloc ε (lt_of_not_ge hε1)) with ⟨%γec, HecAuth, HecFrag⟩
  let IAS : ApproxisGS rT .hasNoLC GF := {
    appGS  := IA
    specGS := ISpec
    ecGS   := { toECPreGS := IECPre, γec := γec }
    invGS  := Hinv }
  ihave Hwp' := Hwp IAS $$ HspecFrag HecFrag
  iapply wp_adequacy_step_fupdN $$ [$]

theorem wp_adequacy
    (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩)
        (limExecV ⟨e', σ'⟩) := by
  -- `limExecV = asExpr ∘ limExec`, and `limExecV_AddCoupl` takes the limit *under*
  -- the `asExpr` pushforward (via `AddCoupl.iSup_left`). The old route pulled the
  -- coupling back along `Cfg.expr` with `AddCoupl.map_inv`, took the limit, then
  -- pushed it forward again with `AddCoupl.map`; `map_inv` is the one genuinely
  -- discrete step in the adequacy path, and this avoids it entirely.
  exact limExecV_AddCoupl fun n => wp_adequacy_exec_n e e' σ σ' n φ ε Hwp

theorem wp_adequacy_error_lim
    (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal) (φ : Val rT → Val rT → Prop)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF) (ε' : ENNReal), ε < ε' →
      ⊢@{IProp GF} ⤇ e' -∗ ec ε' -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩)
        (limExecV ⟨e', σ'⟩) := by
  by_cases hε_top : ε = (⊤ : ENNReal)
  · subst hε_top
    exact AddCoupl.trivial_of_one_le le_top (limExecV_univ_le_one ⟨e, σ⟩)
  apply AddCoupl.limit
  intro δ Hδ
  apply wp_adequacy (GF := GF) (ε := ε + δ)
  intro Hinst
  exact Hwp Hinst (ε + δ) (ENNReal.lt_add_right hε_top (ne_of_gt Hδ))

theorem wp_adequacy_mass
    (e e' : Exp rT) (σ σ' : State rT) (φ : Val rT → Val rT → Prop)
    (ε : ENNReal)
    (Hwp : ∀ (_ : ApproxisGS rT .hasNoLC GF),
      ⊢@{IProp GF} ⤇ e' -∗ ec ε -∗
        wp ⊤ e (fun v => iprop(∃ v' : Val rT, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝))) :
    limExecV ⟨e, σ⟩ Set.univ ≤
        limExecV ⟨e', σ'⟩ Set.univ + ε := by
  simpa using AddCoupl.mass_leq (wp_adequacy e e' σ σ' ε φ Hwp)

end ProbLang
