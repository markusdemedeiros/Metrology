module

public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Exec
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! # Spec-side update modality -/

open Std Iris Iris.Std Iris.BI COFE ProbLang MeasureTheory.Measure Measurable

namespace ProbLang

/-- Spec Update. Gives an interpretation of a spec into an resource. -/
class SpecUpdateGS (GF : BundledGFunctors) where
  specInterp : Cfg → IProp GF

open SpecUpdateGS

section SpecUpdate

variable {GF : BundledGFunctors} {hlc : Bool} [InvGS_gen hlc GF] [SpecUpdateGS GF]

/-- Spec update for `n` deterministic steps. -/
def specUpdateN (n : Nat) (E : CoPset) (P : IProp GF) : IProp GF := iprop%
  ∀ ρ, specInterp ρ -∗ |={E}=> ∃ ρ', ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P

/-- Spec update quantified over an unknown number of deterministic steps -/
abbrev specUpdate (E : CoPset) (P : IProp GF) : IProp GF := iprop%
  ∀ ρ, specInterp ρ -∗ |={E}=> (∃ ρ' n, ⌜pexecN n ρ = dirac ρ'⌝ ∗ specInterp ρ' ∗ P)

theorem specUpdateN_specUpdate {n : Nat} {E : CoPset} {P : IProp GF} :
    specUpdateN n E P ⊢ specUpdate E P := by
  unfold specUpdateN specUpdate
  iintro H %ρ Hρ
  imod H $$ %ρ Hρ with ⟨%ρ', %Hstep, Hρ', HP⟩
  imodintro
  iexists ρ', n
  iframe
  ipure_intro
  assumption

theorem specUpdate_zero {E : CoPset} {P : IProp GF} : P ⊢ specUpdateN 0 E P := by
  unfold specUpdateN
  iintro HP %ρ Hρ !>
  iexists ρ
  iframe
  ipure_intro
  rfl

theorem specUpdate_ret {E : CoPset} {P : IProp GF} : P ⊢ specUpdate E P := by
  iintro _
  iapply specUpdateN_specUpdate
  iapply specUpdate_zero $$ [$]

theorem specUpdateN_bind {n m : Nat} {E1 E2 : CoPset} {P Q : IProp GF} (HE : E1 ⊆ E2) : iprop%
    specUpdateN n E1 P ∗ (P -∗ specUpdateN m E2 Q) ⊢ specUpdateN (n + m) E2 Q := by
  unfold specUpdateN
  iintro ⟨Hn, Hm⟩ %ρ Hρ
  imod BIFUpdate.subset HE with Hclose
  imod Hn $$ %ρ Hρ with ⟨%ρ', %Hexec₁, Hs, HP⟩
  imod Hclose with -
  imod Hm $$ HP %ρ' Hs with ⟨%ρ'', %Hexec₂, Hs, HQ⟩
  imodintro
  iexists ρ''
  iframe
  ipure_intro
  exact pexecN_det_trans Hexec₁ Hexec₂

theorem specUpdate_bind {E1 E2 : CoPset} {P Q : IProp GF} (HE : E1 ⊆ E2) : iprop%
    specUpdate E1 P ∗ (P -∗ specUpdate E2 Q) ⊢ specUpdate E2 Q := by
  unfold specUpdate
  iintro ⟨H₁, H₂⟩ %ρ Hρ
  imod BIFUpdate.subset HE with Hclose
  imod H₁ $$ %ρ Hρ with ⟨%ρ', %n₁, %Hexec₁, Hs, HP⟩
  imod Hclose with -
  imod H₂ $$ HP %ρ' Hs with ⟨%ρ'', %n₂, %Hexec₂, Hs, HQ⟩
  imodintro
  iexists ρ'', n₁ + n₂
  iframe
  ipure_intro
  exact pexecN_det_trans Hexec₁ Hexec₂

theorem specUpdateN_mono_fupd {n : Nat} {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdateN n E P ∗ (P ={E}=∗ Q) ⊢ specUpdateN n E Q := by
  unfold specUpdateN
  iintro ⟨HP, HPQ⟩ %ρ Hρ
  imod HP $$ %ρ Hρ with ⟨%ρ', %Hstep, Hρ', HPres⟩
  imod HPQ $$ HPres with HQres
  imodintro
  iexists ρ'
  iframe
  ipure_intro
  assumption

theorem specUpdate_mono_fupd {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdate E P ∗ (P ={E}=∗ Q) ⊢ specUpdate E Q := by
  unfold specUpdate
  iintro ⟨HP, HPQ⟩ %ρ Hρ
  imod HP $$ %ρ Hρ with ⟨%ρ', %n, %Hstep, Hρ', HPres⟩
  imod HPQ $$ HPres with HQres
  imodintro
  iexists ρ', n
  iframe
  ipure_intro
  assumption

theorem specUpdateN_mono {n : Nat} {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdateN n E P ∗ (P -∗ Q) ⊢ specUpdateN n E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdateN_mono_fupd
  iframe
  iintro _ !>
  iapply HPQ $$ [$]

theorem specUpdate_mono {E : CoPset} {P Q : IProp GF} : iprop%
    specUpdate E P ∗ (P -∗ Q) ⊢ specUpdate E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdate_mono_fupd
  iframe
  iintro _ !>
  iapply HPQ $$ [$]

theorem fupd_specUpdateN {n : Nat} {E : CoPset} {P : IProp GF} : iprop%
    (|={E}=> specUpdateN n E P) ⊢ specUpdateN n E P := by
  unfold specUpdateN
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

theorem fupd_specUpdate {E : CoPset} {P : IProp GF} : iprop%
    (|={E}=> specUpdate E P) ⊢ specUpdate E P := by
  unfold specUpdate
  iintro H %ρ Hρ
  imod H
  iapply H $$ [$]

/-- Left frame. -/
theorem specUpdateN_frame_l {n : Nat} {E : CoPset} {R P : IProp GF} : iprop%
    R ∗ specUpdateN n E P ⊢ specUpdateN n E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdateN_mono
  iframe
  iintro _
  iframe

theorem specUpdate_frame_l {E : CoPset} {R P : IProp GF} :
    iprop(R ∗ specUpdate E P) ⊢@{IProp GF} specUpdate E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdate_mono
  iframe
  iintro _
  iframe

end SpecUpdate

/-- Concrete Approxis SpecUpdateGS -/
instance defaultSpecUpdateGS {GF} [SpecGS GF] : SpecUpdateGS GF where
  specInterp := Cfg.specAuth

end ProbLang
