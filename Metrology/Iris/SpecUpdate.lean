module

public import Metrology.Iris.SpecProgram
public import Metrology.ProbLang.Exec
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-!
# Spec-side update modality

Ports `clutch.base_logic.spec_update`. The modality lets us take deterministic
spec-side steps (at most `n`, or unbounded via `specUpdate`) while holding the
spec interpretation and under an Iris fancy-update mask.

Rocq `stepN n a a' = 1` (mass-one at a singleton in a discrete distribution) is
replaced here by the cleaner `pexecN n ρ = MeasureTheory.Measure.dirac ρ'` — equivalent over
our countable `Cfg` type and avoids a mass-1-to-dirac detour.
-/

open Std Iris Iris.Std Iris.BI COFE ProbLang

namespace ProbLang

/-- The spec interpretation is a predicate on configurations. In the concrete
instantiation this is `Cfg.specAuth`, but we parameterize over the class so
clients of the modality can substitute alternative interpretations (e.g. for
meta-logical arguments). -/
class SpecUpdateGS (GF : BundledGFunctors) where
  specInterp : Cfg → IProp GF

/-- Deterministic spec-side composition: if `pexecN n ρ = δ ρ'` and
`pexecN m ρ' = δ ρ''`, then `pexecN (n+m) ρ = δ ρ''`. -/
theorem pexecN_det_trans {n m : Nat} {ρ ρ' ρ'' : Cfg}
    (Hn : pexecN n ρ = MeasureTheory.Measure.dirac ρ') (Hm : pexecN m ρ' = MeasureTheory.Measure.dirac ρ'') :
    pexecN (n + m) ρ = MeasureTheory.Measure.dirac ρ'' := by
  rw [pexecN_plus, Hn, MeasureTheory.Measure.dirac_bind Measurable.of_discrete, Hm]

section SpecUpdate

variable {GF : BundledGFunctors} {hlc : Bool} [InvGS_gen hlc GF] [SpecUpdateGS GF]

/-- Parameterized spec-side update: starting from spec state `ρ`, advance by
exactly `n` deterministic steps to some `ρ'`, updating the spec interpretation
and delivering `P`. -/
def specUpdateN (n : Nat) (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ ρ, SpecUpdateGS.specInterp ρ -∗ |={E}=> (∃ ρ', ⌜pexecN n ρ = MeasureTheory.Measure.dirac ρ'⌝ ∗ SpecUpdateGS.specInterp ρ' ∗ P))

/-- Spec-side update: advance by some (existentially quantified) number of
deterministic steps. This is the main modality used by spec rules.

⚠️ **Must be `abbrev`, not `def`** — per iris-lean gotcha #1, iprop tactics
(`ispecialize`, `iapply`, `iexact`) need to see through this when the
argument `P` varies (e.g. under `specUpdate E (fun v => ...)`). -/
abbrev specUpdate (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ ρ, SpecUpdateGS.specInterp ρ -∗ |={E}=> (∃ ρ' n, ⌜pexecN n ρ = MeasureTheory.Measure.dirac ρ'⌝ ∗ SpecUpdateGS.specInterp ρ' ∗ P))

/-- `specUpdateN n` is stronger than the unindexed `specUpdate`. -/
theorem specUpdateN_specUpdate {n : Nat} {E : CoPset} {P : IProp GF} :
    ⊢@{IProp GF} specUpdateN n E P -∗ specUpdate E P := by
  iintro H
  unfold specUpdateN specUpdate
  iintro %ρ Hρ
  ispecialize H $$ %ρ Hρ
  imod H with ⟨%ρ', %Hstep, Hρ', HP⟩
  imodintro
  iexists ρ', n
  isplitr; · ipure_intro; exact Hstep
  isplitl [Hρ'] <;> iassumption

/-- Return: `P` implies `specUpdateN 0 E P` (take no steps). -/
theorem specUpdateN_ret {E : CoPset} {P : IProp GF} :
    P ⊢@{IProp GF} specUpdateN 0 E P := by
  iintro HP
  unfold specUpdateN
  iintro %ρ Hρ
  imodintro
  iexists ρ
  isplitr; · ipure_intro; rfl
  isplitl [Hρ] <;> iassumption

/-- Return: `P` implies `specUpdate E P` (take no steps). -/
theorem specUpdate_ret {E : CoPset} {P : IProp GF} :
    P ⊢@{IProp GF} specUpdate E P := by
  iintro HP
  unfold specUpdate
  iintro %ρ Hρ
  imodintro
  iexists ρ, 0
  isplitr; · ipure_intro; rfl
  isplitl [Hρ] <;> iassumption

/-- Bind for `specUpdateN`: steps compose additively. Requires `E1 ⊆ E2` for
the fancy-update mask management. -/
theorem specUpdateN_bind {n m : Nat} {E1 E2 : CoPset} {P Q : IProp GF}
    (HE : E1 ⊆ E2) :
    iprop(specUpdateN n E1 P ∗ (P -∗ specUpdateN m E2 Q)) ⊢@{IProp GF}
      specUpdateN (n + m) E2 Q := by
  iintro ⟨HP, HPQ⟩
  unfold specUpdateN
  iintro %ρ Hρ
  imod (BIFUpdate.subset HE) with Hclose
  ispecialize HP $$ %ρ Hρ
  imod HP with ⟨%ρ', %Hnstep, Hρ', HPres⟩
  imod Hclose
  ispecialize HPQ $$ HPres %ρ' Hρ'
  imod HPQ with ⟨%ρ'', %Hmstep, Hρ'', HQres⟩
  imodintro
  iexists ρ''
  isplitr
  · ipure_intro; exact pexecN_det_trans Hnstep Hmstep
  isplitl [Hρ''] <;> iassumption

/-- Bind for `specUpdate`. -/
theorem specUpdate_bind {E1 E2 : CoPset} {P Q : IProp GF} (HE : E1 ⊆ E2) :
    iprop(specUpdate E1 P ∗ (P -∗ specUpdate E2 Q)) ⊢@{IProp GF} specUpdate E2 Q := by
  iintro ⟨HP, HPQ⟩
  unfold specUpdate
  iintro %ρ Hρ
  imod (BIFUpdate.subset HE) with Hclose
  ispecialize HP $$ %ρ Hρ
  imod HP with ⟨%ρ', %n, %Hnstep, Hρ', HPres⟩
  imod Hclose
  ispecialize HPQ $$ HPres %ρ' Hρ'
  imod HPQ with ⟨%ρ'', %m, %Hmstep, Hρ'', HQres⟩
  imodintro
  iexists ρ'', (n + m)
  isplitr
  · ipure_intro; exact pexecN_det_trans Hnstep Hmstep
  isplitl [Hρ''] <;> iassumption

/-- Monotonicity of `specUpdateN` under a fancy-update continuation. -/
theorem specUpdateN_mono_fupd {n : Nat} {E : CoPset} {P Q : IProp GF} :
    iprop(specUpdateN n E P ∗ (P ={E}=∗ Q)) ⊢@{IProp GF} specUpdateN n E Q := by
  iintro ⟨HP, HPQ⟩
  unfold specUpdateN
  iintro %ρ Hρ
  ispecialize HP $$ %ρ Hρ
  imod HP with ⟨%ρ', %Hstep, Hρ', HPres⟩
  ispecialize HPQ $$ HPres
  imod HPQ with HQres
  imodintro
  iexists ρ'
  isplitr; · ipure_intro; exact Hstep
  isplitl [Hρ'] <;> iassumption

/-- Monotonicity of `specUpdate` under a fancy-update continuation. -/
theorem specUpdate_mono_fupd {E : CoPset} {P Q : IProp GF} :
    iprop(specUpdate E P ∗ (P ={E}=∗ Q)) ⊢@{IProp GF} specUpdate E Q := by
  iintro ⟨HP, HPQ⟩
  unfold specUpdate
  iintro %ρ Hρ
  ispecialize HP $$ %ρ Hρ
  imod HP with ⟨%ρ', %n, %Hstep, Hρ', HPres⟩
  ispecialize HPQ $$ HPres
  imod HPQ with HQres
  imodintro
  iexists ρ', n
  isplitr; · ipure_intro; exact Hstep
  isplitl [Hρ'] <;> iassumption

/-- Plain monotonicity (non-fupd continuation). -/
theorem specUpdateN_mono {n : Nat} {E : CoPset} {P Q : IProp GF} :
    iprop(specUpdateN n E P ∗ (P -∗ Q)) ⊢@{IProp GF} specUpdateN n E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdateN_mono_fupd
  isplitl [HP]; · iassumption
  iintro HP'
  imodintro
  iapply HPQ $$ HP'

theorem specUpdate_mono {E : CoPset} {P Q : IProp GF} :
    iprop(specUpdate E P ∗ (P -∗ Q)) ⊢@{IProp GF} specUpdate E Q := by
  iintro ⟨HP, HPQ⟩
  iapply specUpdate_mono_fupd
  isplitl [HP]; · iassumption
  iintro HP'
  imodintro
  iapply HPQ $$ HP'

/-- Fancy-update absorbs into `specUpdateN`. -/
theorem fupd_specUpdateN {n : Nat} {E : CoPset} {P : IProp GF} :
    (iprop(|={E}=> specUpdateN n E P)) ⊢@{IProp GF} specUpdateN n E P := by
  iintro H
  unfold specUpdateN
  iintro %ρ Hρ
  imod H with H
  ispecialize H $$ %ρ Hρ
  iapply H

/-- Fancy-update absorbs into `specUpdate`. -/
theorem fupd_specUpdate {E : CoPset} {P : IProp GF} :
    (iprop(|={E}=> specUpdate E P)) ⊢@{IProp GF} specUpdate E P := by
  iintro H
  unfold specUpdate
  iintro %ρ Hρ
  imod H with H
  ispecialize H $$ %ρ Hρ
  iapply H

/-- Left frame. -/
theorem specUpdateN_frame_l {n : Nat} {E : CoPset} {R P : IProp GF} :
    iprop(R ∗ specUpdateN n E P) ⊢@{IProp GF} specUpdateN n E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdateN_mono
  isplitl [HP]; · iassumption
  iintro HP'
  isplitl [HP']; · iassumption
  iassumption

theorem specUpdate_frame_l {E : CoPset} {R P : IProp GF} :
    iprop(R ∗ specUpdate E P) ⊢@{IProp GF} specUpdate E iprop(P ∗ R) := by
  iintro ⟨HR, HP⟩
  iapply specUpdate_mono
  isplitl [HP]; · iassumption
  iintro HP'
  isplitl [HP']; · iassumption
  iassumption

end SpecUpdate

/-! ## Default instance: the concrete `Cfg.specAuth` interpretation. -/

instance defaultSpecUpdateGS {GF : BundledGFunctors} [SpecGS GF] :
    SpecUpdateGS GF where
  specInterp := Cfg.specAuth

end ProbLang
