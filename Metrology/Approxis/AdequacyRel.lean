import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Adequacy
import Iris.Algebra.Auth
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Instances.Lib.FUpd

/-!
# Relational Adequacy

Relational adequacy theorem. Bridges from a parametric `refines` proof
(in the Iris logic) to an `AddCoupl` between the limit-step semantics
distributions of the two programs.

Key result: `refines_coupling` — given a parametric `refines ⊤ e e' A` proof
that holds under any `ApproxisRGS`, and a value-relation extraction
`A v v' -∗ ⌜φ v v'⌝`, conclude `AddCoupl 0 (adequacyRel φ) (limExec e) (limExec e')`.

## Rocq source
`clutch/theories/approxis/adequacy_rel.v` — `approximates_coupling`,
`refines_coupling`.
-/

namespace ProbLang

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.AdequacyHelpers ProbLang.ApproxisWpGS

/-! ## `refines_coupling`

Zero-error relational adequacy: a parametric `refines ⊤ e e' A` proof under
any `ApproxisRGS false GF`, together with `A v v' -∗ ⌜φ v v'⌝`, gives an
unconditional coupling between the two programs' limit semantics.

This is the corollary form (`refines_coupling`) of Rocq's
`approximates_coupling`. It avoids the error-credit-splitting infrastructure
since `ε = 0` and the `wp_adequacy_error_lim` iteration provides the small
positive budget directly. -/
theorem refines_coupling {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF] [INaPre : NaInvG GF]
    (A : ∀ (_ : ApproxisRGS false GF), lrel GF)
    (φ : Val → Val → Prop) (e e' : Exp) (σ σ' : State)
    (HA : ∀ (IR : ApproxisRGS false GF) (v v' : Val),
      ⊢@{IProp GF} iprop((A IR).car v v' -∗ ⌜φ v v'⌝))
    (Hlog : ∀ (IR : ApproxisRGS false GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) ((limExec ⟨e, σ⟩).map (·.expr))
        ((limExec ⟨e', σ'⟩).map (·.expr)) := by
  apply wp_adequacy_error_lim (GF := GF) e e' σ σ' 0 φ
  intro IGS ε' Hε'pos
  iintro He' Herr
  imod (Iris.NonAtomicInvariant.alloc (GF := GF)) with HnaEx
  icases HnaEx with ⟨%γ, Htok⟩
  set IR : ApproxisRGS false GF :=
    { approxisGS := IGS
      naInvG := INaPre
      nais := γ }
  have HlogIR : (⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) := Hlog IR
  ihave Hlog' := HlogIR
  ihave Hwp := refines_unfold (E := ⊤) (e := e) (e' := e') (A := A IR) $$ Hlog'
  have hf : e' = Ectx.fill ([] : Ectx) e' := rfl
  ihave He'' : iprop(⤇ Ectx.fill ([] : Ectx) e') $$ [He']
  · rw [← hf]; iexact He'
  ispecialize Hwp $$ %([] : Ectx) %ε' He'' Htok Herr %Hε'pos
  iapply (wp_mono
    (Φ := fun v => iprop(∃ (v' : Val) (ε'' : ENNReal),
      (⤇ Ectx.fill ([] : Ectx) v'.1) ∗ (naOwnP ⊤) ∗ (↯ ε'') ∗
      (⌜(0 : ENNReal) < ε''⌝) ∗ (A IR).car v v'))
    (Ψ := fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
  case HΦ =>
    intro v
    iintro Hpost
    icases Hpost with ⟨%v', %ε'', Hspec, Hna, Herr', %Hpos, HA_v⟩
    iexists v'
    isplitl [Hspec]
    · have hf : (iprop(⤇ Ectx.fill ([] : Ectx) v'.1) : IProp GF) =
                iprop(⤇ Exp.ofVal v') := rfl
      rw [← hf]; iexact Hspec
    · ihave Hbridge := HA IR v v'
      ihave Hphi := Hbridge $$ HA_v
      iexact Hphi
  iexact Hwp

/-! ## A concrete `BundledGFunctors` for the OTP example

Mirrors Rocq's `approxisRΣ := #[approxisΣ; na_invΣ]` where
`approxisΣ := #[invΣ; ghost_mapΣ loc val; ghost_mapΣ loc tape; specΣ; ecΣ]`.

Slots used:
* 0: wsat invariant heap (uses `LaterOF IdOF` to refer abstractly to `IProp Σ`)
* 1: wsat enabled set
* 2: wsat disabled set
* 3: later-credits authority
* 4: program heap (`AppPreGS.heap`)
* 5: program tapes (`AppPreGS.tapes`)
* 6: spec program
* 7: spec heap (different slot from program heap!)
* 8: spec tapes (different slot from program tapes!)
* 9: error credits
* 10: NA invariant pool
-/

/-- Concrete model `BundledGFunctors` for OTP/Approxis. -/
noncomputable def otpSigma : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF, by infer_instance⟩
  | 1  => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3  => ⟨AuthURF (F := ℕ+) (constOF Credit), by infer_instance⟩
  | 4  => ⟨constOF SpecHeap, by infer_instance⟩
  | 5  => ⟨constOF SpecTapes, by infer_instance⟩
  | 6  => ⟨constOF SpecProg, by infer_instance⟩
  | 7  => ⟨constOF SpecHeap, by infer_instance⟩
  | 8  => ⟨constOF SpecTapes, by infer_instance⟩
  | 9  => ⟨constOF (Auth ℕ+ ErrorCredit), by infer_instance⟩
  | 10 => ⟨NaInvF, by infer_instance⟩
  | _  => ⟨constOF Unit, by infer_instance⟩

/-! ## PreGS instances for `otpSigma`

Each `ElemG` instance points at a specific slot of `otpSigma`. -/

instance otpSigma_WsatGpreS : WsatGpreS otpSigma where
  inv := { τ := 0, transp := by unfold otpSigma; rfl }
  enabled := { τ := 1, transp := by unfold otpSigma; rfl }
  disabled := { τ := 2, transp := by unfold otpSigma; rfl }

instance otpSigma_LcGpreS : LcGpreS otpSigma where
  lc_elem := { τ := 3, transp := by unfold otpSigma; rfl }

instance otpSigma_InvGpreS : InvGpreS otpSigma where
  toWsatGpreS := otpSigma_WsatGpreS
  toLcGpreS := otpSigma_LcGpreS

instance otpSigma_AppPreGS : AppPreGS otpSigma where
  heap := { τ := 4, transp := by unfold otpSigma; rfl }
  tapes := { τ := 5, transp := by unfold otpSigma; rfl }

instance otpSigma_SpecPreGS : SpecPreGS otpSigma where
  prog := { τ := 6, transp := by unfold otpSigma; rfl }
  heap := { τ := 7, transp := by unfold otpSigma; rfl }
  tapes := { τ := 8, transp := by unfold otpSigma; rfl }

instance otpSigma_ECPreGS : ECPreGS otpSigma where
  ec := { τ := 9, transp := by unfold otpSigma; rfl }

instance otpSigma_NaInvG : NaInvG otpSigma where
  inv := { τ := 10, transp := by unfold otpSigma; rfl }

end ProbLang
