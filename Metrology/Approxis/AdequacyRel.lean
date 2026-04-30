module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.Model
public import Metrology.Approxis.Adequacy
public import Iris.Algebra.Auth
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! # Relational adequacy: bridging parametric `refines` to an `AddCoupl` on `limExec`. -/

namespace ProbLang

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.AdequacyHelpers ProbLang.ApproxisWpGS

class abbrev RefinesPreGS (GF : BundledGFunctors) :=
  AppPreGS GF, SpecPreGS GF, ECPreGS GF, InvGpreS GF, NaInvG GF

theorem refines_coupling {GF : BundledGFunctors} [RefinesPreGS GF]
    (A : ∀ (_ : ApproxisRGS false GF), lrel GF)
    (φ : Val → Val → Prop) (e e' : Exp) (σ σ' : State)
    (HA : ∀ (IR : ApproxisRGS false GF) (v v' : Val),
      ⊢@{IProp GF} iprop((A IR).car v v' -∗ ⌜φ v v'⌝))
    (Hlog : ∀ (IR : ApproxisRGS false GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  apply wp_adequacy_error_lim (GF := GF) e e' σ σ' 0 φ
  intro IGS ε' Hε'pos
  iintro He' Herr
  imod (Iris.NonAtomicInvariant.alloc (GF := GF)) with HnaEx
  icases HnaEx with ⟨%γ, Htok⟩
  set IR : ApproxisRGS false GF :=
    { approxisGS := IGS
      naInvG := _
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

/-- Concrete model for Approxis -/
noncomputable def ApproxisFunctor : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (F := ℕ+) (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF SpecHeap, by infer_instance⟩
  | 5 => ⟨constOF SpecTapes, by infer_instance⟩
  | 6 => ⟨constOF SpecProg, by infer_instance⟩
  | 7 => ⟨constOF (Auth ℕ+ ErrorCredit), by infer_instance⟩
  | 8 => ⟨NaInvF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-! ### PreGS instances for `otpSigma` -/

instance ApproxisFunctor_WsatGpreS : WsatGpreS ApproxisFunctor where
  inv := ⟨0, rfl⟩
  enabled := ⟨1, rfl⟩
  disabled := ⟨2, rfl⟩

instance ApproxisFunctor_LcGpreS : LcGpreS ApproxisFunctor where
  lc_elem := ⟨3, rfl⟩

instance ApproxisFunctor_InvGpreS : InvGpreS ApproxisFunctor where
  toWsatGpreS := ApproxisFunctor_WsatGpreS
  toLcGpreS := ApproxisFunctor_LcGpreS

instance ApproxisFunctor_AppPreGS : AppPreGS ApproxisFunctor where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_SpecPreGS : SpecPreGS ApproxisFunctor where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_ECPreGS : ECPreGS ApproxisFunctor where
  ec := ⟨7, rfl⟩

instance ApproxisFunctor_NaInvG : NaInvG ApproxisFunctor where
  inv := ⟨8, rfl⟩

instance ApproxisFunctor_RefinesPreGS : RefinesPreGS ApproxisFunctor where

end ProbLang
