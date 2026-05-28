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

set_option linter.unusedSectionVars false

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.AdequacyHelpers ProbLang.ApproxisWpGS

variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

class abbrev RefinesPreGS (rT : outParam (Type _)) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] (GF : BundledGFunctors) :=
  AppPreGS rT GF, SpecPreGS rT GF, ECPreGS GF, InvGpreS GF, NaInvG GF

/-- `⤇ e` and `⤇ Ectx.fill [] e` are definitionally equal. Named for use in
`rw` rewrites where Lean's defeq is not exposed (e.g. when adapting hypotheses
to fit lemmas that universally quantify over an evaluation context). -/
theorem spec_eq_fill_nil {GF : BundledGFunctors} [SpecGS rT GF] (e : Exp rT) :
    (iprop(⤇ e) : IProp GF) = iprop(⤇ Ectx.fill ([] : Ectx rT) e) :=
  rfl

/-- `⤇ Ectx.fill [] v.1` and `⤇ Exp.ofVal v` are definitionally equal. -/
theorem spec_fill_nil_eq_ofVal {GF : BundledGFunctors} [SpecGS rT GF] (v : Val rT) :
    (iprop(⤇ Ectx.fill ([] : Ectx rT) v.1) : IProp GF) = iprop(⤇ Exp.ofVal v) :=
  rfl

/-- **Relational adequacy.** If a parametric `refines` judgement holds for
every `ApproxisRGS` instance, and its relation `A IR` implies a pure
relation `φ`, then the limit-step distributions of `e` and `e'` are coupled
by `φ` with zero error.

This is the bridge from the Iris-internal `refines` judgement to the
external probabilistic semantics, obtained by combining the WP-level
adequacy theorem `wp_adequacy_error_lim` with the parametric assumption
to allocate a fresh non-atomic invariant pool. -/
theorem refines_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT false GF), lrel rT GF)
    (φ : (Val rT) → (Val rT) → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : ApproxisRGS rT false GF) (v v' : Val rT),
      ⊢@{IProp GF} iprop((A IR).car v v' -∗ ⌜φ v v'⌝))
    (Hlog : ∀ (IR : ApproxisRGS rT false GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  -- Reduce relational adequacy to the WP-level adequacy theorem.
  apply wp_adequacy_error_lim (GF := GF) e e' σ σ' 0 φ
  intro IGS ε' Hε'pos
  iintro He' Herr
  -- Allocate the non-atomic invariant pool needed to build an `ApproxisRGS`.
  imod (Iris.NonAtomicInvariant.alloc (GF := GF)) with HnaEx
  icases HnaEx with ⟨%γ, Htok⟩
  set IR : ApproxisRGS rT false GF :=
    { approxisGS := IGS, naInvG := _, nais := γ }
  -- Specialize the parametric `refines` to this instance and unfold to a WP.
  ihave HlogR := Hlog IR
  ihave Hwp := refines_unfold $$ HlogR
  -- Adapt `He'` to the empty-context form expected by `Hwp`.
  ihave He'' : iprop(⤇ Ectx.fill ([] : Ectx rT) e') $$ [He']
  · rw [← spec_eq_fill_nil e']; iexact He'
  ispecialize Hwp $$ %([] : Ectx rT) %ε' He'' Htok Herr %Hε'pos
  -- Weaken the WP post-condition from `(A IR).car v v'` to `φ v v'`.
  iapply (wp_mono
    (Φ := fun v => iprop(∃ (v' : Val rT) (ε'' : ENNReal),
      (⤇ Ectx.fill ([] : Ectx rT) v'.1) ∗ (naOwnP (rT := rT) (hlc := false) ⊤) ∗ (↯ ε'') ∗
      (⌜(0 : ENNReal) < ε''⌝) ∗ (A IR).car v v')))
  case HΦ =>
    intro v
    iintro Hpost
    icases Hpost with ⟨%v', %_, Hspec, _, _, %_, HA_v⟩
    iexists v'
    isplitl [Hspec]
    · rw [← spec_fill_nil_eq_ofVal v']; iexact Hspec
    · iapply (HA IR v v') $$ HA_v
  iexact Hwp

/-- Concrete model for Approxis -/
noncomputable def ApproxisFunctor (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (F := ℕ+) (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (SpecHeap rT), by infer_instance⟩
  | 5 => ⟨constOF SpecTapes, by infer_instance⟩
  | 6 => ⟨constOF (SpecProg rT), by infer_instance⟩
  | 7 => ⟨constOF (Auth ℕ+ ErrorCredit), by infer_instance⟩
  | 8 => ⟨NaInvF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-! ### `RefinesPreGS` instances for `ApproxisFunctor` -/

instance ApproxisFunctor_WsatGpreS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : WsatGpreS (ApproxisFunctor rT) where
  inv := ⟨0, rfl⟩
  enabled := ⟨1, rfl⟩
  disabled := ⟨2, rfl⟩

instance ApproxisFunctor_LcGpreS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : LcGpreS (ApproxisFunctor rT) where
  lc_elem := ⟨3, rfl⟩

instance ApproxisFunctor_InvGpreS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : InvGpreS (ApproxisFunctor rT) where
  toWsatGpreS := ApproxisFunctor_WsatGpreS rT
  toLcGpreS := ApproxisFunctor_LcGpreS rT

instance ApproxisFunctor_AppPreGS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : AppPreGS rT (ApproxisFunctor rT) where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_SpecPreGS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : SpecPreGS rT (ApproxisFunctor rT) where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_ECPreGS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : ECPreGS (ApproxisFunctor rT) where
  ec := ⟨7, rfl⟩

instance ApproxisFunctor_NaInvG (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : NaInvG (ApproxisFunctor rT) where
  inv := ⟨8, rfl⟩

instance ApproxisFunctor_RefinesPreGS (rT : Type) [ProbLangℝ rT] [Countable rT]
    [MeasurableSingletonClass rT] : RefinesPreGS rT (ApproxisFunctor rT) where

end ProbLang
