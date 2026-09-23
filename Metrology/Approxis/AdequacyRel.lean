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

variable {rT : Type _} [ProbLangℝ rT]

/-- Bundle of the "pre" ghost-state classes needed to instantiate the relational
adequacy theorem. Spelled with instance-implicit fields rather than `class abbrev`:
`class abbrev` flattens each parent's *fields* into value parameters, which since
Lean 4.32 is rejected because e.g. `SpecPreGS.prog` is then an uninferable argument. -/
class RefinesPreGS (rT : outParam (Type _)) [ProbLangℝ rT]
    [MeasurableSingletonClass rT] (GF : BundledGFunctors) where
  [app : AppPreGS rT GF]
  [spec : SpecPreGS rT GF]
  [ec : ECPreGS GF]
  [inv : InvGpreS GF]
  [nainv : NaInvG GF]

attribute [reducible, instance] RefinesPreGS.app RefinesPreGS.spec RefinesPreGS.ec
  RefinesPreGS.inv RefinesPreGS.nainv

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

/-- **Approximate relational adequacy.** If a parametric `refines` judgement
holds for every `ApproxisRGS` instance *given* `↯ ε` to spend, and its relation
`A IR` implies a pure relation `φ`, then the limit-step distributions of `e` and
`e'` are coupled by `φ` **at error `ε`**.

This is Approxis's reason to exist: it is the only way an ε > 0 result leaves the
logic. Rocq's `approximates_coupling`.

The proof is `wp_adequacy_error_lim` at `ε`. That theorem hands the continuation
a supply `↯ ε'` with `ε < ε'`; `ErrorCredit.difference` splits it into the `↯ ε`
the refinement consumes and a strictly positive remainder `↯ (ε' - ε)`, which is
what `refines` needs as its own slack.

Free of `[Countable rT]`: approximate contextual refinement holds for a diffuse
real type. -/
theorem approximates_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF),
      ⊢@{IProp GF} ↯ ε -∗ refines ⊤ e e' (A IR)) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  -- Reduce relational adequacy to the WP-level adequacy theorem.
  apply wp_adequacy_error_lim (GF := GF) e e' σ σ' ε φ
  intro IGS ε' Hε'pos
  iintro He' Herr
  -- Allocate the non-atomic invariant pool needed to build an `ApproxisRGS`.
  imod Iris.NonAtomicInvariant.alloc with ⟨%γ, Htok⟩
  set IR : ApproxisRGS rT .hasNoLC GF :=
    { approxisGS := IGS, naInvG := _, nais := γ }
  -- Split the supply: `ε` for the refinement, `ε' - ε > 0` as its own slack.
  icases ErrorCredit.difference (le_of_lt Hε'pos) $$ Herr with ⟨Hεc, Hrest⟩
  have Hrestpos : (0 : ENNReal) < ε' - ε := tsub_pos_of_lt Hε'pos
  -- Specialize the parametric `refines` to this instance and unfold to a WP.
  ihave HlogR := Hlog IR $$ Hεc
  iunfold refines at HlogR
  -- `HlogR` quantifies over an evaluation context, so put `He'` in empty-context form.
  rw [spec_eq_fill_nil e']
  ispecialize HlogR $$ %([] : Ectx rT) %(ε' - ε) He' Htok Hrest %Hrestpos
  -- Weaken the WP post-condition from `(A IR).car v v'` to `φ v v'`.
  iapply ApproxisWpGS.wp_mono $$ HlogR
  intro v
  iintro Hpost
  icases Hpost with ⟨%v', %_, Hspec, -, -, %_, HA_v⟩
  iexists v'
  isplitl [Hspec]
  · rw [← spec_fill_nil_eq_ofVal v']; iexact Hspec
  · iapply (HA IR v v') $$ HA_v

/-- **Exact relational adequacy**, the `ε = 0` case of `approximates_coupling`.
Approxis's top-level statement for refinements that spend no error. -/
theorem refines_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF),
      ⊢@{IProp GF} refines ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  approximates_coupling A φ e e' σ σ' 0 HA fun IR => by
    iintro -
    iapply Hlog IR

section ApproxisFunctor
variable (rT : Type) [ProbLangℝ rT] [MeasurableSingletonClass rT]

/-- Concrete model for Approxis -/
noncomputable def ApproxisFunctor : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (SpecHeap rT), by infer_instance⟩
  | 5 => ⟨constOF SpecTapes, by infer_instance⟩
  | 6 => ⟨constOF (SpecProg rT), by infer_instance⟩
  | 7 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | 8 => ⟨NaInvF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-! ### `RefinesPreGS` instances for `ApproxisFunctor` -/

instance ApproxisFunctor_WsatGpreS : WsatGpreS (ApproxisFunctor rT) where
  inv := ⟨0, rfl⟩
  enabled := ⟨1, rfl⟩
  disabled := ⟨2, rfl⟩

instance ApproxisFunctor_LcGpreS : LcGpreS (ApproxisFunctor rT) where
  lc_elem := ⟨3, rfl⟩

instance ApproxisFunctor_InvGpreS : InvGpreS (ApproxisFunctor rT) where
  toWsatGpreS := ApproxisFunctor_WsatGpreS rT
  toLcGpreS := ApproxisFunctor_LcGpreS rT

instance ApproxisFunctor_AppPreGS : AppPreGS rT (ApproxisFunctor rT) where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_SpecPreGS : SpecPreGS rT (ApproxisFunctor rT) where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_ECPreGS : ECPreGS (ApproxisFunctor rT) where
  ec := ⟨7, rfl⟩

instance ApproxisFunctor_NaInvG : NaInvG (ApproxisFunctor rT) where
  inv := ⟨8, rfl⟩

instance ApproxisFunctor_RefinesPreGS : RefinesPreGS rT (ApproxisFunctor rT) where

end ApproxisFunctor

end ProbLang
