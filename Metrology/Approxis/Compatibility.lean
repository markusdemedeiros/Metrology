module

public import Metrology.Approxis.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.Model
public import Metrology.Approxis.RelTactics
public import Metrology.Approxis.AppRelRules
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

set_option linter.discrete false


/-! # Compatibility Lemmas

Structural compatibility of the logical relation: one rule per language construct. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

-- **Notation gotcha**: `refines E e e' (C A)` within `iprop(...)` clashes with
-- the `REL _ << _ @ _ : _` notation. The delaborator displays `refines` as
-- `REL ... : A`, and when `A` is actually `C A` (application), the parser/printer
-- get confused. Workaround: use `BI.intuitionistically`/`BI.forall` directly
-- rather than `iprop(□ (∀ ...))` for the few statements that need `C A`.

namespace ProbLang


section Compatibility
variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-- Helper: unfold `lrel_arr` application. Proves that `(lrel_arr A B).car v v'`
is definitionally `⌜v.closed ∧ v'.closed⌝ ∗ □ (∀ w w', A w w' -∗ REL (v w) << (v' w') : B)`,
bridging the `.car`/`lrel.mk` projection that iris tactics don't reduce. The
closedness conjunct is port-specific (Lean's `Val` isn't intrinsically closed). -/
theorem lrel_arr_unfold (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      (⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        □ (∀ (w1 w2 : Val rT), A w1 w2 -∗
          refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B) :=
  BIBase.Entails.rfl

theorem lrel_arr_unfold_wand (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      □ (∀ (w1 w2 : Val rT), A w1 w2 -∗
        refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B) := by
  iintro H
  ihave H' := lrel_arr_unfold A B v v' $$ H
  icases H' with ⟨_, HW⟩
  iexact HW

theorem lrel_arr_unfold_closed (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) := by
  iintro H
  ihave H' := lrel_arr_unfold A B v v' $$ H
  icases H' with ⟨%hc, _⟩
  ipureintro; exact hc

theorem lrel_arr_fold (A B : lrel rT GF) (v v' : Val rT) :
    iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      □ (∀ (w1 w2 : Val rT), A w1 w2 -∗
        refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B)) ⊢@{IProp GF}
      (lrel_arr A B).car v v' :=
  BIBase.Entails.rfl

theorem refines_pair {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      refines ⊤ e2 e2' B -∗
            refines ⊤ (Exp.pair e1 e2) (Exp.pair e1' e2') (lrel_prod A B) := by
  -- Surface form is defeq to the Ectx.fill form below; the `show` consolidates the
  -- one unavoidable bridge here so that callers can use surface syntax directly.
  show _ ⊢@{IProp GF} refines ⊤ e2 e2' B -∗
    refines ⊤ (Ectx.fill [EctxItem.pairR e1] e2)
              (Ectx.fill [EctxItem.pairR e1'] e2') (lrel_prod A B)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.pairR e1] [EctxItem.pairR e1']) $$ IH2
  iintro %v2 %v2' HB
  have hbridge_L : Ectx.fill [EctxItem.pairR e1] v2.1 = Ectx.fill [EctxItem.pairL v2] e1 := rfl
  have hbridge_R : Ectx.fill [EctxItem.pairR e1'] v2'.1 = Ectx.fill [EctxItem.pairL v2'] e1' := rfl
  rw [hbridge_L, hbridge_R]
  iapply (refines_bind [EctxItem.pairL v2] [EctxItem.pairL v2']) $$ IH1
  iintro %v1 %v1' HA
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.pairL v2] v1.1)
    (e2 := Ectx.fill [EctxItem.pairL v2'] v1'.1)
    (v1 := ⟨.pair v1.1 v2.1, IsVal.pair v1.2 v2.2, (IsVal.pair v1.2 v2.2).lc⟩)
    (v2 := ⟨.pair v1'.1 v2'.1, IsVal.pair v1'.2 v2'.2, (IsVal.pair v1'.2 v2'.2).lc⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_prod
  iexists v1, v1', v2, v2'
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  iframe HA
  iexact HB

/-- `refines_injl` (compatibility.v:31): left-injection compatibility. -/
theorem refines_injl {e e' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e e' A)
      ⊢@{IProp GF} refines ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inl] e) (Ectx.fill [EctxItem.inl] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inl] [EctxItem.inl]) $$ IH
  iintro %v %v' HA
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inl] v.1)
    (e2 := Ectx.fill [EctxItem.inl] v'.1)
    (v1 := ⟨.inl v.1, IsVal.inl v.2, (IsVal.inl v.2).lc⟩)
    (v2 := ⟨.inl v'.1, IsVal.inl v'.2, (IsVal.inl v'.2).lc⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  ileft
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  iexact HA

/-- `refines_injr` (compatibility.v:41): right-injection compatibility. -/
theorem refines_injr {e e' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e e' B)
      ⊢@{IProp GF} refines ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inr] e) (Ectx.fill [EctxItem.inr] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inr] [EctxItem.inr]) $$ IH
  iintro %v %v' HB
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inr] v.1)
    (e2 := Ectx.fill [EctxItem.inr] v'.1)
    (v1 := ⟨.inr v.1, IsVal.inr v.2, (IsVal.inr v.2).lc⟩)
    (v2 := ⟨.inr v'.1, IsVal.inr v'.2, (IsVal.inr v'.2).lc⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  iright
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  iexact HB

/-- `refines_app` (compatibility.v:51): function application compatibility. -/
theorem refines_app {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e1 e1' (lrel_arr A B)) ⊢@{IProp GF}
      refines ⊤ e2 e2' A -∗
            refines ⊤ (Exp.app e1 e2) (Exp.app e1' e2') B := by
  show _ ⊢@{IProp GF} refines ⊤ e2 e2' A -∗
    refines ⊤ (Ectx.fill [EctxItem.appR e1] e2)
              (Ectx.fill [EctxItem.appR e1'] e2') B
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR e1] [EctxItem.appR e1']) $$ IH2
  iintro %v2 %v2' HA
  have hbR : Ectx.fill [EctxItem.appR e1'] v2'.1 = Ectx.fill [EctxItem.appL v2'] e1' := rfl
  rw [(show Ectx.fill [EctxItem.appR e1] v2.1 = Ectx.fill [EctxItem.appL v2] e1 from rfl), hbR]
  iapply (refines_bind [EctxItem.appL v2] [EctxItem.appL v2']) $$ IH1
  iintro %v1 %v1' #Hff
  ihave Hff' := lrel_arr_unfold_wand A B v1 v1' $$ Hff
  have hgR : Ectx.fill [EctxItem.appL v2'] v1'.1 = Exp.app v1'.1 v2'.1 := rfl
  rw [(show Ectx.fill [EctxItem.appL v2] v1.1 = Exp.app v1.1 v2.1 from rfl), hgR]
  iapply Hff' $$ %v2 %v2' HA

/-- `refines_seq` (compatibility.v:62): sequencing compatibility.
`(REL e1 << e1' : A) ∗ (REL e2 << e2' : B) ⊢ REL (e1; e2) << (e1'; e2') : B`.

**Port note**: Rocq's `e1 ;; e2 = (λ_. e2) e1` uses an anonymous binder, so
the body doesn't reference the bound variable. In Lean, `.lam e2`'s beta-step
gives `Exp.open' e2 v`, which equals `e2` only when e2 is locally closed.
We require `e2.IsLocallyClosed` and `e2'.IsLocallyClosed` as hypotheses. -/
theorem refines_seq (A : lrel rT GF) {e1 e2 e1' e2' : Exp rT} {B : lrel rT GF}
    (he2 : e2.IsLocallyClosed) (he2' : e2'.IsLocallyClosed) :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      refines ⊤ e2 e2' B -∗
        refines ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B := by
  show iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      refines ⊤ e2 e2' B -∗
        refines ⊤ (Ectx.fill [EctxItem.appR (.lam e2)] e1)
          (Ectx.fill [EctxItem.appR (.lam e2')] e1') B
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR (.lam e2)] [EctxItem.appR (.lam e2')]
    (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v %v' _HA
  rw [Ectx.fill_appR, Ectx.eq_fill_nil (Exp.app (.lam e2) v.1), Ectx.fill_appR]
  have hv_iv : IsVal v.1 := v.2
  iapply (refines_pure_l
    (e := .app (.lam e2) v.1) (e' := Exp.open' e2 v.1) (A := B)
    (n := 1) (φ := v.1.isValue ∧ (Exp.lam e2).IsLocallyClosed)
    (Hφ := ⟨⟨hv_iv⟩, by is_lc⟩))
  have hfill_empty : Ectx.fill [] (Exp.open' e2 v.1) = e2 := by
    show Exp.open' e2 v.1 = e2
    exact (show Exp.open' e2 v.1 = e2 from (Exp.open_lc 0 v.1 e2 he2).symm)
  rw [hfill_empty]
  inext
  rw [Ectx.eq_fill_nil (.app (.lam e2') v'.1)]
  have hv'_iv : IsVal v'.1 := v'.2
  iapply (refines_pure_r
    (e := .app (.lam e2') v'.1) (e' := Exp.open' e2' v'.1) (A := B)
    (n := 1) (φ := v'.1.isValue ∧ (Exp.lam e2').IsLocallyClosed)
    (Hφ := ⟨⟨hv'_iv⟩, by is_lc⟩))
  have hopen' : Exp.open' e2' v'.1 = e2' := (Exp.open_lc 0 v'.1 e2' he2').symm
  rw [(show Ectx.fill [] (Exp.open' e2' v'.1) = e2' from hopen')]
  iexact IH2

omit [ProbLangℝ rT] in
/-- Helper: build `(lrel_exists C).car v v'` from a closedness witness and the
existential body. Defeq via `lrel.mk` projection. -/
theorem lrel_exists_unfold (C : lrel rT GF → lrel rT GF) (v v' : Val rT) :
    iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      (∃ A : lrel rT GF, (C A).car v v'))
      ⊢@{IProp GF} (lrel_exists C).car v v' :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_nat).car v v' ⊢ ∃ n : Nat, v = #n ∧ v' = #n`. -/
theorem lrel_nat_unfold (v v' : Val rT) :
    (lrel_nat (GF := GF)).car v v'
      ⊢@{IProp GF} ∃ n : Nat,
        ⌜v.1 = pl(#(.int (n : Int))) ∧ v'.1 = pl(#(.int (n : Int)))⌝ :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_pos_nat).car v v' ⊢ ∃ n : Nat, 0 < n ∧ v = #n ∧ v' = #n`. -/
theorem lrel_pos_nat_unfold (v v' : Val rT) :
    (lrel_pos_nat (GF := GF)).car v v'
      ⊢@{IProp GF} ∃ n : Nat, ⌜0 < n ∧
        v.1 = pl(#(.int (n : Int))) ∧ v'.1 = pl(#(.int (n : Int)))⌝ :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_int).car v v' ⊢ ∃ n : Int, v = #n ∧ v' = #n`. -/
theorem lrel_int_unfold (v v' : Val rT) :
    (lrel_int (GF := GF)).car v v'
      ⊢@{IProp GF} ∃ n : Int,
        ⌜v.1 = pl(#(.int n)) ∧ v'.1 = pl(#(.int n))⌝ :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_prod A
  B).car v v' ⊢ ∃ a1 a2 b1 b2, v=(a1,b1) ∧ v'=(a2,b2) ∧ A a1 a2 ∧ B b1 b2`. -/
theorem lrel_prod_unfold (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_prod A B).car v v' ⊢@{IProp GF}
      ∃ (a1 a2 b1 b2 : Val rT),
        (⌜v.1 = .pair a1.1 b1.1⌝) ∗ (⌜v'.1 = .pair a2.1 b2.1⌝) ∗
        A a1 a2 ∗ B b1 b2 :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_sum A B).car v v' ⊢ ∃ w1 w2, ((inl form) ∨ (inr form))`. -/
theorem lrel_sum_unfold (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_sum A B).car v v' ⊢@{IProp GF}
      ∃ (w1 w2 : Val rT),
        ((⌜v.1 = .inl w1.1⌝) ∗ (⌜v'.1 = .inl w2.1⌝) ∗ A w1 w2)
        ∨
        ((⌜v.1 = .inr w1.1⌝) ∗ (⌜v'.1 = .inr w2.1⌝) ∗ B w1 w2) :=
  BIBase.Entails.rfl

omit [ProbLangℝ rT] in
/-- Helper: `(lrel_bool).car v v' ⊢ ∃ b : Bool, v=#b ∧ v'=#b`. -/
theorem lrel_bool_unfold (v v' : Val rT) :
    (lrel_bool (GF := GF)).car v v' ⊢@{IProp GF}
      ∃ b : Bool, ⌜v.1 = pl(#(.bool b)) ∧ v'.1 = pl(#(.bool b))⌝ :=
  BIBase.Entails.rfl

/-! ### Symmetric refines lemmas for pure-step constructors

These are bin_log_related-supporting helpers that step both sides via
`refines_pure_l/r` over the corresponding `PureExec_discrete` instance, then either
recurse on the projected component (`refines_fst`/`refines_snd`) or apply the
appropriate IH (`refines_case`/`refines_if`). -/

/-- `refines_fst`: if `e ≤ e' : A × B`, then `fst e ≤ fst e' : A`. -/
theorem refines_fst {e e' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e e' (lrel_prod A B))
      ⊢@{IProp GF} refines ⊤ (.fst e) (.fst e') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.fst] e) (Ectx.fill [EctxItem.fst] e') A
  iintro IH
  iapply (refines_bind [EctxItem.fst] [EctxItem.fst]) $$ IH
  iintro %v %v' Hprod
  icases lrel_prod_unfold A B v v' $$ Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, HB⟩
  rw [show Ectx.fill [EctxItem.fst] v.1 = Exp.fst v.1 from rfl,
      show Ectx.fill [EctxItem.fst] v'.1 = Exp.fst v'.1 from rfl,
      hv, hv']
  rw [Ectx.eq_fill_nil (Exp.fst (.pair a1.1 b1.1)), Ectx.eq_fill_nil (Exp.fst (.pair a2.1 b2.1))]
  have hφ1 : a1.1.isValue ∧ b1.1.isValue := ⟨a1.2.toIsValue, b1.2.toIsValue⟩
  have hφ2 : a2.1.isValue ∧ b2.1.isValue := ⟨a2.2.toIsValue, b2.2.toIsValue⟩
  iapply (refines_pure_l (e' := a1.1)
    (Hex := pureExec_fst_pair) hφ1)
  inext
  iapply (refines_pure_r (e' := a2.1)
    (Hex := pureExec_fst_pair) hφ2)
  iapply refines_ret (e1 := Ectx.fill [] a1.1) (e2 := Ectx.fill [] a2.1)
    (v1 := a1) (v2 := a2) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iexact HA

/-- `refines_case`: case-split compatibility. After binding e0, the value
is `inl w` or `inr w`; we step the case to `e1 w` or `e2 w` and apply IH. -/
theorem refines_case {e0 e1 e2 e0' e1' e2' : Exp rT} {A B C : lrel rT GF} :
    iprop(refines ⊤ e0 e0' (lrel_sum A B)) ⊢@{IProp GF}
      refines ⊤ e1 e1' (lrel_arr A C) -∗
        refines ⊤ e2 e2' (lrel_arr B C) -∗
        refines ⊤ (.case e0 e1 e2) (.case e0' e1' e2') C := by
  show _ ⊢@{IProp GF}
    refines ⊤ e1 e1' (lrel_arr A C) -∗
      refines ⊤ e2 e2' (lrel_arr B C) -∗
      refines ⊤ (Ectx.fill [EctxItem.case e1 e2] e0)
        (Ectx.fill [EctxItem.case e1' e2'] e0') C
  iintro IH0 IH1 IH2
  iapply (refines_bind [EctxItem.case e1 e2] [EctxItem.case e1' e2']
    (A := lrel_sum A B)) $$ [IH0]
  · iexact IH0
  iintro %v %v' Hsum
  icases lrel_sum_unfold A B v v' $$ Hsum with ⟨%w1, %w2, HOr⟩
  rw [show Ectx.fill [EctxItem.case e1 e2] v.1 = Exp.case v.1 e1 e2 from rfl,
      show Ectx.fill [EctxItem.case e1' e2'] v'.1 = Exp.case v'.1 e1' e2' from rfl]
  icases HOr with (⟨%hv, %hv', HA⟩ | ⟨%hv, %hv', HB⟩)
  · rw [hv, hv']
    rw [Ectx.eq_fill_nil (Exp.case (.inl w1.1) e1 e2),
        Ectx.eq_fill_nil (Exp.case (.inl w2.1) e1' e2')]
    iapply (refines_pure_l (Hex := pureExec_case_inl) w1.2.toIsValue)
    inext
    iapply (refines_pure_r (Hex := pureExec_case_inl) w2.2.toIsValue)
    rw [show Ectx.fill [] (Exp.app e1 w1.1) = Exp.app e1 w1.1 from rfl,
        show Ectx.fill [] (Exp.app e1' w2.1) = Exp.app e1' w2.1 from rfl]
    iapply refines_app $$ IH1
    iapply refines_ret (e1 := w1.1) (e2 := w2.1) (v1 := w1) (v2 := w2)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HA
  · rw [hv, hv']
    rw [Ectx.eq_fill_nil (Exp.case (.inr w1.1) e1 e2),
        Ectx.eq_fill_nil (Exp.case (.inr w2.1) e1' e2')]
    iapply (refines_pure_l (Hex := pureExec_case_inr) w1.2.toIsValue)
    inext
    iapply (refines_pure_r (Hex := pureExec_case_inr) w2.2.toIsValue)
    rw [show Ectx.fill [] (Exp.app e2 w1.1) = Exp.app e2 w1.1 from rfl,
        show Ectx.fill [] (Exp.app e2' w2.1) = Exp.app e2' w2.1 from rfl]
    iapply refines_app $$ IH2
    iapply refines_ret (e1 := w1.1) (e2 := w2.1) (v1 := w1) (v2 := w2)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HB


/-- `refines_binop_pure`: helper for binop compatibility when `op.eval` on
literal values gives a deterministic result. Steps both sides via PureExec_discrete
on `binop op v1 v2 → r`, then concludes via `refines_ret` with `r` in the
provided result relation `Hres : Aresult r r`. -/
theorem refines_binop_pure (op : BinOp) (v1 v2 r : Exp rT)
    (hv1 : IsVal v1) (hv2 : IsVal v2) (hrv : IsVal r)
    (heval : op.eval v1 v2 = some r) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢@{IProp GF} refines ⊤ (.binop op v1 v2) (.binop op v1 v2) A := by
  rw [Ectx.eq_fill_nil (Exp.binop op v1 v2)]
  have hφ : v1.isValue ∧ v2.isValue ∧ op.eval v1 v2 = some r :=
    ⟨hv1.toIsValue, hv2.toIsValue, heval⟩
  iapply (refines_pure_l hφ)
  inext
  iapply (refines_pure_r hφ)
  iapply refines_ret (e1 := Ectx.fill [] r) (e2 := Ectx.fill [] r)
    (v1 := ⟨r, hrv, hrv.lc⟩) (v2 := ⟨r, hrv, hrv.lc⟩) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply HA

/-- Unary counterpart of `refines_binop_pure`: both sides hold the same value
`v`, the operation evaluates to the same `r`, so one pure step on each side
lands in `A r r`. -/
theorem refines_unop_pure (op : UnOp) (v r : Exp rT)
    (hv : IsVal v) (hrv : IsVal r)
    (heval : op.eval v = some r) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢@{IProp GF} refines ⊤ (.unop op v) (.unop op v) A := by
  rw [Ectx.eq_fill_nil (Exp.unop op v)]
  have hφ : v.isValue ∧ op.eval v = some r := ⟨hv.toIsValue, heval⟩
  iapply (refines_pure_l hφ)
  inext
  iapply (refines_pure_r hφ)
  iapply refines_ret (e1 := Ectx.fill [] r) (e2 := Ectx.fill [] r)
    (v1 := ⟨r, hrv, hrv.lc⟩) (v2 := ⟨r, hrv, hrv.lc⟩) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply HA

/-! ### Discrete fragment: tape allocation and bounded sampling -/


/-- `refines_alloctape`: tape-allocation compatibility. After binding the
bound argument to value `n : Int`, allocate fresh tapes on both sides and
establish the `lrel_tape` invariant. -/
theorem refines_alloctape {e e' : Exp rT} :
    iprop(refines ⊤ e e' lrel_int)
      ⊢@{IProp GF} refines ⊤ (.tape e) (.tape e') lrel_tape := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.tape] e) (Ectx.fill [EctxItem.tape] e') lrel_tape
  iintro IH
  iapply (refines_bind [EctxItem.tape] [EctxItem.tape]) $$ IH
  iintro %v %v' Hint
  icases lrel_int_unfold v v' $$ Hint with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.tape] v.1 = Exp.tape v.1 from rfl,
      show Ectx.fill [EctxItem.tape] v'.1 = Exp.tape v'.1 from rfl,
      hv, hv']
  unfold refines
  iintro %K %ε Hj Hna Herr Hpos
  ihave HStep := step_alloctape K n $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨%l', HKRes, Hl'frag⟩
  iapply specUpdate_ret
  iapply (wp_lift_atomic_head_step
    (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w))
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.TapeS rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    imod app_state_tape_alloc (σ := σ₁) (Tape.empty n) $$ Hσ with ⟨Hσ', Hlfrag⟩
    set lL := σ₁.tapes.fresh
    have htape_eq : Tape.empty n = (⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n })⟩ : Tape) := rfl
    ihave HlfragV : iprop(appTapesFrag lL ⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n
      })⟩) $$ [Hlfrag]
    · rw [← htape_eq]; iexact Hlfrag
    ihave Hl'fragV : iprop(specTapesFrag l' ⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n
      })⟩) $$ [Hl'frag]
    · rw [← htape_eq]; iexact Hl'frag
    ihave HInvBody : iprop(▷ ((appTapesFrag lL ⟨n, []⟩) ∗
        (specTapesFrag l' ⟨n, []⟩))) $$ [HlfragV Hl'fragV]
    · iintro !>
      iframe HlfragV
      iexact Hl'fragV
    imod (Iris.inv_alloc
      (P := iprop((appTapesFrag lL ⟨n, []⟩) ∗ (specTapesFrag l' ⟨n, []⟩)))) $$ [HInvBody] with #HInv
    · iexact HInvBody
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iexists (.lbl l' : Val _)
    iexists ε
    iframe HKRes Hna Herr Hpos
    unfold lrel_tape
    iexists lL, l', n
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iexact HInv

/-- `refines_alloc`: alloc compatibility. After binding `e/e'` to value pair
related at `A`, alloc fresh refs on both sides and establish the invariant. -/
theorem refines_alloc {e e' : Exp rT} {A : lrel rT GF} :
    iprop(refines ⊤ e e' A)
      ⊢@{IProp GF} refines ⊤ (.alloc e) (.alloc e') (lrel_ref A) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.alloc] e) (Ectx.fill [EctxItem.alloc] e') (lrel_ref A)
  iintro IH
  iapply (refines_bind [EctxItem.alloc] [EctxItem.alloc]) $$ IH
  iintro %v %v' #HA
  rw [show Ectx.fill [EctxItem.alloc] v.1 = Exp.alloc v.1 from rfl,
      show Ectx.fill [EctxItem.alloc] v'.1 = Exp.alloc v'.1 from rfl]
  rw [Ectx.eq_fill_nil (Exp.alloc v.1), Ectx.eq_fill_nil (Exp.alloc v'.1)]
  iapply refines_alloc_r
  iintro %l' Hl'
  iapply refines_alloc_l
  iintro %l Hl
  ihave HInvBody : iprop(▷ ∃ (w1 w2 : Val rT),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2) $$ [Hl Hl' HA]
  · iintro !>
    iexists v, v'
    iframe Hl Hl'
    iexact HA
  imod (Iris.inv_alloc (E := ⊤)
    (P := iprop(∃ (w1 w2 : Val rT),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2))) $$ [HInvBody] with #HInv
  · iexact HInvBody
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.loc l)))
    (e2 := Ectx.fill [] pl(#(.loc l')))
    (v1 := .loc l) (v2 := .loc l')
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_ref
  iexists l, l'
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  iexact HInv

/-- `refines_if`: if-then-else compatibility. -/
theorem refines_if {e0 e1 e2 e0' e1' e2' : Exp rT} {A : lrel rT GF} :
    iprop(refines ⊤ e0 e0' lrel_bool) ⊢@{IProp GF}
      refines ⊤ e1 e1' A -∗ refines ⊤ e2 e2' A -∗
        refines ⊤ (.cond e0 e1 e2) (.cond e0' e1' e2') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ e1 e1' A -∗ refines ⊤ e2 e2' A -∗
      refines ⊤ (Ectx.fill [EctxItem.condC e1 e2] e0)
        (Ectx.fill [EctxItem.condC e1' e2'] e0') A
  iintro IH0 IH1 IH2
  iapply (refines_bind [EctxItem.condC e1 e2] [EctxItem.condC e1' e2']) $$ IH0
  iintro %v %v' Hb
  ihave Hb' := lrel_bool_unfold v v' $$ Hb
  icases Hb' with ⟨%b, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.condC e1 e2] v.1 = Exp.cond v.1 e1 e2 from rfl,
      show Ectx.fill [EctxItem.condC e1' e2'] v'.1 = Exp.cond v'.1 e1' e2' from rfl,
      hv, hv']
  cases b with
  | true =>
    rw [Ectx.eq_fill_nil (Exp.cond pl(#(.bool true)) e1 e2),
        Ectx.eq_fill_nil (Exp.cond pl(#(.bool true)) e1' e2')]
    iapply (refines_pure_l (Hex := pureExec_cond_true) trivial)
    inext
    iapply (refines_pure_r (Hex := pureExec_cond_true) trivial)
    rw [show Ectx.fill [] e1 = e1 from rfl, show Ectx.fill [] e1' = e1' from rfl]
    iexact IH1
  | false =>
    rw [Ectx.eq_fill_nil (Exp.cond pl(#(.bool false)) e1 e2),
        Ectx.eq_fill_nil (Exp.cond pl(#(.bool false)) e1' e2')]
    iapply (refines_pure_l (Hex := pureExec_cond_false) trivial)
    inext
    iapply (refines_pure_r (Hex := pureExec_cond_false) trivial)
    rw [show Ectx.fill [] e2 = e2 from rfl, show Ectx.fill [] e2' = e2' from rfl]
    iexact IH2

/-- `refines_snd`: if `e ≤ e' : A × B`, then `snd e ≤ snd e' : B`. -/
theorem refines_snd {e e' : Exp rT} {A B : lrel rT GF} :
    iprop(refines ⊤ e e' (lrel_prod A B))
      ⊢@{IProp GF} refines ⊤ (.snd e) (.snd e') B := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.snd] e) (Ectx.fill [EctxItem.snd] e') B
  iintro IH
  iapply (refines_bind [EctxItem.snd] [EctxItem.snd]) $$ IH
  iintro %v %v' Hprod
  icases lrel_prod_unfold A B v v' $$ Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, HB⟩
  rw [show Ectx.fill [EctxItem.snd] v.1 = Exp.snd v.1 from rfl,
      show Ectx.fill [EctxItem.snd] v'.1 = Exp.snd v'.1 from rfl,
      hv, hv']
  rw [Ectx.eq_fill_nil (Exp.snd (.pair a1.1 b1.1)), Ectx.eq_fill_nil (Exp.snd (.pair a2.1 b2.1))]
  have hφ1 : a1.1.isValue ∧ b1.1.isValue := ⟨a1.2.toIsValue, b1.2.toIsValue⟩
  have hφ2 : a2.1.isValue ∧ b2.1.isValue := ⟨a2.2.toIsValue, b2.2.toIsValue⟩
  iapply (refines_pure_l (e' := b1.1)
    (Hex := pureExec_snd_pair) hφ1)
  inext
  iapply (refines_pure_r (e' := b2.1)
    (Hex := pureExec_snd_pair) hφ2)
  iapply refines_ret (e1 := Ectx.fill [] b1.1) (e2 := Ectx.fill [] b2.1)
    (v1 := b1) (v2 := b2) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iexact HB

/-- Helper: `(lrel_tape).car v v'` exposes the tape locations and bound. -/
theorem lrel_tape_unfold (v v' : Val rT) :
    (lrel_tape (GF := GF)).car v v' ⊢@{IProp GF}
      ∃ (α1 α2 : Loc) (z : Int),
        (⌜ v.1 = pl(#(.lbl α1)) ⌝) ∗ (⌜ v'.1 = pl(#(.lbl α2)) ⌝) ∗
        Iris.inv (logN.@ ((α1, α2) : Loc × Loc))
          (iprop((appTapesFrag α1 ⟨z, []⟩) ∗ (specTapesFrag α2 ⟨z, []⟩))) :=
  BIBase.Entails.rfl

/-- `refines_pack` (compatibility.v:73): existential-packing compatibility.
Given `REL e << e' : C A` for a specific `A`, conclude `REL e << e' : ∃ A, C A`.
Requires a proof that `C A` only relates closed values (port-specific). -/
theorem refines_pack (A : lrel rT GF) {e e' : Exp rT} {C : lrel rT GF → lrel rT GF}
    (_hC : OFE.NonExpansive C)
    (hCclosed : ∀ v v' : Val rT, (C A).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝)) :
    refines (⊤ : CoPset) e e' (C A)
      ⊢@{IProp GF} refines ⊤ e e' (lrel_exists C) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill Ectx.empty e) (Ectx.fill Ectx.empty e') (lrel_exists C)
  iintro IH
  iapply (refines_bind Ectx.empty Ectx.empty) $$ IH
  iintro %v %v' HCA
  iapply refines_ret
    (e1 := Ectx.fill Ectx.empty v.1) (e2 := Ectx.fill Ectx.empty v'.1)
    (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  ihave %Hcl : iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ : IProp GF) $$ [HCA]
  · iapply (hCclosed v v'); iexact HCA
  iapply lrel_exists_unfold
  isplitr
  · ipureintro; exact Hcl
  iexists A
  iexact HCA

/-- `refines_forall` (compatibility.v:83): universal-typing compatibility.
If for all semantic types `A`, `REL e << e' : C A`, then `(λ_. e) << (λ_. e') : ∀A, C A`.

Two pure beta steps over the value-restricted forall encoding (via
`refines_pure_l`/`refines_pure_r`), then apply the persistent IH at the chosen
semantic type `A`.

**Port note**: same `IsLocallyClosed` requirement as `refines_seq`. -/
theorem refines_forall {e e' : Exp rT} {C : lrel rT GF → lrel rT GF}
    (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed)
    (he_fv : e.fv = ∅) (he'_fv : e'.fv = ∅) :
    BI.intuitionistically (BI.forall (fun A : lrel rT GF => refines (⊤ : CoPset) e e' (C A)))
      ⊢@{IProp GF} refines ⊤ (.lam e) (.lam e') (lrel_forall C) := by
  iintro #H
  iapply (refines_ret
    (v1 := ⟨.lam e, IsVal.lam (by is_lc), by is_lc⟩)
    (v2 := ⟨.lam e', IsVal.lam (by is_lc), by is_lc⟩) (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_forall
  iintro %A
  unfold lrel_arr
  isplitr
  · ipureintro
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact Exp.IsLocallyClosed.lam ∅ e (fun y _ => by
        show (e.open' (Exp.fvar y)).IsLocallyClosed
        have : e.open' (Exp.fvar y) = e := (Exp.open_lc 0 (Exp.fvar y) e he).symm
        rw [this]; exact he)
    · simp [Exp.fv]; exact he_fv
    · exact Exp.IsLocallyClosed.lam ∅ e' (fun y _ => by
        show (e'.open' (Exp.fvar y)).IsLocallyClosed
        have : e'.open' (Exp.fvar y) = e' := (Exp.open_lc 0 (Exp.fvar y) e' he').symm
        rw [this]; exact he')
    · simp [Exp.fv]; exact he'_fv
  iintro !> %u %u' Hunit
  rw [Ectx.eq_fill_nil (Exp.app (.lam e) u.1)]
  have hu_iv : IsVal u.1 := u.2
  iapply (refines_pure_l
    (e := .app (.lam e) u.1) (e' := Exp.open' e u.1) (A := C A)
    (n := 1) (φ := u.1.isValue ∧ (Exp.lam e).IsLocallyClosed)
    (Hφ := ⟨⟨hu_iv⟩, by is_lc⟩))
  have hopenL : Exp.open' e u.1 = e := (Exp.open_lc 0 u.1 e he).symm
  rw [(show Ectx.fill [] (Exp.open' e u.1) = e from hopenL)]
  inext
  rw [Ectx.eq_fill_nil (Exp.app (.lam e') u'.1)]
  have hu'_iv : IsVal u'.1 := u'.2
  iapply (refines_pure_r
    (e := .app (.lam e') u'.1) (e' := Exp.open' e' u'.1) (A := C A)
    (n := 1) (φ := u'.1.isValue ∧ (Exp.lam e').IsLocallyClosed)
    (Hφ := ⟨⟨hu'_iv⟩, by is_lc⟩))
  have hopenR : Exp.open' e' u'.1 = e' := (Exp.open_lc 0 u'.1 e' he').symm
  rw [(show Ectx.fill [] (Exp.open' e' u'.1) = e' from hopenR)]
  iapply H

/-- Helper: introduce a step-fupd from a `▷ P` with mask shift (E2 ⊆ E1).

Standard Iris `step_fupd_intro`. Construction:
- Use `fupd_mask_intro`: `((|={E2,E1}=> emp) -∗ Q) ⊢ |={E1, E2}=> Q`.
- Set Q := `▷ |={E2, E1}=> P`.
- Provide the wand: given `Hclose : |={E2,E1}=> emp`, produce `▷ |={E2,E1}=> P`.
  Lift Hclose under ▷ via `BI.later_intro`, combine with `▷ P`, mono fupd to drop emp. -/
theorem step_fupd_intro_later {E1 E2 : CoPset} {P : IProp GF} (HE : E2 ⊆ E1) :
    iprop(▷ P) ⊢@{IProp GF} |={E1, E2}=> ▷ |={E2, E1}=> P := by
  iintro HP
  iapply Iris.fupd_mask_intro HE
  iintro Hclose
  iintro !>
  imod Hclose
  imodintro
  iexact HP

/-- Helper: `(lrel_ref A).car v v'` exposes the existence of related locations
plus the heap invariant. -/
theorem lrel_ref_unfold (A : lrel rT GF) (v v' : Val rT) :
    (lrel_ref A).car v v' ⊢@{IProp GF}
      ∃ (l l' : Loc),
        (⌜ v.1 = pl(#(.loc l)) ⌝) ∗ (⌜ v'.1 = pl(#(.loc l')) ⌝) ∗
        Iris.inv (logN.@ ((l, l') : Loc × Loc))
          (iprop(∃ (w1 w2 : Val rT),
            (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) :=
  BIBase.Entails.rfl

/-- `refines_store` (compatibility.v:95): store compatibility.
Stores to related references preserve the refinement.

Same structure as `refines_load`: refines_bind on e2 then e1, destructure
`lrel_ref A` to get `(l, l', inv ...)`, refines_atomic_l, open inv,
step_store + wp_store, close inv with the NEW values. -/
theorem refines_store {e1 e2 e1' e2' : Exp rT} {A : lrel rT GF} :
    iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      refines ⊤ e2 e2' A -∗
        refines ⊤ (.store e1 e2) (.store e1' e2') lrel_unit := by
  show iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      refines ⊤ e2 e2' A -∗
        refines ⊤ (Ectx.fill [EctxItem.storeR e1] e2)
          (Ectx.fill [EctxItem.storeR e1'] e2') lrel_unit
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.storeR e1] [EctxItem.storeR e1']) $$ IH2
  iintro %w %w' #HwA
  have hfillR : Ectx.fill [EctxItem.storeR e1] w.1 = Ectx.fill [EctxItem.storeL w] e1 := rfl
  have hfillR' : Ectx.fill [EctxItem.storeR e1'] w'.1 = Ectx.fill [EctxItem.storeL w'] e1' := rfl
  rw [hfillR, hfillR']
  iapply (refines_bind [EctxItem.storeL w] [EctxItem.storeL w']) $$ IH1
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv' : Ectx.fill [EctxItem.storeL w'] v'.1 = Exp.store v'.1 w'.1 := rfl
  rw [(show Ectx.fill [EctxItem.storeL w] v.1 = Exp.store v.1 w.1 from rfl), hfillv', heq, heq']
  rw [Ectx.eq_fill_nil (Exp.store pl(#(.loc l)) w.1)]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := Exp.store pl(#(.loc l)) w.1)
    (t := Exp.store pl(#(.loc l')) w'.1)
    (A := lrel_unit) (OpenInv.of_atomic (Atomic.store' l w)))
  iintro %K' Hr
  iinv Hinv with ⟨%v1, %v2, >Hv1, >Hv2, -⟩ Hclose
  imodintro
  ihave HStep := step_store
    (E := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) K' (l := l') (v_old := v2) (v_new := w')
    (hv := w'.2) (hnew := Exp.toVal?_ofVal w') $$ [$Hr $Hv2]
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨HKRes, Hv2'⟩
  iapply specUpdate_ret
  have hstoreL : Exp.store pl(#(.loc l)) w.1 =
    Exp.store pl(#(.loc l)) (Exp.ofVal w) := rfl
  rw [hstoreL]
  iapply (wp_store (v' := v1))
  iframe Hv1
  iintro Hw1'
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val rT),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hv2' HwA]
  · iintro !>
    iexists w, w'
    iframe Hw1' Hv2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with -
  imodintro
  iexists pl(#(.unit))
  iframe HKRes
  iapply (refines_ret (e1 := Ectx.fill [] pl(#(.unit))) (e2 := pl(#(.unit)))
    (v1 := .unit) (v2 := .unit)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_unit
  ipureintro
  exact ⟨rfl, rfl⟩

/-- `refines_load` (compatibility.v:118): dereference compatibility.
Loading through related references yields related values.

Mirrors Rocq's proof: `refines_bind` to focus on the values, destructure
`lrel_ref A` to get `(l, l', inv ...)`, apply `refines_atomic_l`, open the
invariant, RHS-step via `step_load`, LHS-step via `wp_load`, close the
invariant, produce the value post.

Uses `ApproxisWpGS.wp_step_fupd` (AppWeakestpre.lean:2048) to absorb the `▷ A.car w1 w2`
witness from the inv-open through `wp_load`'s atomic step. -/
theorem refines_load {e e' : Exp rT} {A : lrel rT GF} :
    iprop(refines ⊤ e e' (lrel_ref A))
      ⊢@{IProp GF} refines ⊤ (.load e) (.load e') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.load] e) (Ectx.fill [EctxItem.load] e') A
  iintro IH
  iapply (refines_bind [EctxItem.load] [EctxItem.load]) $$ IH
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv' : Ectx.fill [EctxItem.load] v'.1 = Exp.load v'.1 := rfl
  rw [(show Ectx.fill [EctxItem.load] v.1 = Exp.load v.1 from rfl), hfillv', heq, heq']
  rw [(show (pl(!#(.loc l)) : Exp rT) = Ectx.fill [] pl(!#(.loc l)) from rfl)]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := (pl(!#(.loc l)) : Exp rT))
    (t := (pl(!#(.loc l')) : Exp rT))
    (A := A) (OpenInv.of_atomic (Atomic.load' l)))
  iintro %K' Hr
  iinv Hinv with ⟨%w1, %w2, >Hw1, >Hw2, #HwAL⟩ Hclose
  imodintro
  ihave HStep := step_load K' $$ [$Hr $Hw2]
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨HKRes, Hw2'⟩
  iapply specUpdate_ret
  have HE : (∅ : CoPset) ⊆ (⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) :=
    Std.LawfulSet.empty_subset
  have hv : ((pl(!#(.loc l)) : Exp rT)).toVal? = none := Exp.load_toVal?_eq_none
  iapply (ApproxisWpGS.wp_step_fupd
    (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅) HE hv)
  isplitl [HwAL]
  · ihave Hgoal := step_fupd_intro_later
      (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅)
      (P := A.car w1 w2) HE $$ HwAL
    iexact Hgoal
  iapply wp_load
  iframe Hw1
  iintro Hw1'
  iintro #HwA
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val rT),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hw2' HwA]
  · iintro !>
    iexists w1, w2
    iframe Hw1' Hw2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with -
  imodintro
  iexists (Exp.ofVal w2)
  iframe HKRes
  iapply (refines_ret (e1 := Ectx.fill [] w1.1) (e2 := Exp.ofVal w2)
    (v1 := w1) (v2 := w2) (hv1 := rfl) (hv2 := rfl))
  imodintro
  iexact HwA

/-- `refines_rand_tape` (compatibility.v:139): labeled-rand compatibility.
Both sides sample from related tapes, at related bounds.

Mirrors Rocq's proof: bind e2/e2' (tape locations α, α', bound N with inv),
bind e1/e1' (nat value M), refines_atomic_l at `.rand #M (lbl α)`, open
the tape invariant, case-split `N = M` or `N ≠ M`, apply the corresponding
`wp_couple_rand_lbl_rand_lbl`{,_wrong} rule.

**Port note**: positivity is required for the uniform-sample coupling
rule (`wp_couple_rand_lbl_rand_lbl{,_wrong}` take `0 < M`), so we take
the bound at `lrel_pos_nat`. Under the current operational semantics,
`rand M (lbl α)` for `M ≤ 0` returns the sentinel `-1` deterministically
(it is no longer stuck), so a `lrel_int`-bounded variant is provable
via degenerate dirac-dirac coupling on the nonpos branch — not done
here since callers already have positivity in practice. -/
theorem refines_rand_tape {e1 e1' e2 e2' : Exp rT} :
    iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
      refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat := by
  show iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
    refines ⊤ e2 e2' lrel_tape -∗
      refines ⊤ (Ectx.fill [EctxItem.randR e1] e2)
                (Ectx.fill [EctxItem.randR e1'] e2') lrel_nat
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.randR e1] [EctxItem.randR e1']
    (A := lrel_tape)) $$ [IH2]
  · iexact IH2
  iintro %w %w' HTapeRel
  icases lrel_tape_unfold _ _ $$ HTapeRel with ⟨%α, %α', %N, %Hw, %Hw', #Hinv⟩
  have hfillR_to_L : Ectx.fill [EctxItem.randR e1] w.1 =
    Ectx.fill [EctxItem.randL w] e1 := rfl
  have hfillR_to_L' : Ectx.fill [EctxItem.randR e1'] w'.1 =
    Ectx.fill [EctxItem.randL w'] e1' := rfl
  rw [hfillR_to_L, hfillR_to_L']
  iapply (refines_bind [EctxItem.randL w] [EctxItem.randL w']
    (A := lrel_pos_nat)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HPosNat
  icases lrel_pos_nat_unfold v v' $$ HPosNat with ⟨%M, %hM_pos, %HvM, %Hv'M⟩
  have hfillv : Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 := rfl
  rw [hfillv, hfillv', HvM, Hv'M, Hw, Hw']
  have hfill_empty : (Exp.rand (pl(#(.int (M : Int)))) pl(#(.lbl α)) : Exp rT) =
    Ectx.fill [] (Exp.rand (pl(#(.int (M : Int)))) pl(#(.lbl α))) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
    (K := []) (e1 := (Exp.rand (pl(#(.int (M : Int)))) pl(#(.lbl α)) : Exp rT))
    (t := (Exp.rand (pl(#(.int (M : Int)))) pl(#(.lbl α')) : Exp rT))
    (A := lrel_nat) (OpenInv.of_atomic (Atomic.rand_lbl' (M : Int) α)))
  iintro %K' Hr
  iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
  imodintro
  ihave HαN := app_empty_to_natTape (z := N) $$ Hα
  ihave Hα'N := spec_empty_to_natTape (z := N) $$ Hα'
  by_cases hNM : N = (M : Int)
  · subst hNM
    have hMpos : (0 : Int) < (M : Int) := by exact_mod_cast hM_pos
    iapply (wp_couple_rand_lbl_rand_lbl (M : Int) id
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hMpos) (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (α := α) (α' := α'))
    isplitl [HαN]
    · iintro !>; iexact HαN
    isplitl [Hα'N]
    · iintro !>; iexact Hα'N
    iframe Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    ihave HαBack := app_natTape_to_empty $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨(M : Int), []⟩ ∗
        specTapesFrag α' ⟨(M : Int), []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      iframe HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with -
    imodintro
    iexists (pl(#(.int (id n))))
    iframe HKRes
    iapply (refines_ret (e1 := Ectx.fill [] pl(#(.int n)))
      (e2 := pl(#(.int (id n))))
      (v1 := .int n) (v2 := .int (id n))
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipureintro
    have hk : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn0
    refine ⟨?_, ?_⟩ <;> rw [hk]
    · rfl
  · have hMpos : (0 : Int) < (M : Int) := by exact_mod_cast hM_pos
    iapply (wp_couple_rand_lbl_rand_lbl_wrong (M : Int) N id
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hMpos) (HneM := fun heq => hNM heq.symm)
      (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (α := α) (α' := α') (xs := []) (ys := []))
    isplitl [HαN]
    · iintro !>; iexact HαN
    isplitl [Hα'N]
    · iintro !>; iexact Hα'N
    iframe Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
        specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      iframe HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with -
    imodintro
    iexists (pl(#(.int (id n))))
    iframe HKRes
    iapply (refines_ret (e1 := Ectx.fill [] pl(#(.int n)))
      (e2 := pl(#(.int (id n))))
      (v1 := .int n) (v2 := .int (id n))
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipureintro
    have hk : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn0
    refine ⟨?_, ?_⟩ <;> rw [hk]
    · rfl

/-- `refines_rand_unit` (compatibility.v:175): unlabeled-rand compatibility.
Couples unlabeled rand calls at related bounds using `refines_couple_rands_lr`.

**Port note**: positivity is required for the uniform-sample coupling
(`refines_couple_rands_lr` takes `0 < z`), so we take the bound at
`lrel_pos_nat`. Under the current operational semantics, `rand n ()`
for `n ≤ 0` returns the sentinel `-1` deterministically (it is no
longer stuck), so a `lrel_int`-bounded variant is provable via a
degenerate dirac-dirac coupling on the nonpos branch — not done here
since callers already have positivity in practice. Conclusion stays at
`lrel_nat` since the positive-bound result is in `[0, n)`. -/
theorem refines_rand_unit {e e' : Exp rT} :
    iprop(refines ⊤ e e' lrel_pos_nat)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL (.unit : Val _)] e)
          (Ectx.fill [EctxItem.randL (.unit : Val _)] e')
          lrel_nat := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL (.unit : Val _)]
    [EctxItem.randL (.unit : Val _)]
    (A := lrel_pos_nat)) $$ [IH]
  · iexact IH
  iintro %v %v' HPosNat
  icases lrel_pos_nat_unfold v v' $$ HPosNat with ⟨%n, %hn_pos, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL (.unit : Val _)] v.1 =
      Exp.rand v.1 pl(#(.unit)) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL (.unit : Val _)] v'.1 =
      Exp.rand v'.1 pl(#(.unit)) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  · have hnpos : (0 : Int) < (n : Int) := by exact_mod_cast hn_pos
    have hfill_emp : (Exp.rand (pl(#(.int (n : Int)))) pl(#(.unit)) : Exp rT) =
      Ectx.fill [] (Exp.rand (pl(#(.int (n : Int)))) pl(#(.unit))) := rfl
    rw [hfill_emp]
    iapply (refines_couple_rands_lr (K' := []) (A := lrel_nat)
      (z := (n : Int)) (f := id)
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hnpos))
    iintro %m ⟨%Hm0, %Hmn⟩
    have hfill2 : (Ectx.fill [] (pl(#(.int (id m)))) : Exp rT) = pl(#(.int m)) := rfl
    rw [(show (Ectx.fill [] pl(#(.int m)) : Exp rT) = pl(#(.int m)) from rfl), hfill2]
    iapply (refines_ret (e1 := pl(#(.int m))) (e2 := pl(#(.int m)))
      (v1 := .int m) (v2 := .int m)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    iexists m.toNat
    ipureintro
    refine ⟨?_, ?_⟩ <;> rw [(show (m.toNat : Int) = m from Int.toNat_of_nonneg Hm0)]

/-- `refines_rand_tape_int`: int-flavored labeled-rand compatibility. Takes
the bound at `lrel_int` (any integer) and concludes at `lrel_int`.
Case-splits on `0 < n`: positive uses the existing `wp_couple_rand_lbl_rand_lbl{,_wrong}`
flow; nonpos opens the tape invariant and uses `wp_rand_lbl_nonpos{,_r}`. -/
theorem refines_rand_tape_int {e1 e1' e2 e2' : Exp rT} :
    iprop(refines ⊤ e1 e1' lrel_int) ⊢@{IProp GF}
      refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_int := by
  show iprop(refines ⊤ e1 e1' lrel_int) ⊢@{IProp GF}
    refines ⊤ e2 e2' lrel_tape -∗
      refines ⊤ (Ectx.fill [EctxItem.randR e1] e2)
                (Ectx.fill [EctxItem.randR e1'] e2') lrel_int
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.randR e1] [EctxItem.randR e1']
    (A := lrel_tape)) $$ [IH2]
  · iexact IH2
  iintro %w %w' HTapeRel
  icases lrel_tape_unfold _ _ $$ HTapeRel with ⟨%α, %α', %N, %Hw, %Hw', #Hinv⟩
  have hfillR_to_L : Ectx.fill [EctxItem.randR e1] w.1 =
    Ectx.fill [EctxItem.randL w] e1 := rfl
  have hfillR_to_L' : Ectx.fill [EctxItem.randR e1'] w'.1 =
    Ectx.fill [EctxItem.randL w'] e1' := rfl
  rw [hfillR_to_L, hfillR_to_L']
  iapply (refines_bind [EctxItem.randL w] [EctxItem.randL w']
    (A := lrel_int)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HInt
  icases lrel_int_unfold v v' $$ HInt with ⟨%n, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 := rfl
  rw [hfillv, hfillv', Hv, Hv', Hw, Hw']
  by_cases hnpos : 0 < n
  · -- Positive bound: same proof as refines_rand_tape, parameterized over lrel_int.
    have hfill_empty : (pl(rand(#(.int n), #(.lbl α))) : Exp rT) =
      Ectx.fill [] (pl(rand(#(.int n), #(.lbl α)))) := rfl
    rw [hfill_empty]
    iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (K := []) (e1 := (pl(rand(#(.int n), #(.lbl α))) : Exp rT))
      (t := (pl(rand(#(.int n), #(.lbl α'))) : Exp rT))
      (A := lrel_int) (OpenInv.of_atomic (Atomic.rand_lbl' n α)))
    iintro %K' Hr
    iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
    imodintro
    ihave HαN := app_empty_to_natTape $$ Hα
    ihave Hα'N := spec_empty_to_natTape $$ Hα'
    by_cases hNM : N = n
    · subst hNM
      iapply (wp_couple_rand_lbl_rand_lbl N id
        (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
        (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
        (Hz := hnpos) (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
        (α := α) (α' := α'))
      isplitl [HαN]
      · iintro !>; iexact HαN
      isplitl [Hα'N]
      · iintro !>; iexact Hα'N
      iframe Hr
      iintro %m ⟨HαRet, Hα'Ret, HKRes, %Hmr⟩
      ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
      ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
      ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
          specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
      · iintro !>
        iframe HαBack
        iexact Hα'Back
      ispecialize Hclose $$ HCloseArg
      imod Hclose with -
      imodintro
      iexists (pl(#(.int (id m))))
      iframe HKRes
      iapply (refines_ret (e1 := Ectx.fill [] pl(#(.int m)))
        (e2 := pl(#(.int (id m))))
        (v1 := .int m) (v2 := .int (id m))
        (hv1 := rfl) (hv2 := rfl))
      imodintro
      unfold lrel_int
      iexists m
      ipureintro
      exact ⟨rfl, rfl⟩
    · iapply (wp_couple_rand_lbl_rand_lbl_wrong n N id
        (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
        (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
        (Hz := hnpos) (HneM := fun heq => hNM heq.symm)
        (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
        (α := α) (α' := α') (xs := []) (ys := []))
      isplitl [HαN]
      · iintro !>; iexact HαN
      isplitl [Hα'N]
      · iintro !>; iexact Hα'N
      iframe Hr
      iintro %m ⟨HαRet, Hα'Ret, HKRes, %Hmr⟩
      ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
      ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
      ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
          specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
      · iintro !>
        iframe HαBack
        iexact Hα'Back
      ispecialize Hclose $$ HCloseArg
      imod Hclose with -
      imodintro
      iexists (pl(#(.int (id m))))
      iframe HKRes
      iapply (refines_ret (e1 := Ectx.fill [] pl(#(.int m)))
        (e2 := pl(#(.int (id m))))
        (v1 := .int m) (v2 := .int (id m))
        (hv1 := rfl) (hv2 := rfl))
      imodintro
      unfold lrel_int
      iexists m
      ipureintro
      exact ⟨rfl, rfl⟩
  · -- Nonpositive bound: open invariant, both sides step deterministically to -1.
    have hfill_empty : (pl(rand(#(.int n), #(.lbl α))) : Exp rT) =
      Ectx.fill [] (pl(rand(#(.int n), #(.lbl α)))) := rfl
    rw [hfill_empty]
    iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (K := []) (e1 := (pl(rand(#(.int n), #(.lbl α))) : Exp rT))
      (t := (pl(rand(#(.int n), #(.lbl α'))) : Exp rT))
      (A := lrel_int) (OpenInv.of_atomic (Atomic.rand_lbl' n α)))
    iintro %K' Hr
    iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
    imodintro
    iapply (wp_rand_lbl_nonpos_r K' hnpos)
    iframe Hr Hα'
    iintro Hα'New HKRes
    iapply (wp_rand_lbl_nonpos hnpos)
    iframe Hα
    iintro HαNew
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
        specTapesFrag α' ⟨N, []⟩)) $$ [HαNew Hα'New]
    · iintro !>
      iframe HαNew
      iexact Hα'New
    ispecialize Hclose $$ HCloseArg
    imod Hclose with -
    imodintro
    iexists (pl(#(.int (-1))))
    iframe HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (pl(#(.int (-1)))))
      (e2 := pl(#(.int (-1))))
      (v1 := .int (-1)) (v2 := .int (-1))
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_int
    iexists (-1)
    ipureintro
    exact ⟨rfl, rfl⟩

/-- `refines_rand_unit_int`: int-flavored unit-rand compatibility. Takes the
bound at `lrel_int` (any integer) and concludes at `lrel_int`. Case-splits
on `0 < n`: positive lifts to `lrel_pos_nat`+`refines_rand_unit`+widening;
nonpos uses degenerate dirac-(-1) coupling via `wp_rand_nonpos`/`_r`. -/
theorem refines_rand_unit_int {e e' : Exp rT} :
    iprop(refines ⊤ e e' lrel_int)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL (.unit : Val _)] e)
          (Ectx.fill [EctxItem.randL (.unit : Val _)] e')
          lrel_int := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL (.unit : Val _)]
    [EctxItem.randL (.unit : Val _)]
    (A := lrel_int)) $$ [IH]
  · iexact IH
  iintro %v %v' HInt
  icases lrel_int_unfold v v' $$ HInt with ⟨%n, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL (.unit : Val _)] v.1 =
      Exp.rand v.1 pl(#(.unit)) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL (.unit : Val _)] v'.1 =
      Exp.rand v'.1 pl(#(.unit)) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  by_cases hnpos : 0 < n
  · have hfill_emp : (pl(rand(#(.int n), #(.unit))) : Exp rT) =
      Ectx.fill [] (pl(rand(#(.int n), #(.unit)))) := rfl
    rw [hfill_emp]
    iapply (refines_couple_rands_lr (K' := []) (A := lrel_int)
      (z := n) (f := id)
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hnpos))
    iintro %m _
    have hfill2 : (Ectx.fill [] (pl(#(.int (id m)))) : Exp rT) = pl(#(.int m)) := rfl
    rw [(show (Ectx.fill [] pl(#(.int m)) : Exp rT) = pl(#(.int m)) from rfl), hfill2]
    iapply (refines_ret (e1 := pl(#(.int m))) (e2 := pl(#(.int m)))
      (v1 := .int m) (v2 := .int m)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_int
    iexists m
    ipureintro
    exact ⟨rfl, rfl⟩
  · unfold refines
    iintro %K %ε HK Hna Herr Hpos
    iapply (wp_rand_nonpos_r K hnpos)
    iframe HK
    iintro HK'
    iapply (wp_rand_nonpos hnpos)
    iexists (.int (-1) : Val _)
    iexists ε
    iframe HK' Hna Herr Hpos
    unfold lrel_int
    iexists (-1)
    ipureintro
    exact ⟨rfl, rfl⟩

end Compatibility

end ProbLang
