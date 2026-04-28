import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.RelTactics
import Metrology.Approxis.AppRelRules
import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Compatibility Lemmas: structural compatibility of the logical relation, one rule per language construct. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

-- **Notation gotcha**: `refines E e e' (C A)` within `iprop(...)` clashes with
-- the `REL _ << _ @ _ : _` notation. The delaborator displays `refines` as
-- `REL ... : A`, and when `A` is actually `C A` (application), the parser/printer
-- get confused. Workaround: use `BI.intuitionistically`/`BI.forall` directly
-- rather than `iprop(□ (∀ ...))` for the few statements that need `C A`.

namespace ProbLang

section Compatibility
variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS hlc GF]

/-- Helper: unfold `lrel_arr` application. Proves that `(lrel_arr A B).car v v'`
is definitionally `⌜v.closed ∧ v'.closed⌝ ∗ □ (∀ w w', A w w' -∗ REL (v w) << (v' w') : B)`,
bridging the `.car`/`lrel.mk` projection that iris tactics don't reduce. The
closedness conjunct is port-specific (Lean's `Val` isn't intrinsically closed). -/
theorem lrel_arr_unfold (A B : lrel GF) (v v' : Val) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
        □ (∀ (w1 w2 : Val), A w1 w2 -∗
          refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B)) :=
  BIBase.Entails.rfl

theorem lrel_arr_unfold_wand (A B : lrel GF) (v v' : Val) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      iprop(□ (∀ (w1 w2 : Val), A w1 w2 -∗
        refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B)) := by
  iintro H
  ihave H' := lrel_arr_unfold A B v v' $$ H
  icases H' with ⟨_, HW⟩
  iexact HW

theorem lrel_arr_unfold_closed (A B : lrel GF) (v v' : Val) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) := by
  iintro H
  ihave H' := lrel_arr_unfold A B v v' $$ H
  icases H' with ⟨%hc, _⟩
  ipure_intro; exact hc

theorem lrel_arr_fold (A B : lrel GF) (v v' : Val) :
    iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      □ (∀ (w1 w2 : Val), A w1 w2 -∗
        refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B)) ⊢@{IProp GF}
      (lrel_arr A B).car v v' :=
  BIBase.Entails.rfl

theorem refines_pair {e1 e2 e1' e2' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
            refines ⊤ (Ectx.fill [EctxItem.pairR e1] e2)
                      (Ectx.fill [EctxItem.pairR e1'] e2') (lrel_prod A B)) := by
  -- Use an explicit rewrite to bridge [pairR e1].fill v2.1 = [pairL v2].fill e1.
  -- This is `rfl`, but `iapply`/`iexact` don't reduce it during unification.
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.pairR e1] [EctxItem.pairR e1'] (A := B)) $$ [IH2]
  · iexact IH2
  iintro %v2 %v2' HB
  have hbridge_L : Ectx.fill [EctxItem.pairR e1] v2.1 = Ectx.fill [EctxItem.pairL v2] e1 := rfl
  have hbridge_R : Ectx.fill [EctxItem.pairR e1'] v2'.1 = Ectx.fill [EctxItem.pairL v2'] e1' := rfl
  rw [hbridge_L, hbridge_R]
  iapply (refines_bind [EctxItem.pairL v2] [EctxItem.pairL v2'] (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v1 %v1' HA
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.pairL v2] v1.1)
    (e2 := Ectx.fill [EctxItem.pairL v2'] v1'.1)
    (v1 := ⟨.pair v1.1 v2.1, IsVal.pair v1.2 v2.2⟩)
    (v2 := ⟨.pair v1'.1 v2'.1, IsVal.pair v1'.2 v2'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_prod
  iexists v1, v1', v2, v2'
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  isplitl [HA]; · iexact HA
  iexact HB

/-- `refines_injl` (compatibility.v:31): left-injection compatibility. -/
theorem refines_injl {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' A)
      ⊢@{IProp GF} refines ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inl] e) (Ectx.fill [EctxItem.inl] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inl] [EctxItem.inl] (A := A)) $$ [IH]
  · iexact IH
  iintro %v %v' HA
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inl] v.1)
    (e2 := Ectx.fill [EctxItem.inl] v'.1)
    (v1 := ⟨.inl v.1, IsVal.inl v.2⟩) (v2 := ⟨.inl v'.1, IsVal.inl v'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  iapply BI.or_intro_l
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  iexact HA

/-- `refines_injr` (compatibility.v:41): right-injection compatibility. -/
theorem refines_injr {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' B)
      ⊢@{IProp GF} refines ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inr] e) (Ectx.fill [EctxItem.inr] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inr] [EctxItem.inr] (A := B)) $$ [IH]
  · iexact IH
  iintro %v %v' HB
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inr] v.1)
    (e2 := Ectx.fill [EctxItem.inr] v'.1)
    (v1 := ⟨.inr v.1, IsVal.inr v.2⟩) (v2 := ⟨.inr v'.1, IsVal.inr v'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  iapply BI.or_intro_r
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  iexact HB

/-- `refines_app` (compatibility.v:51): function application compatibility. -/
theorem refines_app {e1 e2 e1' e2' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e1 e1' (lrel_arr A B)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
            refines ⊤ (Ectx.fill [EctxItem.appR e1] e2)
                      (Ectx.fill [EctxItem.appR e1'] e2') B) := by
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR e1] [EctxItem.appR e1'] (A := A)) $$ [IH2]
  · iexact IH2
  iintro %v2 %v2' HA
  have hbL : Ectx.fill [EctxItem.appR e1] v2.1 = Ectx.fill [EctxItem.appL v2] e1 := rfl
  have hbR : Ectx.fill [EctxItem.appR e1'] v2'.1 = Ectx.fill [EctxItem.appL v2'] e1' := rfl
  rw [hbL, hbR]
  iapply (refines_bind [EctxItem.appL v2] [EctxItem.appL v2'] (A := lrel_arr A B)) $$ [IH1]
  · iexact IH1
  iintro %v1 %v1' #Hff
  ihave Hff' := lrel_arr_unfold_wand A B v1 v1' $$ Hff
  have hgL : Ectx.fill [EctxItem.appL v2] v1.1 = Exp.app v1.1 v2.1 := rfl
  have hgR : Ectx.fill [EctxItem.appL v2'] v1'.1 = Exp.app v1'.1 v2'.1 := rfl
  rw [hgL, hgR]
  iapply Hff' $$ %v2 %v2' HA

/-- `refines_seq` (compatibility.v:62): sequencing compatibility.
`(REL e1 << e1' : A) ∗ (REL e2 << e2' : B) ⊢ REL (e1; e2) << (e1'; e2') : B`.

**Port note**: Rocq's `e1 ;; e2 = (λ_. e2) e1` uses an anonymous binder, so
the body doesn't reference the bound variable. In Lean, `.lam e2`'s beta-step
gives `Exp.open' e2 v`, which equals `e2` only when e2 is locally closed.
We require `e2.IsLocallyClosed` and `e2'.IsLocallyClosed` as hypotheses. -/
theorem refines_seq (A : lrel GF) {e1 e2 e1' e2' : Exp} {B : lrel GF}
    (he2 : e2.IsLocallyClosed) (he2' : e2'.IsLocallyClosed) :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
        refines ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B) := by
  show iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
        refines ⊤ (Ectx.fill [EctxItem.appR (.lam e2)] e1)
          (Ectx.fill [EctxItem.appR (.lam e2')] e1') B)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR (.lam e2)] [EctxItem.appR (.lam e2')]
    (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v %v' _HA
  have hfv : Ectx.fill [EctxItem.appR (.lam e2)] v.1 =
    Ectx.fill [] (Exp.app (.lam e2) v.1) := rfl
  have hfv' : Ectx.fill [EctxItem.appR (.lam e2')] v'.1 =
    Exp.app (.lam e2') v'.1 := rfl
  rw [hfv, hfv']
  have hv_iv : IsVal v.1 := v.2
  iapply (refines_pure_l (E := ⊤) (K := []) (t := .app (.lam e2') v'.1)
    (e := .app (.lam e2) v.1) (e' := Exp.open' e2 v.1) (A := B)
    (n := 1) (φ := v.1.isValue) (Hφ := ⟨hv_iv⟩))
  simp only [Nat.repeat]
  have hopen : Exp.open' e2 v.1 = e2 := (Exp.open_lc 0 v.1 e2 he2).symm
  have hfill_empty : Ectx.fill [] (Exp.open' e2 v.1) = e2 := by
    show Exp.open' e2 v.1 = e2
    exact hopen
  rw [hfill_empty]
  iintro !>
  have hrhs : Exp.app (.lam e2') v'.1 = Ectx.fill [] (.app (.lam e2') v'.1) := rfl
  rw [hrhs]
  have hv'_iv : IsVal v'.1 := v'.2
  iapply (refines_pure_r (E := ⊤) (K := []) (t := e2)
    (e := .app (.lam e2') v'.1) (e' := Exp.open' e2' v'.1) (A := B)
    (n := 1) (φ := v'.1.isValue) (Hφ := ⟨hv'_iv⟩))
  have hopen' : Exp.open' e2' v'.1 = e2' := (Exp.open_lc 0 v'.1 e2' he2').symm
  have hfillRHS : Ectx.fill [] (Exp.open' e2' v'.1) = e2' := hopen'
  rw [hfillRHS]
  iexact IH2

/-- Helper: build `(lrel_exists C).car v v'` from a closedness witness and the
existential body. Defeq via `lrel.mk` projection. -/
theorem lrel_exists_unfold (C : lrel GF → lrel GF) (v v' : Val) :
    iprop((⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) ∗
      (∃ A : lrel GF, (C A).car v v'))
      ⊢@{IProp GF} (lrel_exists C).car v v' :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_nat).car v v' ⊢ ∃ n : Nat, v = #n ∧ v' = #n`. -/
theorem lrel_nat_unfold (v v' : Val) :
    (lrel_nat (GF := GF)).car v v'
      ⊢@{IProp GF} iprop(∃ n : Nat,
        ⌜v.1 = .lit (.int (n : Int)) ∧ v'.1 = .lit (.int (n : Int))⌝) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_pos_nat).car v v' ⊢ ∃ n : Nat, 0 < n ∧ v = #n ∧ v' = #n`. -/
theorem lrel_pos_nat_unfold (v v' : Val) :
    (lrel_pos_nat (GF := GF)).car v v'
      ⊢@{IProp GF} iprop(∃ n : Nat, ⌜0 < n ∧
        v.1 = .lit (.int (n : Int)) ∧ v'.1 = .lit (.int (n : Int))⌝) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_int).car v v' ⊢ ∃ n : Int, v = #n ∧ v' = #n`. -/
theorem lrel_int_unfold (v v' : Val) :
    (lrel_int (GF := GF)).car v v'
      ⊢@{IProp GF} iprop(∃ n : Int,
        ⌜v.1 = .lit (.int n) ∧ v'.1 = .lit (.int n)⌝) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_prod A B).car v v' ⊢ ∃ a1 a2 b1 b2, v=(a1,b1) ∧ v'=(a2,b2) ∧ A a1 a2 ∧ B b1 b2`. -/
theorem lrel_prod_unfold (A B : lrel GF) (v v' : Val) :
    (lrel_prod A B).car v v' ⊢@{IProp GF}
      iprop(∃ (a1 a2 b1 b2 : Val),
        (⌜v.1 = .pair a1.1 b1.1⌝) ∗ (⌜v'.1 = .pair a2.1 b2.1⌝) ∗
        A a1 a2 ∗ B b1 b2) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_sum A B).car v v' ⊢ ∃ w1 w2, ((inl form) ∨ (inr form))`. -/
theorem lrel_sum_unfold (A B : lrel GF) (v v' : Val) :
    (lrel_sum A B).car v v' ⊢@{IProp GF}
      iprop(∃ (w1 w2 : Val),
        ((⌜v.1 = .inl w1.1⌝) ∗ (⌜v'.1 = .inl w2.1⌝) ∗ A w1 w2)
        ∨
        ((⌜v.1 = .inr w1.1⌝) ∗ (⌜v'.1 = .inr w2.1⌝) ∗ B w1 w2)) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_bool).car v v' ⊢ ∃ b : Bool, v=#b ∧ v'=#b`. -/
theorem lrel_bool_unfold (v v' : Val) :
    (lrel_bool (GF := GF)).car v v' ⊢@{IProp GF}
      iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b) ∧ v'.1 = .lit (.bool b)⌝) :=
  BIBase.Entails.rfl

/-! ### Symmetric refines lemmas for pure-step constructors

These are bin_log_related-supporting helpers that step both sides via
`refines_pure_l/r` over the corresponding `PureExec` instance, then either
recurse on the projected component (`refines_fst`/`refines_snd`) or apply the
appropriate IH (`refines_case`/`refines_if`). -/

/-- `refines_fst`: if `e ≤ e' : A × B`, then `fst e ≤ fst e' : A`. -/
theorem refines_fst {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' (lrel_prod A B))
      ⊢@{IProp GF} refines ⊤ (.fst e) (.fst e') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.fst] e) (Ectx.fill [EctxItem.fst] e') A
  iintro IH
  iapply (refines_bind [EctxItem.fst] [EctxItem.fst] (A := lrel_prod A B)) $$ [IH]
  · iexact IH
  iintro %v %v' Hprod
  ihave HprodEx := lrel_prod_unfold A B v v' $$ Hprod
  icases HprodEx with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, HB⟩
  rw [show Ectx.fill [EctxItem.fst] v.1 = Exp.fst v.1 from rfl,
      show Ectx.fill [EctxItem.fst] v'.1 = Exp.fst v'.1 from rfl,
      hv, hv']
  have hfill : (Exp.fst (.pair a1.1 b1.1)) = Ectx.fill [] (Exp.fst (.pair a1.1 b1.1)) := rfl
  have hfill' : (Exp.fst (.pair a2.1 b2.1)) = Ectx.fill [] (Exp.fst (.pair a2.1 b2.1)) := rfl
  rw [hfill, hfill']
  have hφ1 : a1.1.isValue ∧ b1.1.isValue := ⟨a1.2.toIsValue, b1.2.toIsValue⟩
  have hφ2 : a2.1.isValue ∧ b2.1.isValue := ⟨a2.2.toIsValue, b2.2.toIsValue⟩
  iapply (refines_pure_l (K := []) (e := Exp.fst (.pair a1.1 b1.1)) (e' := a1.1)
    (Hex := pureExec_fst_pair) hφ1)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (e := Exp.fst (.pair a2.1 b2.1)) (e' := a2.1)
    (Hex := pureExec_fst_pair) hφ2)
  iapply refines_ret (e1 := Ectx.fill [] a1.1) (e2 := Ectx.fill [] a2.1)
    (v1 := a1) (v2 := a2) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iexact HA

/-- `refines_case`: case-split compatibility. After binding e0, the value
is `inl w` or `inr w`; we step the case to `e1 w` or `e2 w` and apply IH. -/
theorem refines_case {e0 e1 e2 e0' e1' e2' : Exp} {A B C : lrel GF} :
    iprop(refines ⊤ e0 e0' (lrel_sum A B)) ⊢@{IProp GF}
      iprop(refines ⊤ e1 e1' (lrel_arr A C) -∗
        refines ⊤ e2 e2' (lrel_arr B C) -∗
        refines ⊤ (.case e0 e1 e2) (.case e0' e1' e2') C) := by
  show _ ⊢@{IProp GF}
    iprop(refines ⊤ e1 e1' (lrel_arr A C) -∗
      refines ⊤ e2 e2' (lrel_arr B C) -∗
      refines ⊤ (Ectx.fill [EctxItem.case e1 e2] e0)
        (Ectx.fill [EctxItem.case e1' e2'] e0') C)
  iintro IH0 IH1 IH2
  iapply (refines_bind [EctxItem.case e1 e2] [EctxItem.case e1' e2']
    (A := lrel_sum A B)) $$ [IH0]
  · iexact IH0
  iintro %v %v' Hsum
  ihave HsumEx := lrel_sum_unfold A B v v' $$ Hsum
  icases HsumEx with ⟨%w1, %w2, HOr⟩
  rw [show Ectx.fill [EctxItem.case e1 e2] v.1 = Exp.case v.1 e1 e2 from rfl,
      show Ectx.fill [EctxItem.case e1' e2'] v'.1 = Exp.case v'.1 e1' e2' from rfl]
  icases HOr with (⟨%hv, %hv', HA⟩ | ⟨%hv, %hv', HB⟩)
  · rw [hv, hv']
    have hf1 : (Exp.case (.inl w1.1) e1 e2) = Ectx.fill [] (Exp.case (.inl w1.1) e1 e2) := rfl
    have hf2 : (Exp.case (.inl w2.1) e1' e2') = Ectx.fill [] (Exp.case (.inl w2.1) e1' e2') := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_case_inl) w1.2.toIsValue)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_case_inl) w2.2.toIsValue)
    rw [show Ectx.fill [] (Exp.app e1 w1.1) = Exp.app e1 w1.1 from rfl,
        show Ectx.fill [] (Exp.app e1' w2.1) = Exp.app e1' w2.1 from rfl]
    have hap1 : Exp.app e1 w1.1 = Ectx.fill [EctxItem.appR e1] w1.1 := rfl
    have hap2 : Exp.app e1' w2.1 = Ectx.fill [EctxItem.appR e1'] w2.1 := rfl
    rw [hap1, hap2]
    iapply (refines_app (A := A) (B := C)) $$ [IH1]
    · iexact IH1
    iapply refines_ret (e1 := w1.1) (e2 := w2.1) (v1 := w1) (v2 := w2)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HA
  · rw [hv, hv']
    have hf1 : (Exp.case (.inr w1.1) e1 e2) = Ectx.fill [] (Exp.case (.inr w1.1) e1 e2) := rfl
    have hf2 : (Exp.case (.inr w2.1) e1' e2') = Ectx.fill [] (Exp.case (.inr w2.1) e1' e2') := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_case_inr) w1.2.toIsValue)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_case_inr) w2.2.toIsValue)
    rw [show Ectx.fill [] (Exp.app e2 w1.1) = Exp.app e2 w1.1 from rfl,
        show Ectx.fill [] (Exp.app e2' w2.1) = Exp.app e2' w2.1 from rfl]
    have hap1 : Exp.app e2 w1.1 = Ectx.fill [EctxItem.appR e2] w1.1 := rfl
    have hap2 : Exp.app e2' w2.1 = Ectx.fill [EctxItem.appR e2'] w2.1 := rfl
    rw [hap1, hap2]
    iapply (refines_app (A := B) (B := C)) $$ [IH2]
    · iexact IH2
    iapply refines_ret (e1 := w1.1) (e2 := w2.1) (v1 := w1) (v2 := w2)
      (hv1 := rfl) (hv2 := rfl)
    imodintro
    iexact HB


/-- `refines_binop_pure`: helper for binop compatibility when `op.eval` on
literal values gives a deterministic result. Steps both sides via PureExec
on `binop op v1 v2 → r`, then concludes via `refines_ret` with `r` in the
provided result relation `Hres : Aresult r r`. -/
theorem refines_binop_pure (op : BinOp) (v1 v2 r : Exp)
    (hv1 : IsVal v1) (hv2 : IsVal v2) (hrv : IsVal r)
    (heval : op.eval v1 v2 = some r) {A : lrel GF}
    (HA : ⊢@{IProp GF} A ⟨r, hrv⟩ ⟨r, hrv⟩) :
    ⊢@{IProp GF} refines ⊤ (.binop op v1 v2) (.binop op v1 v2) A := by
  have hf : Exp.binop op v1 v2 = Ectx.fill [] (Exp.binop op v1 v2) := rfl
  rw [hf]
  have hφ : v1.isValue ∧ v2.isValue ∧ op.eval v1 v2 = some r :=
    ⟨hv1.toIsValue, hv2.toIsValue, heval⟩
  iapply (refines_pure_l (K := []) (Hex := pureExec_binop) hφ)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (Hex := pureExec_binop) hφ)
  iapply refines_ret (e1 := Ectx.fill [] r) (e2 := Ectx.fill [] r)
    (v1 := ⟨r, hrv⟩) (v2 := ⟨r, hrv⟩) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply HA

/-- `refines_alloctape`: tape-allocation compatibility. After binding the
bound argument to value `n : Int`, allocate fresh tapes on both sides and
establish the `lrel_tape` invariant. -/
theorem refines_alloctape {e e' : Exp} :
    iprop(refines ⊤ e e' lrel_int)
      ⊢@{IProp GF} refines ⊤ (.tape e) (.tape e') lrel_tape := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.tape] e) (Ectx.fill [EctxItem.tape] e') lrel_tape
  iintro IH
  iapply (refines_bind [EctxItem.tape] [EctxItem.tape] (A := lrel_int)) $$ [IH]
  · iexact IH
  iintro %v %v' Hint
  ihave HvEx := lrel_int_unfold v v' $$ Hint
  icases HvEx with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.tape] v.1 = Exp.tape v.1 from rfl,
      show Ectx.fill [EctxItem.tape] v'.1 = Exp.tape v'.1 from rfl,
      hv, hv']
  unfold refines
  iintro %K %ε Hj Hna Herr Hpos
  ihave HStep := step_alloctape (GF := GF) (E := ⊤) K n $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨%l', HKRes, Hl'frag⟩
  iapply specUpdate_ret
  iapply (wp_lift_atomic_head_step (e₁ := .tape (.lit (.int n)))
    (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w))
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.TapeS (ℓ := σ₁.tapes.fresh) rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    ihave HAlloc := app_state_tape_alloc (GF := GF) (σ := σ₁) (Tape.empty n) $$ Hσ
    imod HAlloc with ⟨Hσ', Hlfrag⟩
    set lL := σ₁.tapes.fresh
    have htape_eq : Tape.empty n = (⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n })⟩ : Tape) := rfl
    ihave HlfragV : iprop(appTapesFrag lL ⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n })⟩) $$ [Hlfrag]
    · rw [← htape_eq]; iexact Hlfrag
    ihave Hl'fragV : iprop(specTapesFrag l' ⟨n, ([] : List { z' : Int // 0 ≤ z' ∧ z' < n })⟩) $$ [Hl'frag]
    · rw [← htape_eq]; iexact Hl'frag
    ihave HInvBody : iprop(▷ ((appTapesFrag lL ⟨n, []⟩) ∗
        (specTapesFrag l' ⟨n, []⟩))) $$ [HlfragV Hl'fragV]
    · iintro !>
      isplitl [HlfragV]; · iexact HlfragV
      iexact Hl'fragV
    imod (Iris.inv_alloc (N := logN.@ ((lL, l') : Loc × Loc)) (E := ⊤)
      (P := iprop((appTapesFrag lL ⟨n, []⟩) ∗ (specTapesFrag l' ⟨n, []⟩)))) $$ [HInvBody] with #HInv
    · iexact HInvBody
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    -- Final: ∃ v' ε', ⤇ K.fill v'.1 ∗ naOwnP ⊤ ∗ ↯ ε' ∗ ⌜0 < ε'⌝ ∗ lrel_tape.car _ _
    iexists ⟨.lit (.lbl l'), IsVal.lit⟩
    iexists ε
    isplitl [HKRes]; · iexact HKRes
    isplitl [Hna]; · iexact Hna
    isplitl [Herr]; · iexact Herr
    isplitl [Hpos]; · iexact Hpos
    unfold lrel_tape
    iexists lL, l', n
    isplitr; · ipure_intro; rfl
    isplitr; · ipure_intro; rfl
    iexact HInv

/-- `refines_alloc`: alloc compatibility. After binding `e/e'` to value pair
related at `A`, alloc fresh refs on both sides and establish the invariant. -/
theorem refines_alloc {e e' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e e' A)
      ⊢@{IProp GF} refines ⊤ (.alloc e) (.alloc e') (lrel_ref A) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.alloc] e) (Ectx.fill [EctxItem.alloc] e') (lrel_ref A)
  iintro IH
  iapply (refines_bind [EctxItem.alloc] [EctxItem.alloc] (A := A)) $$ [IH]
  · iexact IH
  iintro %v %v' #HA
  rw [show Ectx.fill [EctxItem.alloc] v.1 = Exp.alloc v.1 from rfl,
      show Ectx.fill [EctxItem.alloc] v'.1 = Exp.alloc v'.1 from rfl]
  -- Allocate on RHS first (so we have l') then LHS, then set up invariant.
  have hfL : Exp.alloc v.1 = Ectx.fill [] (Exp.alloc v.1) := rfl
  have hfR : Exp.alloc v'.1 = Ectx.fill [] (Exp.alloc v'.1) := rfl
  rw [hfL, hfR]
  iapply (refines_alloc_r (K := []))
  iintro %l' Hl'
  iapply (refines_alloc_l (K := []))
  iintro %l Hl
  -- Now establish the invariant `inv (logN.@(l, l')) (∃ w1 w2, l ↦ w1 ∗ l' ↦ₛ w2 ∗ A w1 w2)`.
  -- Use `Iris.inv_alloc` with the body containing v, v'.
  ihave HInvBody : iprop(▷ ∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2) $$ [Hl Hl' HA]
  · iintro !>
    iexists v, v'
    isplitl [Hl]; · iexact Hl
    isplitl [Hl']; · iexact Hl'
    iexact HA
  imod (Iris.inv_alloc (N := logN.@ ((l, l') : Loc × Loc)) (E := ⊤)
    (P := iprop(∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2))) $$ [HInvBody] with #HInv
  · iexact HInvBody
  iapply refines_ret (e1 := Ectx.fill [] (.lit (.loc l)))
    (e2 := Ectx.fill [] (.lit (.loc l')))
    (v1 := ⟨.lit (.loc l), IsVal.lit⟩) (v2 := ⟨.lit (.loc l'), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_ref
  iexists l, l'
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  iexact HInv

/-- `refines_if`: if-then-else compatibility. -/
theorem refines_if {e0 e1 e2 e0' e1' e2' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e0 e0' lrel_bool) ⊢@{IProp GF}
      iprop(refines ⊤ e1 e1' A -∗ refines ⊤ e2 e2' A -∗
        refines ⊤ (.cond e0 e1 e2) (.cond e0' e1' e2') A) := by
  show _ ⊢@{IProp GF}
    iprop(refines ⊤ e1 e1' A -∗ refines ⊤ e2 e2' A -∗
      refines ⊤ (Ectx.fill [EctxItem.condC e1 e2] e0)
        (Ectx.fill [EctxItem.condC e1' e2'] e0') A)
  iintro IH0 IH1 IH2
  iapply (refines_bind [EctxItem.condC e1 e2] [EctxItem.condC e1' e2'] (A := lrel_bool)) $$ [IH0]
  · iexact IH0
  iintro %v %v' Hb
  ihave Hb' := lrel_bool_unfold v v' $$ Hb
  icases Hb' with ⟨%b, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.condC e1 e2] v.1 = Exp.cond v.1 e1 e2 from rfl,
      show Ectx.fill [EctxItem.condC e1' e2'] v'.1 = Exp.cond v'.1 e1' e2' from rfl,
      hv, hv']
  -- Goal: refines ⊤ (.cond #b e1 e2) (.cond #b e1' e2') A. Case-split on b.
  cases b with
  | true =>
    have hf1 : (Exp.cond (.lit (.bool true)) e1 e2) =
        Ectx.fill [] (Exp.cond (.lit (.bool true)) e1 e2) := rfl
    have hf2 : (Exp.cond (.lit (.bool true)) e1' e2') =
        Ectx.fill [] (Exp.cond (.lit (.bool true)) e1' e2') := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_cond_true) trivial)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_cond_true) trivial)
    rw [show Ectx.fill [] e1 = e1 from rfl, show Ectx.fill [] e1' = e1' from rfl]
    iexact IH1
  | false =>
    have hf1 : (Exp.cond (.lit (.bool false)) e1 e2) =
        Ectx.fill [] (Exp.cond (.lit (.bool false)) e1 e2) := rfl
    have hf2 : (Exp.cond (.lit (.bool false)) e1' e2') =
        Ectx.fill [] (Exp.cond (.lit (.bool false)) e1' e2') := rfl
    rw [hf1, hf2]
    iapply (refines_pure_l (K := []) (Hex := pureExec_cond_false) trivial)
    simp only [Nat.repeat]
    iintro !>
    iapply (refines_pure_r (K := []) (Hex := pureExec_cond_false) trivial)
    rw [show Ectx.fill [] e2 = e2 from rfl, show Ectx.fill [] e2' = e2' from rfl]
    iexact IH2

/-- `refines_snd`: if `e ≤ e' : A × B`, then `snd e ≤ snd e' : B`. -/
theorem refines_snd {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' (lrel_prod A B))
      ⊢@{IProp GF} refines ⊤ (.snd e) (.snd e') B := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.snd] e) (Ectx.fill [EctxItem.snd] e') B
  iintro IH
  iapply (refines_bind [EctxItem.snd] [EctxItem.snd] (A := lrel_prod A B)) $$ [IH]
  · iexact IH
  iintro %v %v' Hprod
  ihave HprodEx := lrel_prod_unfold A B v v' $$ Hprod
  icases HprodEx with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, HB⟩
  rw [show Ectx.fill [EctxItem.snd] v.1 = Exp.snd v.1 from rfl,
      show Ectx.fill [EctxItem.snd] v'.1 = Exp.snd v'.1 from rfl,
      hv, hv']
  have hfill : (Exp.snd (.pair a1.1 b1.1)) = Ectx.fill [] (Exp.snd (.pair a1.1 b1.1)) := rfl
  have hfill' : (Exp.snd (.pair a2.1 b2.1)) = Ectx.fill [] (Exp.snd (.pair a2.1 b2.1)) := rfl
  rw [hfill, hfill']
  have hφ1 : a1.1.isValue ∧ b1.1.isValue := ⟨a1.2.toIsValue, b1.2.toIsValue⟩
  have hφ2 : a2.1.isValue ∧ b2.1.isValue := ⟨a2.2.toIsValue, b2.2.toIsValue⟩
  iapply (refines_pure_l (K := []) (e := Exp.snd (.pair a1.1 b1.1)) (e' := b1.1)
    (Hex := pureExec_snd_pair) hφ1)
  simp only [Nat.repeat]
  iintro !>
  iapply (refines_pure_r (K := []) (e := Exp.snd (.pair a2.1 b2.1)) (e' := b2.1)
    (Hex := pureExec_snd_pair) hφ2)
  iapply refines_ret (e1 := Ectx.fill [] b1.1) (e2 := Ectx.fill [] b2.1)
    (v1 := b1) (v2 := b2) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iexact HB

/-- Helper: `(lrel_tape).car v v'` exposes the tape locations and bound. -/
theorem lrel_tape_unfold (v v' : Val) :
    (lrel_tape (GF := GF)).car v v' ⊢@{IProp GF}
      iprop(∃ (α1 α2 : Loc) (z : Int),
        (⌜ v.1 = .lit (.lbl α1) ⌝) ∗ (⌜ v'.1 = .lit (.lbl α2) ⌝) ∗
        Iris.inv (logN.@ ((α1, α2) : Loc × Loc))
          (iprop((appTapesFrag α1 ⟨z, []⟩) ∗ (specTapesFrag α2 ⟨z, []⟩)))) :=
  BIBase.Entails.rfl

/-- `refines_pack` (compatibility.v:73): existential-packing compatibility.
Given `REL e << e' : C A` for a specific `A`, conclude `REL e << e' : ∃ A, C A`.
Requires a proof that `C A` only relates closed values (port-specific). -/
theorem refines_pack (A : lrel GF) {e e' : Exp} {C : lrel GF → lrel GF}
    (_hC : OFE.NonExpansive C)
    (hCclosed : ∀ v v' : Val, (C A).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝)) :
    refines (⊤ : CoPset) e e' (C A)
      ⊢@{IProp GF} refines ⊤ e e' (lrel_exists C) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill Ectx.empty e) (Ectx.fill Ectx.empty e') (lrel_exists C)
  iintro IH
  iapply (refines_bind Ectx.empty Ectx.empty (A := C A)) $$ [IH]
  · iexact IH
  iintro %v %v' HCA
  iapply refines_ret
    (e1 := Ectx.fill Ectx.empty v.1) (e2 := Ectx.fill Ectx.empty v'.1)
    (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  ihave %Hcl : iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ : IProp GF) $$ [HCA]
  · iapply (hCclosed v v'); iexact HCA
  iapply lrel_exists_unfold
  isplitr
  · ipure_intro; exact Hcl
  iexists A
  iexact HCA

/-- `refines_forall` (compatibility.v:83): universal-typing compatibility.
If for all semantic types `A`, `REL e << e' : C A`, then `(λ_. e) << (λ_. e') : ∀A, C A`.

Two pure beta steps over the value-restricted forall encoding (via
`refines_pure_l`/`refines_pure_r`), then apply the persistent IH at the chosen
semantic type `A`.

**Port note**: same `IsLocallyClosed` requirement as `refines_seq`. -/
theorem refines_forall {e e' : Exp} {C : lrel GF → lrel GF}
    (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed)
    (he_fv : e.fv = ∅) (he'_fv : e'.fv = ∅) :
    BI.intuitionistically (BI.forall (fun A : lrel GF => refines (⊤ : CoPset) e e' (C A)))
      ⊢@{IProp GF} refines ⊤ (.lam e) (.lam e') (lrel_forall C) := by
  iintro #H
  iapply (refines_ret (e1 := Exp.lam e) (e2 := Exp.lam e')
    (v1 := ⟨.lam e, IsVal.lam⟩) (v2 := ⟨.lam e', IsVal.lam⟩) (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_forall
  iintro %A
  unfold lrel_arr
  isplitr
  · ipure_intro
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
  -- Hunit : lrel_unit u u' = ⌜u.1 = .lit .unit ∧ u'.1 = .lit .unit⌝.
  -- Goal: refines ⊤ (.app (.lam e) u.1) (.app (.lam e') u'.1) (C A).
  -- Beta-step LHS: reshape, apply refines_pure_l with n=1, use open_lc.
  have hfL : Exp.app (.lam e) u.1 = Ectx.fill [] (Exp.app (.lam e) u.1) := rfl
  rw [hfL]
  have hu_iv : IsVal u.1 := u.2
  iapply (refines_pure_l (E := ⊤) (K := []) (t := .app (.lam e') u'.1)
    (e := .app (.lam e) u.1) (e' := Exp.open' e u.1) (A := C A)
    (n := 1) (φ := u.1.isValue) (Hφ := ⟨hu_iv⟩))
  simp only [Nat.repeat]
  have hopenL : Exp.open' e u.1 = e := (Exp.open_lc 0 u.1 e he).symm
  have hfillL : Ectx.fill [] (Exp.open' e u.1) = e := hopenL
  rw [hfillL]
  iintro !>
  -- Goal: refines ⊤ e (.app (.lam e') u'.1) (C A).
  -- Beta-step RHS.
  have hfR : Exp.app (.lam e') u'.1 = Ectx.fill [] (Exp.app (.lam e') u'.1) := rfl
  rw [hfR]
  have hu'_iv : IsVal u'.1 := u'.2
  iapply (refines_pure_r (E := ⊤) (K := []) (t := e)
    (e := .app (.lam e') u'.1) (e' := Exp.open' e' u'.1) (A := C A)
    (n := 1) (φ := u'.1.isValue) (Hφ := ⟨hu'_iv⟩))
  have hopenR : Exp.open' e' u'.1 = e' := (Exp.open_lc 0 u'.1 e' he').symm
  have hfillR : Ectx.fill [] (Exp.open' e' u'.1) = e' := hopenR
  rw [hfillR]
  -- Goal: refines ⊤ e e' (C A). Apply IH (persistent H) at A.
  iapply H

/-- Helper: introduce a step-fupd from a `▷ P` with mask shift (E2 ⊆ E1).

Standard Iris `step_fupd_intro`. Construction:
- Use `fupd_mask_intro`: `((|={E2,E1}=> emp) -∗ Q) ⊢ |={E1, E2}=> Q`.
- Set Q := `▷ |={E2, E1}=> P`.
- Provide the wand: given `Hclose : |={E2,E1}=> emp`, produce `▷ |={E2,E1}=> P`.
  Lift Hclose under ▷ via `BI.later_intro`, combine with `▷ P`, mono fupd to drop emp. -/
theorem step_fupd_intro_later {E1 E2 : CoPset} {P : IProp GF} (HE : E2 ⊆ E1) :
    iprop(▷ P) ⊢@{IProp GF} iprop(|={E1, E2}=> ▷ |={E2, E1}=> P) := by
  iintro HP
  iapply Iris.fupd_mask_intro HE
  iintro Hclose
  iintro !>
  imod Hclose
  imodintro
  iexact HP

/-- Helper: `(lrel_ref A).car v v'` exposes the existence of related locations
plus the heap invariant. -/
theorem lrel_ref_unfold (A : lrel GF) (v v' : Val) :
    (lrel_ref A).car v v' ⊢@{IProp GF}
      iprop(∃ (l l' : Loc),
        (⌜ v.1 = .lit (.loc l) ⌝) ∗ (⌜ v'.1 = .lit (.loc l') ⌝) ∗
        Iris.inv (logN.@ ((l, l') : Loc × Loc))
          (iprop(∃ (w1 w2 : Val),
            (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2))) :=
  BIBase.Entails.rfl

/-- `refines_store` (compatibility.v:95): store compatibility.
Stores to related references preserve the refinement.

Same structure as `refines_load`: refines_bind on e2 then e1, destructure
`lrel_ref A` to get `(l, l', inv ...)`, refines_atomic_l, open inv,
step_store + wp_store, close inv with the NEW values. -/
theorem refines_store {e1 e2 e1' e2' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
        refines ⊤ (.store e1 e2) (.store e1' e2') lrel_unit) := by
  -- Reshape goal upfront to expose the bind contexts.
  show iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
        refines ⊤ (Ectx.fill [EctxItem.storeR e1] e2)
          (Ectx.fill [EctxItem.storeR e1'] e2') lrel_unit)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.storeR e1] [EctxItem.storeR e1'] (A := A)) $$ [IH2]
  · iexact IH2
  iintro %w %w' #HwA
  -- Goal: refines ⊤ ([storeR e1].fill w.1) ([storeR e1'].fill w'.1) lrel_unit
  -- which equals refines ⊤ (.store e1 w.1) (.store e1' w'.1) lrel_unit.
  -- Reshape via fill equalities: .store e1 w.1 = [storeL w].fill e1.
  have hfillR : Ectx.fill [EctxItem.storeR e1] w.1 = Ectx.fill [EctxItem.storeL w] e1 := rfl
  have hfillR' : Ectx.fill [EctxItem.storeR e1'] w'.1 = Ectx.fill [EctxItem.storeL w'] e1' := rfl
  rw [hfillR, hfillR']
  iapply (refines_bind [EctxItem.storeL w] [EctxItem.storeL w'] (A := lrel_ref A)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv : Ectx.fill [EctxItem.storeL w] v.1 = Exp.store v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.storeL w'] v'.1 = Exp.store v'.1 w'.1 := rfl
  rw [hfillv, hfillv', heq, heq']
  -- Goal: refines ⊤ (.store #l w.1) (.store #l' w'.1) lrel_unit.
  have hfill_empty : Exp.store (.lit (.loc l)) w.1 =
    Ectx.fill [] (Exp.store (.lit (.loc l)) w.1) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := Exp.store (.lit (.loc l)) w.1)
    (t := Exp.store (.lit (.loc l')) w'.1)
    (A := lrel_unit) (OpenInv.of_atomic (Atomic.store l w)))
  iintro %K' Hr
  -- Open the invariant.
  have hsub : (↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  ihave HInvBody1 := later_exists.mpr $$ HInvBody
  icases HInvBody1 with ⟨%v1, HInvBody2⟩
  ihave HInvBody3 := later_exists.mpr $$ HInvBody2
  icases HInvBody3 with ⟨%v2, HInvBody4⟩
  ihave HInvBody5 := later_sep.mp $$ HInvBody4
  icases HInvBody5 with ⟨Hv1L, HInvBody6⟩
  ihave HInvBody7 := later_sep.mp $$ HInvBody6
  icases HInvBody7 with ⟨Hv2L, _HwAL⟩
  imod Hv1L with Hv1
  imod Hv2L with Hv2
  imodintro
  -- RHS step: step_store on Hr.
  ihave HStep := step_store
    (E := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) K' (l := l') (v_old := v2) (v_new := w')
    (hv := w'.2) (hnew := Exp.toVal?_ofVal w') $$ [Hr Hv2]
  · isplitl [Hr]; · iexact Hr
    iexact Hv2
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hv2'⟩
  iapply specUpdate_ret
  -- LHS step: wp_store. Use wp_step_fupd to thread close-inv through the step.
  -- Actually, there's no extra ▷ to absorb here (HwA is already persistent),
  -- so we don't need wp_step_fupd.
  have hstoreL : Exp.store (.lit (.loc l)) w.1 =
    Exp.store (.lit (.loc l)) (Exp.ofVal w) := rfl
  rw [hstoreL]
  iapply (wp_store (l := l) (v := w) (v' := v1))
  isplitl [Hv1]; · iexact Hv1
  iintro Hw1'
  -- Close the invariant with NEW values w, w'.
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hv2' HwA]
  · iintro !>
    iexists w, w'
    isplitl [Hw1']; · iexact Hw1'
    isplitl [Hv2']; · iexact Hv2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with _
  imodintro
  iexists (Exp.lit .unit)
  isplitl [HKRes]; · iexact HKRes
  iapply (refines_ret (e1 := Ectx.fill [] (Exp.lit .unit)) (e2 := Exp.lit .unit)
    (v1 := ⟨.lit .unit, IsVal.lit⟩) (v2 := ⟨.lit .unit, IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_unit
  ipure_intro
  exact ⟨rfl, rfl⟩

/-- `refines_load` (compatibility.v:118): dereference compatibility.
Loading through related references yields related values.

Mirrors Rocq's proof: `refines_bind` to focus on the values, destructure
`lrel_ref A` to get `(l, l', inv ...)`, apply `refines_atomic_l`, open the
invariant, RHS-step via `step_load`, LHS-step via `wp_load`, close the
invariant, produce the value post.

Uses `wp_step_fupd` (AppWeakestpre.lean:2048) to absorb the `▷ A.car w1 w2`
witness from the inv-open through `wp_load`'s atomic step. -/
theorem refines_load {e e' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e e' (lrel_ref A))
      ⊢@{IProp GF} refines ⊤ (.load e) (.load e') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.load] e) (Ectx.fill [EctxItem.load] e') A
  iintro IH
  iapply (refines_bind [EctxItem.load] [EctxItem.load] (A := lrel_ref A)) $$ [IH]
  · iexact IH
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv : Ectx.fill [EctxItem.load] v.1 = Exp.load v.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.load] v'.1 = Exp.load v'.1 := rfl
  rw [hfillv, hfillv', heq, heq']
  have hfill_empty : Exp.load (.lit (.loc l)) = Ectx.fill [] (Exp.load (.lit (.loc l))) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := Exp.load (.lit (.loc l))) (t := Exp.load (.lit (.loc l')))
    (A := A) (OpenInv.of_atomic (Atomic.load l)))
  iintro %K' Hr
  -- Open the invariant.
  have hsub : (↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  -- HInvBody : ▷ (∃ w1 w2, l ↦ w1 ∗ l' ↦ₛ w2 ∗ A w1 w2).
  ihave HInvBody1 := later_exists.mpr $$ HInvBody
  icases HInvBody1 with ⟨%w1, HInvBody2⟩
  ihave HInvBody3 := later_exists.mpr $$ HInvBody2
  icases HInvBody3 with ⟨%w2, HInvBody4⟩
  ihave HInvBody5 := later_sep.mp $$ HInvBody4
  icases HInvBody5 with ⟨Hw1L, HInvBody6⟩
  ihave HInvBody7 := later_sep.mp $$ HInvBody6
  icases HInvBody7 with ⟨Hw2L, #HwAL⟩
  imod Hw1L with Hw1
  imod Hw2L with Hw2
  imodintro
  -- RHS step: step_load on Hr.
  ihave HStep := step_load (E := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) K' (l := l') (v := w2)
    $$ [Hr Hw2]
  · isplitl [Hr]; · iexact Hr
    iexact Hw2
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hw2'⟩
  iapply specUpdate_ret
  -- LHS step: wp_load, but use wp_step_fupd to thread HwAL : ▷ A.car w1 w2
  -- through the step. The step absorbs the outer ▷, so inside the post we
  -- have access to A.car w1 w2 directly.
  have HE : (∅ : CoPset) ⊆ (⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) :=
    Std.LawfulSet.empty_subset
  have hv : (Exp.load (.lit (.loc l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_step_fupd (P := A.car w1 w2)
    (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅) HE hv)
  isplitl [HwAL]
  · -- First sub-goal (with HwAL): |={E1, ∅}=> ▷ |={∅, E1}=> A.car w1 w2.
    ihave Hgoal := step_fupd_intro_later
      (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅)
      (P := A.car w1 w2) HE $$ HwAL
    iexact Hgoal
  -- Second sub-goal: wp ∅ (.load #l) (fun v => A.car w1 w2 -∗ ...).
  iapply (wp_load (l := l) (v := w1))
  isplitl [Hw1]; · iexact Hw1
  iintro Hw1'
  -- Now goal post: A.car w1 w2 -∗ ... (the wp_step_fupd post wand).
  iintro #HwA
  -- HwA : A.car w1 w2 (no ▷!). Now close inv and produce post.
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hw2' HwA]
  · iintro !>
    iexists w1, w2
    isplitl [Hw1']; · iexact Hw1'
    isplitl [Hw2']; · iexact Hw2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with _
  imodintro
  iexists (Exp.ofVal w2)
  isplitl [HKRes]; · iexact HKRes
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
theorem refines_rand_tape {e1 e1' e2 e2' : Exp} :
    iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat) := by
  show iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
    iprop(refines ⊤ e2 e2' lrel_tape -∗
      refines ⊤ (Ectx.fill [EctxItem.randR e1] e2)
                (Ectx.fill [EctxItem.randR e1'] e2') lrel_nat)
  iintro IH1 IH2
  -- Bind e2/e2' to get tape locations α, α' and bound N under invariant.
  iapply (refines_bind [EctxItem.randR e1] [EctxItem.randR e1']
    (A := lrel_tape)) $$ [IH2]
  · iexact IH2
  iintro %w %w' HTapeRel
  ihave HTapeEx := lrel_tape_unfold _ _ $$ HTapeRel
  icases HTapeEx with ⟨%α, %α', %N, %Hw, %Hw', #Hinv⟩
  -- Reshape via defeq: [randR e1].fill w.1 = .rand e1 w.1 = [randL w].fill e1.
  have hfillR_to_L : Ectx.fill [EctxItem.randR e1] w.1 =
    Ectx.fill [EctxItem.randL w] e1 := rfl
  have hfillR_to_L' : Ectx.fill [EctxItem.randR e1'] w'.1 =
    Ectx.fill [EctxItem.randL w'] e1' := rfl
  rw [hfillR_to_L, hfillR_to_L']
  -- Now bind e1/e1' to get M : Nat (positive).
  iapply (refines_bind [EctxItem.randL w] [EctxItem.randL w']
    (A := lrel_pos_nat)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HPosNat
  ihave HPosNatEx := lrel_pos_nat_unfold v v' $$ HPosNat
  icases HPosNatEx with ⟨%M, %hM_pos, %HvM, %Hv'M⟩
  have hfillv : Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 := rfl
  rw [hfillv, hfillv', HvM, Hv'M, Hw, Hw']
  -- Goal: refines ⊤ (.rand #M (lbl α)) (.rand #M (lbl α')) lrel_nat.
  -- Apply refines_atomic_l at K = [].
  have hfill_empty : Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α)) =
    Ectx.fill [] (Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α))) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
    (K := []) (e1 := Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α)))
    (t := Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α')))
    (A := lrel_nat) (OpenInv.of_atomic (Atomic.rand_lbl (M : Int) α)))
  iintro %K' Hr
  -- Open the tape invariant.
  have hsub : (↑(logN.@ ((α, α') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  -- HInvBody : ▷ (α ↪ₐ ⟨N, []⟩ ∗ α' ↪ₛ ⟨N, []⟩). Push ▷ inside, strip via Timeless.
  ihave HInvBody1 := later_sep.mp $$ HInvBody
  icases HInvBody1 with ⟨HαL, Hα'L⟩
  imod HαL with Hα
  imod Hα'L with Hα'
  imodintro
  -- Convert backend-frags to user-level appNatTape/specNatTape.
  ihave HαN := app_empty_to_natTape (GF := GF) (l := α) (z := N) $$ Hα
  ihave Hα'N := spec_empty_to_natTape (GF := GF) (l := α') (z := N) $$ Hα'
  -- Case-split on N = M.
  by_cases hNM : N = (M : Int)
  · -- N = M case: use wp_couple_rand_lbl_rand_lbl.
    subst hNM
    -- M > 0 comes from lrel_pos_nat.
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
    isplitl [Hr]; · iexact Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    -- Close invariant.
    ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := M) $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := M) $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨(M : Int), []⟩ ∗
        specTapesFrag α' ⟨(M : Int), []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      isplitl [HαBack]; · iexact HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with _
    imodintro
    iexists (.lit (.int (id n)))
    isplitl [HKRes]; · iexact HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int n)))
      (e2 := Exp.lit (.int (id n)))
      (v1 := ⟨.lit (.int n), IsVal.lit⟩) (v2 := ⟨.lit (.int (id n)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipure_intro
    have hk : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn0
    refine ⟨?_, ?_⟩ <;> rw [hk]
    · rfl
  · -- N ≠ M case: use wp_couple_rand_lbl_rand_lbl_wrong (rand bound z = M, tape bound N).
    have hMpos : (0 : Int) < (M : Int) := by exact_mod_cast hM_pos
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
    isplitl [Hr]; · iexact Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
        specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      isplitl [HαBack]; · iexact HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with _
    imodintro
    iexists (.lit (.int (id n)))
    isplitl [HKRes]; · iexact HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int n)))
      (e2 := Exp.lit (.int (id n)))
      (v1 := ⟨.lit (.int n), IsVal.lit⟩) (v2 := ⟨.lit (.int (id n)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipure_intro
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
theorem refines_rand_unit {e e' : Exp} :
    iprop(refines ⊤ e e' lrel_pos_nat)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e)
          (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e')
          lrel_nat := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    (A := lrel_pos_nat)) $$ [IH]
  · iexact IH
  iintro %v %v' HPosNat
  ihave HPosNatEx := lrel_pos_nat_unfold v v' $$ HPosNat
  icases HPosNatEx with ⟨%n, %hn_pos, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v.1 =
      Exp.rand v.1 (.lit .unit) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v'.1 =
      Exp.rand v'.1 (.lit .unit) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  -- Goal: refines ⊤ (.rand #n ()) (.rand #n ()) lrel_nat. Apply couple_rands_lr.
  · have hnpos : (0 : Int) < (n : Int) := by exact_mod_cast hn_pos
    -- Reshape: .rand #n () = Ectx.fill [] (.rand #n ()).
    have hfill_emp : Exp.rand (.lit (.int (n : Int))) (.lit .unit) =
      Ectx.fill [] (Exp.rand (.lit (.int (n : Int))) (.lit .unit)) := rfl
    rw [hfill_emp]
    iapply (refines_couple_rands_lr (E := ⊤) (K := []) (K' := []) (A := lrel_nat)
      (z := (n : Int)) (f := id)
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hnpos))
    iintro %m ⟨%Hm0, %Hmn⟩
    -- Goal: refines ⊤ ([].fill #m) ([].fill #(id m)) lrel_nat. id m = m.
    have hfill1 : Ectx.fill [] (Exp.lit (.int m)) = Exp.lit (.int m) := rfl
    have hfill2 : Ectx.fill [] (Exp.lit (.int (id m))) = Exp.lit (.int m) := rfl
    rw [hfill1, hfill2]
    -- Goal: refines ⊤ #m #m lrel_nat. Use refines_ret with v = ⟨#m, IsVal.lit⟩.
    -- But m : Int, and we need m = (some Nat : Int). We have 0 ≤ m, so m is Nat.
    iapply (refines_ret (e1 := Exp.lit (.int m)) (e2 := Exp.lit (.int m))
      (v1 := ⟨.lit (.int m), IsVal.lit⟩) (v2 := ⟨.lit (.int m), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    -- Goal: lrel_nat.car ⟨#m, _⟩ ⟨#m, _⟩ = ∃ k : Nat, ⌜#m = #(k:Int) ∧ #m = #(k:Int)⌝.
    unfold lrel_nat
    iexists m.toNat
    ipure_intro
    have hk : (m.toNat : Int) = m := Int.toNat_of_nonneg Hm0
    refine ⟨?_, ?_⟩ <;> rw [hk]

/-- `refines_rand_tape_int`: int-flavored labeled-rand compatibility. Takes
the bound at `lrel_int` (any integer) and concludes at `lrel_int`.
Case-splits on `0 < n`: positive uses the existing `wp_couple_rand_lbl_rand_lbl{,_wrong}`
flow; nonpos opens the tape invariant and uses `wp_rand_lbl_nonpos{,_r}`. -/
theorem refines_rand_tape_int {e1 e1' e2 e2' : Exp} :
    iprop(refines ⊤ e1 e1' lrel_int) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_int) := by
  show iprop(refines ⊤ e1 e1' lrel_int) ⊢@{IProp GF}
    iprop(refines ⊤ e2 e2' lrel_tape -∗
      refines ⊤ (Ectx.fill [EctxItem.randR e1] e2)
                (Ectx.fill [EctxItem.randR e1'] e2') lrel_int)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.randR e1] [EctxItem.randR e1']
    (A := lrel_tape)) $$ [IH2]
  · iexact IH2
  iintro %w %w' HTapeRel
  ihave HTapeEx := lrel_tape_unfold _ _ $$ HTapeRel
  icases HTapeEx with ⟨%α, %α', %N, %Hw, %Hw', #Hinv⟩
  have hfillR_to_L : Ectx.fill [EctxItem.randR e1] w.1 =
    Ectx.fill [EctxItem.randL w] e1 := rfl
  have hfillR_to_L' : Ectx.fill [EctxItem.randR e1'] w'.1 =
    Ectx.fill [EctxItem.randL w'] e1' := rfl
  rw [hfillR_to_L, hfillR_to_L']
  iapply (refines_bind [EctxItem.randL w] [EctxItem.randL w']
    (A := lrel_int)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HInt
  ihave HIntEx := lrel_int_unfold v v' $$ HInt
  icases HIntEx with ⟨%n, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 := rfl
  rw [hfillv, hfillv', Hv, Hv', Hw, Hw']
  by_cases hnpos : 0 < n
  · -- Positive bound: same proof as refines_rand_tape, parameterized over lrel_int.
    have hfill_empty : Exp.rand (.lit (.int n)) (.lit (.lbl α)) =
      Ectx.fill [] (Exp.rand (.lit (.int n)) (.lit (.lbl α))) := rfl
    rw [hfill_empty]
    iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (K := []) (e1 := Exp.rand (.lit (.int n)) (.lit (.lbl α)))
      (t := Exp.rand (.lit (.int n)) (.lit (.lbl α')))
      (A := lrel_int) (OpenInv.of_atomic (Atomic.rand_lbl n α)))
    iintro %K' Hr
    have hsub : (↑(logN.@ ((α, α') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
      fun _ _ => CoPset.mem_full
    imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
    ihave HInvBody1 := later_sep.mp $$ HInvBody
    icases HInvBody1 with ⟨HαL, Hα'L⟩
    imod HαL with Hα
    imod Hα'L with Hα'
    imodintro
    ihave HαN := app_empty_to_natTape (GF := GF) (l := α) (z := N) $$ Hα
    ihave Hα'N := spec_empty_to_natTape (GF := GF) (l := α') (z := N) $$ Hα'
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
      isplitl [Hr]; · iexact Hr
      iintro %m ⟨HαRet, Hα'Ret, HKRes, %Hmr⟩
      ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
      ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
      ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
          specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
      · iintro !>
        isplitl [HαBack]; · iexact HαBack
        iexact Hα'Back
      ispecialize Hclose $$ HCloseArg
      imod Hclose with _
      imodintro
      iexists (.lit (.int (id m)))
      isplitl [HKRes]; · iexact HKRes
      iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int m)))
        (e2 := Exp.lit (.int (id m)))
        (v1 := ⟨.lit (.int m), IsVal.lit⟩) (v2 := ⟨.lit (.int (id m)), IsVal.lit⟩)
        (hv1 := rfl) (hv2 := rfl))
      imodintro
      unfold lrel_int
      iexists m
      ipure_intro
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
      isplitl [Hr]; · iexact Hr
      iintro %m ⟨HαRet, Hα'Ret, HKRes, %Hmr⟩
      ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
      ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
      ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
          specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
      · iintro !>
        isplitl [HαBack]; · iexact HαBack
        iexact Hα'Back
      ispecialize Hclose $$ HCloseArg
      imod Hclose with _
      imodintro
      iexists (.lit (.int (id m)))
      isplitl [HKRes]; · iexact HKRes
      iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int m)))
        (e2 := Exp.lit (.int (id m)))
        (v1 := ⟨.lit (.int m), IsVal.lit⟩) (v2 := ⟨.lit (.int (id m)), IsVal.lit⟩)
        (hv1 := rfl) (hv2 := rfl))
      imodintro
      unfold lrel_int
      iexists m
      ipure_intro
      exact ⟨rfl, rfl⟩
  · -- Nonpositive bound: open invariant, both sides step deterministically to -1.
    have hfill_empty : Exp.rand (.lit (.int n)) (.lit (.lbl α)) =
      Ectx.fill [] (Exp.rand (.lit (.int n)) (.lit (.lbl α))) := rfl
    rw [hfill_empty]
    iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (K := []) (e1 := Exp.rand (.lit (.int n)) (.lit (.lbl α)))
      (t := Exp.rand (.lit (.int n)) (.lit (.lbl α')))
      (A := lrel_int) (OpenInv.of_atomic (Atomic.rand_lbl n α)))
    iintro %K' Hr
    have hsub : (↑(logN.@ ((α, α') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
      fun _ _ => CoPset.mem_full
    imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
    ihave HInvBody1 := later_sep.mp $$ HInvBody
    icases HInvBody1 with ⟨HαL, Hα'L⟩
    imod HαL with Hα
    imod Hα'L with Hα'
    imodintro
    -- Step the spec side first via wp_rand_lbl_nonpos_r.
    iapply (wp_rand_lbl_nonpos_r K' (l := α') (z := n) (N := N) hnpos)
    isplitl [Hr]; · iexact Hr
    isplitl [Hα']; · iexact Hα'
    iintro Hα'New HKRes
    -- Now step the LHS via wp_rand_lbl_nonpos.
    iapply (wp_rand_lbl_nonpos (l := α) (z := n) (N := N) hnpos)
    isplitl [Hα]; · iexact Hα
    iintro HαNew
    -- Close the invariant.
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
        specTapesFrag α' ⟨N, []⟩)) $$ [HαNew Hα'New]
    · iintro !>
      isplitl [HαNew]; · iexact HαNew
      iexact Hα'New
    ispecialize Hclose $$ HCloseArg
    imod Hclose with _
    imodintro
    iexists (.lit (.int (-1)))
    isplitl [HKRes]; · iexact HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int (-1))))
      (e2 := Exp.lit (.int (-1)))
      (v1 := ⟨.lit (.int (-1)), IsVal.lit⟩) (v2 := ⟨.lit (.int (-1)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_int
    iexists (-1)
    ipure_intro
    exact ⟨rfl, rfl⟩

/-- `refines_rand_unit_int`: int-flavored unit-rand compatibility. Takes the
bound at `lrel_int` (any integer) and concludes at `lrel_int`. Case-splits
on `0 < n`: positive lifts to `lrel_pos_nat`+`refines_rand_unit`+widening;
nonpos uses degenerate dirac-(-1) coupling via `wp_rand_nonpos`/`_r`. -/
theorem refines_rand_unit_int {e e' : Exp} :
    iprop(refines ⊤ e e' lrel_int)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e)
          (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e')
          lrel_int := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    (A := lrel_int)) $$ [IH]
  · iexact IH
  iintro %v %v' HInt
  ihave HIntEx := lrel_int_unfold v v' $$ HInt
  icases HIntEx with ⟨%n, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v.1 =
      Exp.rand v.1 (.lit .unit) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v'.1 =
      Exp.rand v'.1 (.lit .unit) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  by_cases hnpos : 0 < n
  · -- Positive bound: use refines_couple_rands_lr at lrel_int.
    have hfill_emp : Exp.rand (.lit (.int n)) (.lit .unit) =
      Ectx.fill [] (Exp.rand (.lit (.int n)) (.lit .unit)) := rfl
    rw [hfill_emp]
    iapply (refines_couple_rands_lr (E := ⊤) (K := []) (K' := []) (A := lrel_int)
      (z := n) (f := id)
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hnpos))
    iintro %m _
    have hfill1 : Ectx.fill [] (Exp.lit (.int m)) = Exp.lit (.int m) := rfl
    have hfill2 : Ectx.fill [] (Exp.lit (.int (id m))) = Exp.lit (.int m) := rfl
    rw [hfill1, hfill2]
    iapply (refines_ret (e1 := Exp.lit (.int m)) (e2 := Exp.lit (.int m))
      (v1 := ⟨.lit (.int m), IsVal.lit⟩) (v2 := ⟨.lit (.int m), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_int
    iexists m
    ipure_intro
    exact ⟨rfl, rfl⟩
  · -- Nonpositive bound: both sides step to dirac -1.
    unfold refines
    iintro %K %ε HK Hna Herr Hpos
    -- Step the spec side first via wp_rand_nonpos_r.
    iapply (wp_rand_nonpos_r K hnpos)
    isplitl [HK]; · iexact HK
    iintro HK'
    -- Now step the LHS via wp_rand_nonpos.
    iapply (wp_rand_nonpos hnpos)
    iexists ⟨.lit (.int (-1)), IsVal.lit⟩
    iexists ε
    isplitl [HK']; · iexact HK'
    isplitl [Hna]; · iexact Hna
    isplitl [Herr]; · iexact Herr
    isplitl [Hpos]; · iexact Hpos
    unfold lrel_int
    iexists (-1)
    ipure_intro
    exact ⟨rfl, rfl⟩

end Compatibility

end ProbLang
