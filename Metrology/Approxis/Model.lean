module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Iris.Instances.Lib.NaInvariants
public import Iris.Instances.Lib.Invariants

@[expose] public section

set_option linter.discrete false

/-!
# Semantic Model

Semantic model for the binary logical relation: `ApproxisRGS`, `lrel`,
`refines`, and type constructors.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

/-! ## `Pos.Countable` instances for namespace indexing -/

theorem Pos.toNat_succ (p : Pos) : p.succ.toNat = p.toNat + 1 := by
  induction p with
  | xH => rfl
  | xI p ih => show 2 * p.succ.toNat = _; rw [ih]; simp [Pos.toNat]; ring
  | xO p => show 2 * p.toNat + 1 = _; simp [Pos.toNat]

theorem Pos.toNat_ofNat (n : Nat) : (Pos.ofNat n).toNat = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Pos.ofNat, Pos.toNat_succ, ih]

instance : Pos.Countable Nat where
  encode n := Pos.ofNat n
  decode p := some (p.toNat - 1)
  decode_encode n := by
    congr 1
    rw [Pos.toNat_ofNat]; omega

/-- Encode `Int` into `Nat` via the standard zigzag: `n ≥ 0 ↦ 2n`, `n < 0 ↦ -2n - 1`. -/
instance : Pos.Countable Int where
  encode z :=
    Pos.Countable.encode (A := Nat)
      (if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1)
  decode p := (Pos.Countable.decode (A := Nat) p).bind fun k =>
    some (if k % 2 = 0 then (k / 2 : Int) else -((k - 1) / 2 : Int) - 1)
  decode_encode z := by
    show Option.bind
      (Pos.Countable.decode (A := Nat)
        (Pos.Countable.encode (A := Nat)
          (if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1))) _ = _
    rw [Pos.Countable.decode_encode]
    show (Option.bind (some _) _ : Option Int) = _
    rw [Option.bind_some]
    by_cases hz : 0 ≤ z
    · rw [if_pos hz]
      have hmod : (2 * z.toNat) % 2 = 0 := Nat.mul_mod_right 2 _
      rw [if_pos hmod]
      have htn : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
      have : (((2 * z.toNat : Nat) : Int) / 2) = z := by
        push_cast; rw [Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]; exact htn
      rw [this]
    · rw [if_neg hz]
      have hmod : (2 * (-z - 1).toNat + 1) % 2 ≠ 0 := by
        intro h; omega
      rw [if_neg hmod]
      have hnn : (0 : Int) ≤ -z - 1 := by omega
      have htn : ((-z - 1).toNat : Int) = -z - 1 := Int.toNat_of_nonneg hnn
      have hd : ((((2 * (-z - 1).toNat + 1 : Nat) : Int) - 1) / 2) = -z - 1 := by
        push_cast
        rw [show (2 * ((-z - 1).toNat : Int) + 1 - 1) = 2 * (-z - 1) by rw [htn]; ring]
        rw [Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]
      rw [hd]
      congr 1; omega

instance {A B : Type} [Pos.Countable A] [Pos.Countable B] : Pos.Countable (A × B) where
  encode p := Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]
  decode p := match Pos.unflatten p with
    | some [a, b] =>
      (Pos.Countable.decode a).bind fun x =>
      (Pos.Countable.decode b).bind fun y =>
      some (x, y)
    | _ => none
  decode_encode p := by
    show (match Pos.unflatten
        (Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]) with
      | _ => _) = _
    rw [Pos.unflatten_flatten]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.1)) _ = _
    rw [Pos.Countable.decode_encode]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.2)) _ = _
    rw [Pos.Countable.decode_encode]
    rfl

/-! ## Log-relation namespace -/

def logN : Namespace := nroot.@ (1 : Pos)

/-! ## `ApproxisRGS` ghost-state bundle -/

class ApproxisRGS (rT : Type _) [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (hlc : outParam Bool) (GF : BundledGFunctors) where
  approxisGS : ApproxisGS rT hlc GF
  naInvG     : NaInvG GF
  nais       : NaInvPoolName

attribute [reducible, instance] ApproxisRGS.approxisGS ApproxisRGS.naInvG

/-! ## Logical relation type -/

structure lrel (rT : Type _) (GF : BundledGFunctors) where
  car : Val rT → Val rT → IProp GF
  persistent v1 v2 : Persistent (car v1 v2)
  closed v1 v2 : car v1 v2 ⊢@{IProp GF} iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝)

attribute [instance] lrel.persistent

instance {GF} : CoeFun (lrel rT GF) (fun _ => Val rT → Val rT → IProp GF) := ⟨lrel.car⟩

/-! ## OFE/COFE structure on `lrel` -/

instance {GF : BundledGFunctors} : OFE (lrel rT GF) where
  Equiv A B := ∀ v1 v2, A.car v1 v2 ≡ B.car v1 v2
  Dist n A B := ∀ v1 v2, A.car v1 v2 ≡{n}≡ B.car v1 v2
  dist_eqv := {
    refl _ _ _ := dist_eqv.refl _
    symm h v1 v2 := dist_eqv.symm (h v1 v2)
    trans h1 h2 v1 v2 := dist_eqv.trans (h1 v1 v2) (h2 v1 v2)
  }
  equiv_dist := by
    intro A B
    refine ⟨fun h n v1 v2 => Equiv.dist (h v1 v2), fun h v1 v2 => ?_⟩
    exact OFE.equiv_dist.mpr fun n => h n v1 v2
  dist_lt hd hmn v1 v2 := OFE.dist_lt (hd v1 v2) hmn

/-- Project an `lrel`-valued chain into the underlying function-space chain. -/
noncomputable def lrel.toFunChain {GF : BundledGFunctors}
    (c : Chain (lrel rT GF)) : Chain (Val rT → Val rT → IProp GF) where
  chain k := (c.chain k).car
  cauchy h := (c.cauchy h : _)

noncomputable instance {GF : BundledGFunctors} : IsCOFE (lrel rT GF) where
  compl c :=
    let carC : Val rT → Val rT → IProp GF := IsCOFE.compl (lrel.toFunChain c)
    { car := carC
      persistent := fun v1 v2 => by
        have hk : ∀ k, (c.chain k).car v1 v2 ⊢ iprop(<pers> (c.chain k).car v1 v2) :=
          fun k => ((c.chain k).persistent v1 v2).persistent
        refine ⟨?_⟩
        have hne_Φ : OFE.NonExpansive
          (fun f : Val rT → Val rT → IProp GF => f v1 v2) :=
          ⟨fun _ _ _ hfg => hfg v1 v2⟩
        have hne_Ψ : OFE.NonExpansive
          (fun f : Val rT → Val rT → IProp GF => iprop(<pers> f v1 v2)) :=
          ⟨fun _ _ _ hfg => persistently_ne.ne (hfg v1 v2)⟩
        exact Iris.BI.LimitPreserving.entails (Φne := hne_Φ) (Ψne := hne_Ψ)
          (fun f => f v1 v2) (fun f => iprop(<pers> f v1 v2))
          (lrel.toFunChain c) hk
      closed := fun v1 v2 => by
        have hk : ∀ k, (c.chain k).car v1 v2 ⊢
            iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ : IProp GF) :=
          fun k => (c.chain k).closed v1 v2
        have hne_Φ : OFE.NonExpansive
          (fun f : Val rT → Val rT → IProp GF => f v1 v2) :=
          ⟨fun _ _ _ hfg => hfg v1 v2⟩
        have hne_Ψ : OFE.NonExpansive
          (fun _ : Val rT → Val rT → IProp GF =>
            iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ : IProp GF)) :=
          ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
        exact Iris.BI.LimitPreserving.entails (Φne := hne_Φ) (Ψne := hne_Ψ)
          (fun f => f v1 v2)
          (fun _ => iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ : IProp GF))
          (lrel.toFunChain c) hk }
  conv_compl {_ c} v1 v2 := IsCOFE.conv_compl (c := lrel.toFunChain c) v1 v2

instance {GF : BundledGFunctors} : Inhabited (lrel rT GF) where
  default :=
    { car := fun _ _ => iprop(False)
      persistent := fun _ _ => inferInstance
      closed := fun _ _ => Iris.BI.false_elim }

instance lrel.car_ne {GF : BundledGFunctors} (v1 v2 : Val rT) :
    OFE.NonExpansive (fun A : lrel rT GF => A.car v1 v2) where
  ne {_ _ _} hAB := hAB v1 v2

instance lrel.leibniz {GF : BundledGFunctors} : OFE.Leibniz (lrel rT GF) where
  eq_of_eqv {A B} hequiv := by
    obtain ⟨carA, persA, closA⟩ := A
    obtain ⟨carB, persB, closB⟩ := B
    have hcar : carA = carB := by
      funext v1 v2
      exact OFE.Leibniz.eq_of_eqv (hequiv v1 v2)
    subst hcar
    rfl

/-! ## `na_own` / `na_inv` abbreviations keyed on the pool name -/

section NaShorthand
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

@[reducible] noncomputable def naOwnP (E : CoPset) : IProp GF :=
  Iris.NonAtomicInvariant.own (GF := GF) (ApproxisRGS.nais (rT := rT) (hlc := hlc) GF) E

@[reducible] noncomputable def naInvP (N : Namespace) (P : IProp GF) : IProp GF :=
  Iris.NonAtomicInvariant.inv (GF := GF) (ApproxisRGS.nais (rT := rT) (hlc := hlc) GF) N P

@[reducible] noncomputable def naCloseP (P : IProp GF) (N : Namespace) (E : CoPset) : IProp GF :=
  iprop((▷ P) ∗ (naOwnP (rT := rT) (hlc := hlc) (SDiff.sdiff E ((↑N : CoPset) : CoPset))) ={⊤}=∗ naOwnP (rT := rT) (hlc := hlc) E)

end NaShorthand

/-! ## Refinement judgement -/

section Refines
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

noncomputable def refines (E : CoPset) (e e' : Exp rT) (A : lrel rT GF) : IProp GF :=
  iprop(∀ (K : Ectx rT) (ε : ENNReal),
    (⤇ (K.fill e')) -∗
    (naOwnP (rT := rT) (hlc := hlc) E) -∗
    (↯ ε) -∗
    (⌜ (0 : ENNReal) < ε ⌝) -∗
    wp ⊤ e (fun v => iprop(∃ (v' : Val rT) (ε' : ENNReal),
      (⤇ (K.fill v'.1)) ∗ (naOwnP (rT := rT) (hlc := hlc) ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v')))

/-- Bridge between the folded and unfolded form of `refines` for `iapply`/`iexact`. -/
theorem refines_unfold {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} :
    refines E e e' A ⊢@{IProp GF}
      iprop(∀ (K : Ectx rT) (ε : ENNReal),
        (⤇ (K.fill e')) -∗
        (naOwnP (rT := rT) (hlc := hlc) E) -∗
        (↯ ε) -∗
        (⌜ (0 : ENNReal) < ε ⌝) -∗
        wp ⊤ e (fun v => iprop(∃ (v' : Val rT) (ε' : ENNReal),
          (⤇ (K.fill v'.1)) ∗ (naOwnP (rT := rT) (hlc := hlc) ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v'))) :=
  BIBase.Entails.rfl

end Refines

/-! ## Notation for the refinement judgement -/

scoped notation:100 "REL " e1 " << " e2 " @ " E " : " A =>
  refines E e1 e2 A

scoped notation:100 "REL " e1 " << " e2 " : " A =>
  refines (⊤ : CoPset) e1 e2 A

/-! ## Simple lrel constructors -/

section SimpleLRels
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem lrel_closed_lit_pair (v1 v2 : Val rT) :
    iprop(⌜v1.1 = .lit .unit ∧ v2.1 = .lit .unit⌝ : IProp GF)
      ⊢@{IProp GF} iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝) := by
  iintro %h
  ipure_intro
  exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

noncomputable def lrel_unit : lrel rT GF where
  car v1 v2 := iprop(⌜ v1.1 = .lit .unit ∧ v2.1 = .lit .unit ⌝)
  persistent _ _ := inferInstance
  closed v1 v2 := lrel_closed_lit_pair v1 v2

noncomputable def lrel_bool : lrel rT GF where
  car v1 v2 := iprop(∃ b : Bool, ⌜ v1.1 = .lit (.bool b) ∧ v2.1 = .lit (.bool b) ⌝)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%b, %h⟩
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

noncomputable def lrel_nat : lrel rT GF where
  car v1 v2 := iprop(∃ n : Nat, ⌜ v1.1 = .lit (.int (n : Int)) ∧ v2.1 = .lit (.int (n : Int)) ⌝)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%n, %h⟩
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Both values are the same positive integer literal (`0 < n`). -/
noncomputable def lrel_pos_nat : lrel rT GF where
  car v1 v2 := iprop(∃ n : Nat, ⌜ 0 < n ∧
    v1.1 = .lit (.int (n : Int)) ∧ v2.1 = .lit (.int (n : Int)) ⌝)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%n, %h⟩
    ipure_intro
    exact ⟨h.2.1 ▸ Exp.lit_isClosedEmpty _, h.2.2 ▸ Exp.lit_isClosedEmpty _⟩

noncomputable def lrel_int : lrel rT GF where
  car v1 v2 := iprop(∃ n : Int, ⌜ v1.1 = .lit (.int n) ∧ v2.1 = .lit (.int n) ⌝)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%n, %h⟩
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

noncomputable def lrel_arr (A1 A2 : lrel rT GF) : lrel rT GF where
  car v1 v2 :=
    iprop((⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝) ∗
      □ (∀ (w1 w2 : Val rT), A1 w1 w2 -∗
        refines (⊤ : CoPset) (.app v1.1 w1.1) (.app v2.1 w2.1) A2))
  persistent _ _ := inferInstance
  closed _ _ := by iintro ⟨%h, _⟩; ipure_intro; exact h

noncomputable def lrel_prod (A B : lrel rT GF) : lrel rT GF where
  car v1 v2 :=
    iprop(∃ (a1 a2 b1 b2 : Val rT),
      (⌜ v1.1 = .pair a1.1 b1.1 ⌝) ∗
      (⌜ v2.1 = .pair a2.1 b2.1 ⌝) ∗
      A a1 a2 ∗ B b1 b2)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %hAcl := A.closed a1 a2 $$ HA
    ihave %hBcl := B.closed b1 b2 $$ HB
    ipure_intro
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [h1]
        exact Exp.IsLocallyClosed.pair hAcl.1.1 hBcl.1.1
      · rw [h1]; simp [Exp.fv]; exact ⟨hAcl.1.2, hBcl.1.2⟩
    · refine ⟨?_, ?_⟩
      · rw [h2]
        exact Exp.IsLocallyClosed.pair hAcl.2.1 hBcl.2.1
      · rw [h2]; simp [Exp.fv]; exact ⟨hAcl.2.2, hBcl.2.2⟩

noncomputable def lrel_sum (A B : lrel rT GF) : lrel rT GF where
  car v1 v2 :=
    iprop(∃ (w1 w2 : Val rT),
      ((⌜ v1.1 = .inl w1.1 ⌝) ∗ (⌜ v2.1 = .inl w2.1 ⌝) ∗ A w1 w2)
      ∨
      ((⌜ v1.1 = .inr w1.1 ⌝) ∗ (⌜ v2.1 = .inr w2.1 ⌝) ∗ B w1 w2))
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%w1, %w2, Hd⟩
    icases Hd with (⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩)
    · ihave %hAcl := A.closed w1 w2 $$ HA
      ipure_intro
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [h1]; exact Exp.IsLocallyClosed.inl hAcl.1.1
        · rw [h1]; simp [Exp.fv]; exact hAcl.1.2
      · refine ⟨?_, ?_⟩
        · rw [h2]; exact Exp.IsLocallyClosed.inl hAcl.2.1
        · rw [h2]; simp [Exp.fv]; exact hAcl.2.2
    · ihave %hBcl := B.closed w1 w2 $$ HB
      ipure_intro
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [h1]; exact Exp.IsLocallyClosed.inr hBcl.1.1
        · rw [h1]; simp [Exp.fv]; exact hBcl.1.2
      · refine ⟨?_, ?_⟩
        · rw [h2]; exact Exp.IsLocallyClosed.inr hBcl.2.1
        · rw [h2]; simp [Exp.fv]; exact hBcl.2.2

noncomputable def lrel_exists (C : lrel rT GF → lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop((⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝) ∗
    ∃ A : lrel rT GF, C A v1 v2)
  persistent _ _ := inferInstance
  closed _ _ := by iintro ⟨%h, _⟩; ipure_intro; exact h

/-- Universal over semantic types, uniform via `lrel_arr lrel_unit`. -/
noncomputable def lrel_forall (C : lrel rT GF → lrel rT GF) : lrel rT GF where
  car v1 v2 :=
    iprop(∀ (A : lrel rT GF), (lrel_arr lrel_unit (C A)).car v1 v2)
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro Hall
    ihave Hinst := Hall $$ %(default : lrel rT GF)
    iapply ((lrel_arr lrel_unit (C default)).closed v1 v2)
    iexact Hinst

/-- Trivial relation that relates everything that's closed. -/
noncomputable def lrel_true : lrel rT GF where
  car v1 v2 := iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝)
  persistent _ _ := inferInstance
  closed _ _ := BIBase.Entails.rfl

/-! ### Recursive lrel via `fixpoint` -/

/-- One-step unfolding of a recursive semantic type. Carries a closedness
conjunct so `interp_closed` can project it without `▷`-stripping. -/
noncomputable def lrelRec1 (C : lrel rT GF -n> lrel rT GF) (r : lrel rT GF) : lrel rT GF where
  car w1 w2 := iprop((⌜w1.1.isClosedEmpty ∧ w2.1.isClosedEmpty⌝) ∗
    ▷ (C r).car w1 w2)
  persistent _ _ := inferInstance
  closed _ _ := by iintro ⟨%h, _⟩; ipure_intro; exact h

instance lrelRec1_contractive (C : lrel rT GF -n> lrel rT GF) : OFE.Contractive (lrelRec1 C) where
  distLater_dist {n P Q} hPQ w1 w2 := by
    show iprop(_ ∗ ▷ _) ≡{n}≡ iprop(_ ∗ ▷ _)
    refine sep_ne.ne .rfl ?_
    refine Contractive.distLater_dist (f := (Iris.BI.later : IProp GF → IProp GF)) ?_
    intro k hk
    have hk' : P ≡{k}≡ Q := hPQ k hk
    exact C.ne.ne hk' w1 w2

noncomputable def lrelRec1Hom (C : lrel rT GF -n> lrel rT GF) : lrel rT GF -c> lrel rT GF where
  f := lrelRec1 C
  ne := inferInstance
  contractive := inferInstance

noncomputable def lrel_rec (C : lrel rT GF -n> lrel rT GF) : lrel rT GF :=
  fixpoint (lrelRec1 C)

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem lrel_rec_unfold (C : lrel rT GF -n> lrel rT GF) :
    lrel_rec C ≡ lrelRec1 C (lrel_rec C) :=
  fixpoint_unfold (lrelRec1Hom C)

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem lrel_rec_ne {n : Nat} {C1 C2 : lrel rT GF -n> lrel rT GF}
    (hC : ∀ A : lrel rT GF, C1 A ≡{n}≡ C2 A) :
    lrel_rec C1 ≡{n}≡ lrel_rec C2 := by
  induction n generalizing C1 C2 with
  | zero =>
    intro w1 w2
    have h1 : (lrel_rec C1).car w1 w2 ≡{0}≡ (lrelRec1 C1 (lrel_rec C1)).car w1 w2 :=
      Equiv.dist (lrel_rec_unfold C1) w1 w2
    have h2 : (lrelRec1 C2 (lrel_rec C2)).car w1 w2 ≡{0}≡ (lrel_rec C2).car w1 w2 :=
      (Equiv.dist (lrel_rec_unfold C2) w1 w2).symm
    have hmid : (lrelRec1 C1 (lrel_rec C1)).car w1 w2 ≡{0}≡
                (lrelRec1 C2 (lrel_rec C2)).car w1 w2 := by
      show iprop(_ ∗ ▷ (C1 (lrel_rec C1)).car w1 w2) ≡{0}≡
           iprop(_ ∗ ▷ (C2 (lrel_rec C2)).car w1 w2)
      refine sep_ne.ne .rfl ?_
      exact Contractive.zero (f := (Iris.BI.later : IProp GF → IProp GF))
    exact h1.trans (hmid.trans h2)
  | succ m ih =>
    intro w1 w2
    have h1 : (lrel_rec C1).car w1 w2 ≡{m+1}≡ (lrelRec1 C1 (lrel_rec C1)).car w1 w2 :=
      Equiv.dist (lrel_rec_unfold C1) w1 w2
    have h2 : (lrelRec1 C2 (lrel_rec C2)).car w1 w2 ≡{m+1}≡ (lrel_rec C2).car w1 w2 :=
      (Equiv.dist (lrel_rec_unfold C2) w1 w2).symm
    have hmid : (lrelRec1 C1 (lrel_rec C1)).car w1 w2 ≡{m+1}≡
                (lrelRec1 C2 (lrel_rec C2)).car w1 w2 := by
      show iprop(_ ∗ ▷ (C1 (lrel_rec C1)).car w1 w2) ≡{m+1}≡
           iprop(_ ∗ ▷ (C2 (lrel_rec C2)).car w1 w2)
      refine sep_ne.ne .rfl ?_
      refine Contractive.succ (f := (Iris.BI.later : IProp GF → IProp GF)) ?_
      have ih' : lrel_rec C1 ≡{m}≡ lrel_rec C2 :=
        ih (fun A => (hC A).lt (Nat.lt_succ_self m))
      have step1 : (C1 (lrel_rec C1)).car w1 w2 ≡{m}≡ (C1 (lrel_rec C2)).car w1 w2 :=
        C1.ne.ne ih' w1 w2
      have step2 : (C1 (lrel_rec C2)).car w1 w2 ≡{m}≡ (C2 (lrel_rec C2)).car w1 w2 :=
        (hC (lrel_rec C2) w1 w2).lt (Nat.lt_succ_self m)
      exact step1.trans step2
    exact h1.trans (hmid.trans h2)

/-! ### Nonexpansive instances on simple lrel constructors -/

instance lrel_prod_ne_2 : OFE.NonExpansive₂ (lrel_prod (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    refine exists_ne fun a1 => ?_
    refine exists_ne fun a2 => ?_
    refine exists_ne fun b1 => ?_
    refine exists_ne fun b2 => ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    exact sep_ne.ne (hA a1 a2) (hB b1 b2)

instance lrel_sum_ne_2 : OFE.NonExpansive₂ (lrel_sum (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    refine exists_ne fun w1 => ?_
    refine exists_ne fun w2 => ?_
    refine or_ne.ne ?_ ?_
    · refine sep_ne.ne .rfl ?_
      exact sep_ne.ne .rfl (hA w1 w2)
    · refine sep_ne.ne .rfl ?_
      exact sep_ne.ne .rfl (hB w1 w2)

/-- `refines` is nonexpansive in its relation argument. -/
theorem refines_ne {E : CoPset} {e e' : Exp rT} {n : Nat} {A B : lrel rT GF}
    (h : A ≡{n}≡ B) : refines E e e' A ≡{n}≡ refines E e e' B := by
  unfold refines
  refine forall_ne fun K => ?_
  refine forall_ne fun ε => ?_
  refine wand_ne.ne .rfl ?_
  refine wand_ne.ne .rfl ?_
  refine wand_ne.ne .rfl ?_
  refine wand_ne.ne .rfl ?_
  refine NonExpansive.ne (f := wp ⊤ e) ?_
  intro v
  refine exists_ne fun v' => exists_ne fun ε' => ?_
  refine sep_ne.ne .rfl ?_
  refine sep_ne.ne .rfl ?_
  refine sep_ne.ne .rfl ?_
  refine sep_ne.ne .rfl ?_
  exact h v v'

instance lrel_arr_ne_2 : OFE.NonExpansive₂ (lrel_arr (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    refine sep_ne.ne .rfl ?_
    refine intuitionistically_ne.ne ?_
    refine forall_ne fun w1 => ?_
    refine forall_ne fun w2 => ?_
    exact wand_ne.ne (hA w1 w2) (refines_ne hB)

/-- `refines` respects equivalence of relations. Mirrors `refines_proper`
(model.v:96–98). -/
theorem refines_proper {E : CoPset} {e e' : Exp rT} {A B : lrel rT GF}
    (h : A ≡ B) : refines E e e' A ≡ refines E e e' B :=
  OFE.equiv_dist.mpr fun n => refines_ne (OFE.equiv_dist.mp h n)

/-- `lrel_ref A`: reference values whose contents are related by `A`,
guarded by an invariant at the log-namespace. Mirrors `lrel_ref` (model.v:108–110). -/
noncomputable def lrel_ref (A : lrel rT GF) : lrel rT GF where
  car v1 v2 :=
    iprop(∃ (l1 l2 : Loc),
      (⌜ v1.1 = .lit (.loc l1) ⌝) ∗ (⌜ v2.1 = .lit (.loc l2) ⌝) ∗
      Iris.inv (logN.@ ((l1, l2) : Loc × Loc))
        (iprop(∃ (w1 w2 : Val rT), (appHeapFrag l1 w1) ∗ (specHeapFrag l2 w2) ∗ A w1 w2)))
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%l1, %l2, %h1, %h2, _⟩
    ipure_intro
    exact ⟨h1 ▸ Exp.lit_isClosedEmpty _, h2 ▸ Exp.lit_isClosedEmpty _⟩

/-- `lrel_tape`: tape values whose contents are empty and sampled from the
same finite range. Mirrors `lrel_tape` (model.v:113–115). -/
noncomputable def lrel_tape : lrel rT GF where
  car v1 v2 :=
    iprop(∃ (α1 α2 : Loc) (z : Int),
      (⌜ v1.1 = .lit (.lbl α1) ⌝) ∗ (⌜ v2.1 = .lit (.lbl α2) ⌝) ∗
      Iris.inv (logN.@ ((α1, α2) : Loc × Loc))
        (iprop((appTapesFrag α1 ⟨z, []⟩) ∗ (specTapesFrag α2 ⟨z, []⟩))))
  persistent _ _ := inferInstance
  closed v1 v2 := by
    iintro ⟨%α1, %α2, %z, %h1, %h2, _⟩
    ipure_intro
    exact ⟨h1 ▸ Exp.lit_isClosedEmpty _, h2 ▸ Exp.lit_isClosedEmpty _⟩

/-- `lrel_ref` is nonexpansive in its content type. -/
instance lrel_ref_ne : OFE.NonExpansive (lrel_ref (rT := rT) (GF := GF)) where
  ne {n A B} hAB v1 v2 := by
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    refine exists_ne fun l1 => ?_
    refine exists_ne fun l2 => ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    refine (Iris.inv_ne _).ne ?_
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    refine exists_ne fun w1 => ?_
    refine exists_ne fun w2 => ?_
    refine sep_ne.ne .rfl ?_
    refine sep_ne.ne .rfl ?_
    exact hAB w1 w2

/-- `lrel_forall` is nonexpansive in the body function (pointwise-`≡{n}≡`). -/
theorem lrel_forall_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_forall C1 : lrel rT GF) ≡{n}≡ lrel_forall C2 := by
  intro v1 v2
  show iprop(∀ _, _) ≡{n}≡ iprop(∀ _, _)
  refine forall_ne fun A => ?_
  exact lrel_arr_ne_2.ne .rfl (h A) v1 v2

omit [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem lrel_exists_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_exists C1 : lrel rT GF) ≡{n}≡ lrel_exists C2 := by
  intro v1 v2
  show iprop(_ ∗ ∃ _, _) ≡{n}≡ iprop(_ ∗ ∃ _, _)
  refine sep_ne.ne .rfl ?_
  refine exists_ne fun A => ?_
  exact h A v1 v2

end SimpleLRels

/-! ### Semantic property lemmas -/

section SemtypesProperties
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

instance : Inhabited (Val rT) := ⟨⟨.lit .unit, .lit⟩⟩

/-- Reference type is functional in the program-side location: if `#l` is
related to both `#l1` and `#l2` at `ref A`, then `l1 = l2`. -/
theorem interp_ref_funct {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢@{IProp GF} (lrel_ref A).car ⟨.lit (.loc l), .lit⟩ ⟨.lit (.loc l1), .lit⟩ -∗
        (lrel_ref A).car ⟨.lit (.loc l), .lit⟩ ⟨.lit (.loc l2), .lit⟩ -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro H1 H2
  icases H1 with ⟨%l', %l1', %Heq1, %Heq1', Hinv1⟩
  icases H2 with ⟨%l'', %l2', %Heq2, %Heq2', Hinv2⟩
  have heq_l : l = l' := by simp at Heq1; exact Heq1
  have heq_l' : l = l'' := by simp at Heq2; exact Heq2
  have heq_l1 : l1 = l1' := by simp at Heq1'; exact Heq1'
  have heq_l2 : l2 = l2' := by simp at Heq2'; exact Heq2'
  subst heq_l' heq_l1 heq_l2
  subst heq_l
  by_cases h : l1 = l2
  · imodintro; ipure_intro; exact h
  · have hN_disj : logN.@ ((l, l1) : Loc × Loc) ## logN.@ ((l, l2) : Loc × Loc) :=
      ndot_ne_disjoint _ (fun heq => h (by injection heq))
    have h1 : (↑(logN.@ ((l, l1) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2 : (↑(logN.@ ((l, l2) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2' : (↑(logN.@ ((l, l2) : Loc × Loc)) : CoPset) ⊆
               E \ (↑(logN.@ ((l, l1) : Loc × Loc)) : CoPset) := by
      intro p hp
      rw [CoPset.in_diff]
      exact ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
    imod Iris.inv_acc E _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
    imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
    ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
    · ihave HP1a := later_exists.mpr $$ HP1
      icases HP1a with ⟨%wa1, HP1b⟩
      ihave HP1c := later_exists.mpr $$ HP1b
      icases HP1c with ⟨%ws1, HP1d⟩
      ihave HP1e := later_sep.mp $$ HP1d
      icases HP1e with ⟨Hl1L, _⟩
      ihave HP2a := later_exists.mpr $$ HP2
      icases HP2a with ⟨%wa2, HP2b⟩
      ihave HP2c := later_exists.mpr $$ HP2b
      icases HP2c with ⟨%ws2, HP2d⟩
      ihave HP2e := later_sep.mp $$ HP2d
      icases HP2e with ⟨Hl2L, _⟩
      inext
      iapply appHeapFrag_valid_2 $$ Hl1L Hl2L
    iapply IsExcept0.is_except0
    unfold BIBase.except0
    iapply BI.or_intro_l
    iexact HbotLater

/-- Reference type is injective on the program-side location: if both `#l1`
and `#l2` are related to `#l` at `ref A`, then `l1 = l2`. -/
theorem interp_ref_inj {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢@{IProp GF} (lrel_ref A).car ⟨.lit (.loc l1), .lit⟩ ⟨.lit (.loc l), .lit⟩ -∗
        (lrel_ref A).car ⟨.lit (.loc l2), .lit⟩ ⟨.lit (.loc l), .lit⟩ -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro H1 H2
  icases H1 with ⟨%l1', %l', %Heq1, %Heq1', Hinv1⟩
  icases H2 with ⟨%l2', %l'', %Heq2, %Heq2', Hinv2⟩
  have heq_l1 : l1 = l1' := by simp at Heq1; exact Heq1
  have heq_l : l = l' := by simp at Heq1'; exact Heq1'
  have heq_l2 : l2 = l2' := by simp at Heq2; exact Heq2
  have heq_l' : l = l'' := by simp at Heq2'; exact Heq2'
  subst heq_l1 heq_l heq_l2
  subst heq_l'
  by_cases h : l1 = l2
  · imodintro; ipure_intro; exact h
  · have hN_disj :
        logN.@ ((l1, l) : Loc × Loc) ## logN.@ ((l2, l) : Loc × Loc) :=
      ndot_ne_disjoint _ (fun heq => h (by injection heq))
    have h1 : (↑(logN.@ ((l1, l) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2 : (↑(logN.@ ((l2, l) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2' : (↑(logN.@ ((l2, l) : Loc × Loc)) : CoPset) ⊆
               E \ (↑(logN.@ ((l1, l) : Loc × Loc)) : CoPset) := by
      intro p hp
      rw [CoPset.in_diff]
      exact ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
    imod Iris.inv_acc E _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
    imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
    ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
    · ihave HP1a := later_exists.mpr $$ HP1
      icases HP1a with ⟨%wa1, HP1b⟩
      ihave HP1c := later_exists.mpr $$ HP1b
      icases HP1c with ⟨%ws1, HP1d⟩
      ihave HP1e := later_sep.mp $$ HP1d
      icases HP1e with ⟨_, HP1f⟩
      ihave HP1g := later_sep.mp $$ HP1f
      icases HP1g with ⟨Hs1L, _⟩
      ihave HP2a := later_exists.mpr $$ HP2
      icases HP2a with ⟨%wa2, HP2b⟩
      ihave HP2c := later_exists.mpr $$ HP2b
      icases HP2c with ⟨%ws2, HP2d⟩
      ihave HP2e := later_sep.mp $$ HP2d
      icases HP2e with ⟨_, HP2f⟩
      ihave HP2g := later_sep.mp $$ HP2f
      icases HP2g with ⟨Hs2L, _⟩
      inext
      iapply specHeapFrag_valid_2 $$ Hs1L Hs2L
    iapply IsExcept0.is_except0
    unfold BIBase.except0
    iapply BI.or_intro_l
    iexact HbotLater

/-- Tape type is functional in the program-side location. -/
theorem interp_tape_funct {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢@{IProp GF} (lrel_tape (rT := rT) (GF := GF)).car ⟨.lit (.lbl l), .lit⟩ ⟨.lit (.lbl l1), .lit⟩ -∗
        (lrel_tape (rT := rT) (GF := GF)).car ⟨.lit (.lbl l), .lit⟩ ⟨.lit (.lbl l2), .lit⟩ -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro H1 H2
  icases H1 with ⟨%l', %l1', %z1, %Heq1, %Heq1', Hinv1⟩
  icases H2 with ⟨%l'', %l2', %z2, %Heq2, %Heq2', Hinv2⟩
  have heq_l : l = l' := by simp at Heq1; exact Heq1
  have heq_l' : l = l'' := by simp at Heq2; exact Heq2
  have heq_l1 : l1 = l1' := by simp at Heq1'; exact Heq1'
  have heq_l2 : l2 = l2' := by simp at Heq2'; exact Heq2'
  subst heq_l' heq_l1 heq_l2 heq_l
  by_cases h : l1 = l2
  · imodintro; ipure_intro; exact h
  · have hN_disj : logN.@ ((l, l1) : Loc × Loc) ## logN.@ ((l, l2) : Loc × Loc) :=
      ndot_ne_disjoint _ (fun heq => h (by injection heq))
    have h1 : (↑(logN.@ ((l, l1) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2 : (↑(logN.@ ((l, l2) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2' : (↑(logN.@ ((l, l2) : Loc × Loc)) : CoPset) ⊆
               E \ (↑(logN.@ ((l, l1) : Loc × Loc)) : CoPset) := by
      intro p hp
      rw [CoPset.in_diff]
      exact ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
    imod Iris.inv_acc E _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
    imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
    ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
    · ihave HP1e := later_sep.mp $$ HP1
      icases HP1e with ⟨Hl1L, _⟩
      ihave HP2e := later_sep.mp $$ HP2
      icases HP2e with ⟨Hl2L, _⟩
      inext
      iapply appTapesFrag_valid_2 $$ Hl1L Hl2L
    iapply IsExcept0.is_except0
    unfold BIBase.except0
    iapply BI.or_intro_l
    iexact HbotLater

/-- Tape type is injective on the program-side location. -/
theorem interp_tape_inj {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢@{IProp GF} (lrel_tape (rT := rT) (GF := GF)).car ⟨.lit (.lbl l1), .lit⟩ ⟨.lit (.lbl l), .lit⟩ -∗
        (lrel_tape (rT := rT) (GF := GF)).car ⟨.lit (.lbl l2), .lit⟩ ⟨.lit (.lbl l), .lit⟩ -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro H1 H2
  icases H1 with ⟨%l1', %l', %z1, %Heq1, %Heq1', Hinv1⟩
  icases H2 with ⟨%l2', %l'', %z2, %Heq2, %Heq2', Hinv2⟩
  have heq_l1 : l1 = l1' := by simp at Heq1; exact Heq1
  have heq_l : l = l' := by simp at Heq1'; exact Heq1'
  have heq_l2 : l2 = l2' := by simp at Heq2; exact Heq2
  have heq_l' : l = l'' := by simp at Heq2'; exact Heq2'
  subst heq_l1 heq_l heq_l2
  subst heq_l'
  by_cases h : l1 = l2
  · imodintro; ipure_intro; exact h
  · have hN_disj :
        logN.@ ((l1, l) : Loc × Loc) ## logN.@ ((l2, l) : Loc × Loc) :=
      ndot_ne_disjoint _ (fun heq => h (by injection heq))
    have h1 : (↑(logN.@ ((l1, l) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2 : (↑(logN.@ ((l2, l) : Loc × Loc)) : CoPset) ⊆ E :=
      LawfulSet.subset_trans (nclose_subseteq _ _) HE
    have h2' : (↑(logN.@ ((l2, l) : Loc × Loc)) : CoPset) ⊆
               E \ (↑(logN.@ ((l1, l) : Loc × Loc)) : CoPset) := by
      intro p hp
      rw [CoPset.in_diff]
      exact ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
    imod Iris.inv_acc E _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
    imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
    ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
    · ihave HP1e := later_sep.mp $$ HP1
      icases HP1e with ⟨_, Hs1L⟩
      ihave HP2e := later_sep.mp $$ HP2
      icases HP2e with ⟨_, Hs2L⟩
      inext
      iapply specTapesFrag_valid_2 $$ Hs1L Hs2L
    iapply IsExcept0.is_except0
    unfold BIBase.except0
    iapply BI.or_intro_l
    iexact HbotLater

end SemtypesProperties

/-! ## Monadic layer -/

section Monadic
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

theorem fupd_refines {E : CoPset} {e t : Exp rT} {A : lrel rT GF} :
    iprop(|={⊤}=> refines E e t A) ⊢@{IProp GF} refines E e t A := by
  unfold refines
  iintro H %K %ε HR Hna Herr Hpos
  imod H
  iapply H $$ %K %ε HR Hna Herr Hpos

/-- Sequence two refinements via evaluation-context framing. -/
theorem refines_bind (K K' : Ectx rT) {E : CoPset} {A A' : lrel rT GF} {e e' : Exp rT} :
    ⊢@{IProp GF} iprop((refines E e e' A) -∗
      (∀ (v v' : Val rT), A v v' -∗ refines (⊤ : CoPset) (K.fill v.1) (K'.fill v'.1) A')
      -∗ refines E (K.fill e) (K'.fill e') A') := by
  unfold refines
  iintro Hm Hf
  iintro %K'' %ε Hj Hna Herr Hpos
  have hfc : ∀ x : Exp rT, K''.fill (K'.fill x) = (K''.comp K').fill x :=
    fun x => Ectx.fill_comp K'' K' x
  ispecialize Hm $$ %(K''.comp K') %ε
  ihave Hj2 : iprop(⤇ (K''.comp K').fill e') $$ [Hj]
  · rw [← hfc]; iassumption
  ispecialize Hm $$ Hj2 Hna Herr Hpos
  let ΦInner : Val rT → IProp GF := fun v => iprop(
    ∃ (v' : Val rT) (ε' : ENNReal),
      (⤇ (K''.comp K').fill v'.1) ∗ naOwnP (rT := rT) (hlc := hlc) ⊤ ∗ ↯ ε' ∗
      ⌜(0 : ENNReal) < ε'⌝ ∗ A.car v v')
  let ΦOuter : Val rT → IProp GF := fun v => iprop(
    ∃ (v' : Val rT) (ε' : ENNReal),
      (⤇ K''.fill v'.1) ∗ naOwnP (rT := rT) (hlc := hlc) ⊤ ∗ ↯ ε' ∗
      ⌜(0 : ENNReal) < ε'⌝ ∗ A'.car v v')
  let HfTy : IProp GF := iprop(
    ∀ (v v' : Val rT), A v v' -∗ ∀ (K_1 : Ectx rT) (ε : ENNReal),
      (⤇ K_1.fill (K'.fill v'.1)) -∗ (naOwnP (rT := rT) (hlc := hlc) ⊤) -∗ (↯ ε) -∗ (⌜(0 : ENNReal) < ε⌝) -∗
      wp ⊤ (K.fill v.1) (fun v₂ => iprop(
        ∃ (v'' : Val rT) (ε'' : ENNReal),
          (⤇ K_1.fill v''.1) ∗ naOwnP (rT := rT) (hlc := hlc) ⊤ ∗ ↯ ε'' ∗
          ⌜(0 : ENNReal) < ε''⌝ ∗ A'.car v₂ v'')))
  iapply wp_bind (K := K)
  ihave Hstep : iprop(wp ⊤ e (fun v => iprop(HfTy ∗ ΦInner v))) $$ [Hf Hm]
  · iapply wp_frame_l (R := HfTy) (e := e) (E := ⊤) (Φ := ΦInner)
    isplitl [Hf]; · iexact Hf
    iexact Hm
  iapply wp_mono
    (Φ := fun v => iprop(HfTy ∗ ΦInner v))
    (Ψ := fun v => wp ⊤ (K.fill (Exp.ofVal v)) ΦOuter)
  case HΦ =>
    intro v
    change _ ⊢ wp ⊤ (K.fill v.1) _
    iintro ⟨HfLoc, %v', %ε', Hj', Hna', Herr', Hpos', HA⟩
    ihave Hj3 : iprop(⤇ K''.fill (K'.fill v'.1)) $$ [Hj']
    · rw [hfc]; iassumption
    ihave Hf'' := HfLoc $$ %v %v' HA
    iapply Hf'' $$ %K'' %ε' Hj3 Hna' Herr' Hpos'
  iexact Hstep

/-- Value introduction that consumes the local `na_own E` to produce
`na_own ⊤` together with `A v1 v2`. -/
theorem refines_ret_na {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop((naOwnP (rT := rT) (hlc := hlc) E) ={⊤}=∗ (naOwnP (rT := rT) (hlc := hlc) ⊤) ∗ A v1 v2) ⊢@{IProp GF}
    refines E e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HFA
  iintro %K %ε
  iintro HK Hnais Herr Hpos
  have hv : v1.1 = Exp.ofVal v1 := rfl
  rw [hv]
  iapply wp_value_fupd_of_toVal (Exp.toVal?_ofVal v1)
  ispecialize HFA $$ Hnais
  imod HFA with ⟨HF, HA⟩
  imodintro
  iexists v2, ε
  isplitl [HK]; · iassumption
  isplitl [HF]; · iassumption
  isplitl [Herr]; · iassumption
  isplitl [Hpos]; · iassumption
  iassumption

/-- Dual of `refines_ret_na` splitting `⊤ = E ∪ (⊤ \ E)`. -/
theorem refines_ret_na' {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> (naOwnP (rT := rT) (hlc := hlc) (SDiff.sdiff (⊤ : CoPset) E)) ∗ A v1 v2) ⊢@{IProp GF}
    refines E e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HFA
  iintro %K %ε
  iintro Hj Hnais Herr Hpos
  have hv : v1.1 = Exp.ofVal v1 := rfl
  rw [hv]
  iapply wp_value_fupd_of_toVal (Exp.toVal?_ofVal v1)
  imod HFA with ⟨HF, HA⟩
  imodintro
  iexists v2, ε
  isplitl [Hj]; · iassumption
  have hdisj : E ## (SDiff.sdiff (⊤ : CoPset) E) := LawfulSet.disjoint_diff_right
  have hunion : E ∪ (SDiff.sdiff (⊤ : CoPset) E) = (⊤ : CoPset) :=
    LawfulSet.subset_union_diff (fun _ _ => CoPset.mem_full)
  ihave Hfull : iprop(naOwnP (rT := rT) (hlc := hlc) ⊤) $$ [Hnais HF]
  · have heq : (⊤ : CoPset) = E ∪ (SDiff.sdiff (⊤ : CoPset) E) := hunion.symm
    rw [show (naOwnP (rT := rT) (hlc := hlc) (⊤ : CoPset)) = naOwnP (rT := rT) (hlc := hlc) (E ∪ (SDiff.sdiff (⊤ : CoPset) E)) from
        congrArg _ heq]
    iapply (Iris.NonAtomicInvariant.own_union hdisj).mpr
    isplitl [Hnais]
    · iexact Hnais
    · iexact HF
  isplitl [Hfull]; · iexact Hfull
  isplitl [Herr]; · iassumption
  isplitl [Hpos]; · iassumption
  iassumption

/-- From `|={⊤}=> A v1 v2`, conclude `REL v1 << v2 : A`. -/
theorem refines_ret {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> A v1 v2) ⊢@{IProp GF} refines (⊤ : CoPset) e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HA
  iintro %K %ε
  iintro Hj Hna Herr Hpos
  have hv : v1.1 = Exp.ofVal v1 := rfl
  rw [hv]
  iapply wp_value_fupd_of_toVal (Exp.toVal?_ofVal v1)
  imod HA
  imodintro
  iexists v2, ε
  isplitl [Hj]; · iassumption
  isplitl [Hna]; · iassumption
  isplitl [Herr]; · iassumption
  isplitl [Hpos]; · iassumption
  iassumption

instance elim_fupd_refines (E : CoPset) (e t : Exp rT) (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false false (iprop(|={⊤}=> P)) P
      (refines E e t A) (refines E e t A) where
  elim_modal _ := by
    simp only [Iris.BI.intuitionisticallyIf_false']
    iintro ⟨HP, HI⟩
    iapply fupd_refines
    imod HP
    iapply HI $$ HP

instance elim_bupd_refines (E : CoPset) (e t : Exp rT) (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false false (iprop(|==> P)) P
      (refines E e t A) (refines E e t A) where
  elim_modal _ := by
    simp only [Iris.BI.intuitionisticallyIf_false']
    iintro ⟨HP, HI⟩
    iapply fupd_refines
    imod HP
    iapply HI $$ HP

instance is_except_0_refines (E : CoPset) (e t : Exp rT) (A : lrel rT GF) :
    IsExcept0 (refines E e t A) where
  is_except0 := by
    iintro HL
    iapply fupd_refines
    imod HL
    imodintro
    iexact HL

theorem refines_na_alloc {P : IProp GF} (N : Namespace) {E : CoPset} {e1 e2 : Exp rT} {A : lrel rT GF} :
    iprop((▷ P) ∗ ((naInvP (rT := rT) (hlc := hlc) N P) -∗ refines E e1 e2 A)) ⊢@{IProp GF}
    refines E e1 e2 A := by
  iintro ⟨HP, Hcont⟩
  iapply fupd_refines
  imod (Iris.NonAtomicInvariant.inv_alloc (N := N) (E := ⊤)) $$ [HP] with Hinv
  · iassumption
  imodintro
  iapply Hcont $$ Hinv

theorem refines_na_inv {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT} {A : lrel rT GF}
    (HNE : (↑N : CoPset) ⊆ E) :
    iprop((naInvP (rT := rT) (hlc := hlc) N P) ∗ ((▷ P) ∗ (naCloseP (rT := rT) (hlc := hlc) P N E) -∗
        refines (SDiff.sdiff E ((↑N : CoPset) : CoPset)) e1 e2 A)) ⊢@{IProp GF}
    refines E e1 e2 A := by
  unfold refines
  iintro ⟨Hinv, IH⟩
  iintro %K %ε Hj Hnais Herr Hpos
  iapply fupd_wp
  imod Iris.NonAtomicInvariant.inv_acc (F := E) (E := ⊤)
    ((fun _ _ => CoPset.mem_full) : (↑N : CoPset) ⊆ ⊤) HNE $$ Hinv Hnais
    with ⟨HP, Hnais', Hclose⟩
  ihave HPc : iprop((▷ P) ∗ naCloseP (rT := rT) (hlc := hlc) P N E) $$ [HP Hclose]
  · isplitl [HP]; · iassumption
    iassumption
  ihave IH' := IH $$ HPc
  imodintro
  iapply IH' $$ %K %ε Hj Hnais' Herr Hpos

theorem refines_na_close {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT} {A : lrel rT GF} :
    iprop((▷ P) ∗ (naCloseP (rT := rT) (hlc := hlc) P N E) ∗ refines E e1 e2 A) ⊢@{IProp GF}
    refines (SDiff.sdiff E ((↑N : CoPset) : CoPset)) e1 e2 A := by
  unfold refines
  iintro ⟨HP, Hclose, IH⟩
  iintro %K %ε Hj HownFN Herr Hpos
  ihave Hpair : iprop((▷ P) ∗ naOwnP (rT := rT) (hlc := hlc) (SDiff.sdiff E ((↑N : CoPset) : CoPset))) $$ [HP HownFN]
  · isplitl [HP]; · iassumption
    iassumption
  ihave HownF := Hclose $$ Hpair
  iapply fupd_wp
  imod HownF with HownF'
  imodintro
  iapply IH $$ %K %ε Hj HownF' Herr Hpos

end Monadic

end ProbLang
