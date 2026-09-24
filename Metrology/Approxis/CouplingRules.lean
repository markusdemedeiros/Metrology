module

public import Metrology.Approxis.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.ProbLang.Metatheory

@[expose] public section

set_option linter.discrete false


/-!
# Coupling Rules

Coupling rules used by Compatibility/Fundamental/Soundness.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang


variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

/-! ## Timeless instances for tape predicates -/

/-! ## `id` as a coupling bijection -/

/-- `id` maps `[0, z)` into itself — the `hdom` side condition of the coupling rules. -/
theorem id_dom_range {z : Int} : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ id n ∧ id n < z :=
  fun _ h0 hlt => ⟨h0, hlt⟩

/-- Amortised cost of avoiding a single bad draw out of `z`: the indicator of `bad`
summed over `[0, z)` and averaged is at most `1/z`. -/
theorem avoid_one_amort {z : Int} (bad : Int) :
    (∑ n ∈ Finset.Ico (0 : Int) z, if n = bad then (1 : ENNReal) else 0)
      / (z.toNat : ENNReal) ≤ ((z.toNat : ENNReal))⁻¹ := by
  rw [← one_div]
  gcongr
  rw [Finset.sum_ite_eq' (Finset.Ico (0 : Int) z) bad (fun _ => (1 : ENNReal))]
  split <;> simp

/-- `id` hits every point of `[0, z)` exactly once — the `hbij` side condition. -/
theorem id_bij_range {z : Int} :
    ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ id n = m :=
  fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun _ ⟨_, heq⟩ => heq⟩

section TimelessTapes
open scoped AppGS

variable {GF : BundledGFunctors}

instance heapView_tape_frag_discreteE (l : Loc) (t : Tape) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree t)) :=
  View.frag_discrete

instance appTapesFrag_timeless [MeasurableSingletonClass rT] [AppGS rT GF] (l : Loc)
    (t : Tape) :
    BI.Timeless (iprop(l ↪ₐ t) : IProp GF) := iOwn_timeless

instance specTapesFrag_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (t : Tape) :
    BI.Timeless (l ↪ₛ t : IProp GF) := iOwn_timeless

instance heapView_heap_frag_discreteE (l : Loc) (v : Val rT) :
    OFE.DiscreteE (HeapView.Frag (H := LocHeap) l (.own 1) (toAgree v)) := by
  unfold HeapView.Frag
  exact View.frag_discrete

instance appHeapFrag_timeless [MeasurableSingletonClass rT] [IApp : AppGS rT GF]
    (l : Loc) (v : Val rT) :
    BI.Timeless (iprop(l ↦ v) : IProp GF) := by
  unfold appHeapFrag
  exact iOwn_timeless

instance specHeapFrag_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (v : Val rT) :
    BI.Timeless (iprop(l ↦ₛ v) : IProp GF) := by
  unfold specHeapFrag
  exact iOwn_timeless

instance appNatTape_timeless [MeasurableSingletonClass rT] [IApp : AppGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (appNatTape l z ns : IProp GF) := by
  unfold appNatTape
  infer_instance

instance specNatTape_timeless [MeasurableSingletonClass rT] [ISpec : SpecGS rT GF]
    (l : Loc) (z : Int) (ns : List Int) :
    BI.Timeless (specNatTape l z ns : IProp GF) := by
  unfold specNatTape
  infer_instance

end TimelessTapes

/-! ## Fold/unfold bridges for the user-level tape predicates

`appNatTape`/`specNatTape` are `def`s, so `icases`/`iexists` do not see through them.
These bridges name the one defeq step, in the style of `lrel_arr_unfold`
(`Approxis/Compatibility.lean`). -/

section NatTapeBridges
open scoped AppGS

variable {GF : BundledGFunctors}

/-- Unfold `appNatTape` to its existential form, so `icases` can destruct it. -/
theorem appNatTape_unfold [AppGS rT GF] (l : Loc) (z : Int) (ns : List Int) :
    appNatTape l z ns ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₐ ⟨z, fs⟩) :=
  .rfl

/-- Fold a backend app tape back into `appNatTape`. -/
theorem appNatTape_fold [AppGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    (l ↪ₐ ⟨z, fs⟩) ⊢@{IProp GF} appNatTape l z ns := by
  iintro Hb
  iunfold appNatTape
  iexists fs
  iframe %hfs
  iexact Hb

/-- Unfold `specNatTape` to its existential form, so `icases` can destruct it. -/
theorem specNatTape_unfold [SpecGS rT GF] (l : Loc) (z : Int) (ns : List Int) :
    specNatTape l z ns ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₛ ⟨z, fs⟩) :=
  .rfl

/-- Fold a backend spec tape back into `specNatTape`. -/
theorem specNatTape_fold [SpecGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    (l ↪ₛ ⟨z, fs⟩) ⊢@{IProp GF} specNatTape l z ns := by
  iintro Hb
  iunfold specNatTape
  iexists fs
  iframe %hfs
  iexact Hb

end NatTapeBridges

/-! ## Core probability fact: uniform coupling under bijection -/

/-- Uniform-measure coupling under a bijection on the support: for `f` that
restricts to a bijection on `Ico 0 z`, `Cfg.uniform z σ` and `Cfg.uniform z σ'`
are exactly coupled along `{(⟨#n, σ⟩, ⟨#(f n), σ'⟩) | n ∈ Ico 0 z}`. -/
theorem Cfg.uniform_addCoupl_bij [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT)
    (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0
      {p : Cfg rT × Cfg rT | ∃ n : Int, 0 ≤ n ∧ n < z ∧
        p.1 = ⟨pl(#(.int n)), σ⟩ ∧ p.2 = ⟨pl(#(.int (f n))), σ'⟩}
      (Cfg.uniform z σ) (Cfg.uniform z σ') := by
  classical
  rintro ⟨φ, Hφm, Hφb⟩ ⟨ψ, Hψm, Hψb⟩ Hle
  simp only [add_zero]
  show ∫⁻ c, φ c ∂(Cfg.uniform z σ) ≤ ∫⁻ c, ψ c ∂(Cfg.uniform z σ')
  rw [Cfg.lintegral_uniform' Hz σ Hφm, Cfg.lintegral_uniform' Hz σ' Hψm]
  refine mul_le_mul_right ?_ _
  rw [← Finset.sum_Ico_comp_of_bijOn hdom hbij (fun m => ψ (⟨pl(#(.int m)), σ'⟩ : Cfg rT))]
  refine Finset.sum_le_sum fun n hn => ?_
  simp only [Finset.mem_Ico] at hn
  exact Hle ⟨n, hn.1, hn.2, rfl, rfl⟩

/-- **The relation coupling two uniform draws.** Draw `n` on the left is matched with
draw `f n` on the right, filled into the spec-side evaluation context `K`. -/
@[reducible] def CoupledDraw (z : Int) (f : Int → Int) (σ σ' : State rT) (K : Ectx rT) :
    Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
  ∃ n : Int, 0 ≤ n ∧ n < z ∧
    c₁ = ⟨pl(#(.int n)), σ⟩ ∧ c₂ = ⟨K.fill (pl(#(.int (f n)))), σ'⟩

/-- `Cfg.uniform_addCoupl_bij` transported through `K.fill` on the spec side. This is the
form every two-sided `rand` coupling needs: the left draw is taken bare, the right draw is
plugged back into its context. -/
theorem Cfg.uniform_addCoupl_bij_fill [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ σ' : State rT) (f : Int → Int) (K : Ectx rT)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m) :
    AddCoupl 0 {p : Cfg rT × Cfg rT | CoupledDraw z f σ σ' K p.1 p.2}
      (Cfg.uniform z σ) ((Cfg.uniform z σ').map K.fillCfg) := by
  rw [show Cfg.uniform z σ = (Cfg.uniform z σ).map id from MeasureTheory.Measure.map_id.symm]
  refine AddCoupl.map (f := id) (g := K.fillCfg) measurable_id
    (Ectx.fillCfg.measurable K) ?_ (Cfg.uniform_addCoupl_bij Hz σ σ' f hdom hbij)
  rintro a b ⟨n, h0, hz, heqL, rfl⟩
  exact ⟨n, h0, hz, heqL, rfl⟩

/-- `primStep` of `rand #z ()` (unlabeled) equals `Cfg.uniform z σ`. -/
theorem primStep_rand_unit [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    primStep (⟨pl(rand(#(.int z), #(.unit))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  have Hwitness :
      HeadStepSupport (⟨pl(rand(#(.int z), #(.unit))), σ⟩ : Cfg rT) ⟨pl(#(.int 0)), σ⟩ :=
    (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwitness))]
  rfl

/-- `rand #z ()` is reducible and steps uniformly: the payload every unlabeled-`rand`
coupling hands to `wp_couple_rand_core`. -/
theorem randUnit_uniform_step [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) :
    Discrete.Reducible (pl(rand(#(.int z), #(.unit))) : Exp rT) σ ∧
      primStep (⟨pl(rand(#(.int z), #(.unit))), σ⟩ : Cfg rT) = Cfg.uniform z σ :=
  ⟨.of_headStepSupport (.RandNoTapeS Hz (_root_.le_refl _) Hz) (by is_lc),
    primStep_rand_unit Hz σ⟩

/-- `primStep` of `rand #z (lbl α)` unfolds to the lookup of `α` in the tape store. -/
theorem primStep_rand_lbl_eq [MeasurableSingletonClass rT] {z : Int} {σ : State rT} {l : Loc}
    {ρ : Cfg rT} (Hwit : HeadStepSupport (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) ρ) :
    primStep (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) =
      match σ.tapes[l]? with
      | none => (0 : MeasureTheory.Measure (Cfg rT))
      | some ⟨M, ns⟩ =>
        if M = z then
          match ns with
          | [] => Cfg.uniform z σ
          | n :: ns => MeasureTheory.Measure.dirac ⟨.lit <| .int n,
              σ.update_tapes fun t => t.insert l ⟨M, ns⟩⟩
        else Cfg.uniform z σ := by
  rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc)
    (HeadReducible.of_headStepSupport Hwit))]
  rfl

/-- `primStep` of `rand #z (lbl α)` when the tape has the wrong bound. -/
theorem primStep_rand_lbl_wrong [MeasurableSingletonClass rT] {z M : Int}
    (Hz : 0 < z) (HneM : z ≠ M)
    (σ : State rT) (l : Loc) (fs : List { z' : Int // 0 ≤ z' ∧ z' < M })
    (Hlk : σ.tapes[l]? = some ⟨M, fs⟩) :
    primStep (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl), Hlk]
  simp only [if_neg (Ne.symm HneM)]

/-- `primStep` of `rand #z (lbl α)` when the tape has the correct bound and is empty. -/
theorem primStep_rand_lbl_empty [MeasurableSingletonClass rT] {z : Int} (Hz : 0 < z)
    (σ : State rT) (l : Loc)
    (Hlk : σ.tapes[l]? = some ⟨z, []⟩) :
    primStep (⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ : Cfg rT) = Cfg.uniform z σ := by
  rw [primStep_rand_lbl_eq (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl), Hlk]
  simp only [↓reduceIte]

/-! ## Coupling-context helpers -/

open MeasureTheory in
/-- Lift a coupling between `μ` and `primStep ⟨e, σ⟩` to one between `μ` and
`primStep ⟨K.fill e, σ⟩` via `λ a (e', σ'). ∃ e'', e' = K.fill e'' ∧ R a (e'', σ')`. -/
theorem AddCoupl_steps_ctx_bind_r [MeasurableSingletonClass rT] {α}
    [MeasurableSpace α]
    {μ : Measure α} {e : Exp rT} {σ : State rT} {R : Set (α × Cfg rT)} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε R μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : α × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv, show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := K.fillCfg)
    measurable_id (Ectx.fillCfg.measurable K)
    (R := {p : α × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R (p.1, ⟨e'', p.2.state⟩)}) ?_ Hcpl
  intro a ⟨e', σ'⟩ HR
  exact ⟨e', rfl, HR⟩

open MeasureTheory in
/-- Variant of `AddCoupl_steps_ctx_bind_r` where the relation only depends on
the expression of the second component. -/
theorem AddCoupl_steps_ctx_bind_r_no_state [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {e : Exp rT} {σ : State rT} {R : Exp rT → Exp rT → Prop} {ε : ENNReal}
    {K : Ectx rT} (hv : ¬ e.isValue)
    (Hcpl : AddCoupl ε {p : Cfg rT × Cfg rT | R p.1.expr p.2.expr} μ (primStep ⟨e, σ⟩)) :
    AddCoupl ε
      {p : Cfg rT × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}
      μ (primStep ⟨K.fill e, σ⟩) := by
  rw [primStep_fill (K := K) hv, show μ = μ.map id from (MeasureTheory.Measure.map_id).symm]
  refine AddCoupl.map (f := id) (g := K.fillCfg)
    measurable_id (Ectx.fillCfg.measurable K)
    (R := {p : Cfg rT × Cfg rT | ∃ e'', p.2.expr = K.fill e'' ∧ R p.1.expr e''}) ?_ Hcpl
  intro _ b HR
  exact ⟨b.expr, rfl, HR⟩

section CouplingRules

variable {hlc : HasLC} {GF : BundledGFunctors}
    [MeasurableSingletonClass rT] [ApproxisGS rT hlc GF]

/-- The skeleton shared by the two-sided `rand` couplings: the program draws `n ∈ [0, z)`,
the spec side draws the linked value `f n` inside `K`, and the tape resource `A` is handed
back untouched. `HstepL`/`HstepR` are where ownership of `A` is turned into the two
`primStep` equations; they only read `A`, never consume it. -/
theorem wp_couple_rand_core (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) {eL eR : Exp rT} (K : Ectx rT) (E : CoPset) (A : IProp GF) [BI.Timeless A]
    (HvL : eL.toVal? = none) (HvR : ¬ eR.isValue)
    (HstepL : ∀ σ : State rT, ⊢@{IProp GF} appStateAuth σ -∗ A -∗
      ⌜Discrete.Reducible eL σ ∧ primStep (⟨eL, σ⟩ : Cfg rT) = Cfg.uniform z σ⌝)
    (HstepR : ∀ (e' : Exp rT) (σ' : State rT), ⊢@{IProp GF} Cfg.specAuth ⟨e', σ'⟩ -∗ A -∗
      ⌜Discrete.Reducible eR σ' ∧ primStep (⟨eR, σ'⟩ : Cfg rT) = Cfg.uniform z σ'⌝)
    (Φ : Val rT → IProp GF) :
    iprop((▷ A) ∗ (⤇ K.fill eR) ∗
        (∀ (n : Int), A ∗ (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E eL Φ := by
  iintro ⟨HA, Hj, Hcnt⟩
  iapply (wp_lift_prim_steps_coupl HvL)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  imod HA
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %HL := HstepL σ₁ $$ Hσ HA
  ihave %HR := HstepR (K.fill eR) σ₁' $$ Hs HA
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iexists CoupledDraw z f σ₁ σ₁' K, 0, ε
  isplitr; · ipureintro; rw [zero_add]
  isplitr; · ipureintro; exact HL.1.toReducible
  isplitr; · ipureintro; exact HR.1.toReducible.fill K
  isplitr
  · ipureintro
    rw [HL.2, primStep_fill HvR, HR.2]
    exact Cfg.uniform_addCoupl_bij_fill Hz σ₁ σ₁' f K hdom hbij
  iintro %e₂ %σ₂ %e₂' %σ₂' %Hdraw
  obtain ⟨n, hn0, hnz, heq1, heq2⟩ := Hdraw
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update (GF := GF)
    (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hε
  iapply (wp_value_of_toVal (v := (.int n : Val rT)) rfl)
  iapply Hcnt
  iframe HA Hj'
  ipureintro; exact ⟨hn0, hnz⟩

/-- Same-bound bijective coupling: `f : Int → Int` restricts to a bijection on
`[0, z)`. -/
theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
          (⤇ K.fill (pl(#(.int (f n))))) -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply (wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.unit))))
    (eR := pl(rand(#(.int z), #(.unit)))) K E iprop(emp)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by iintro _ _; ipureintro; exact randUnit_uniform_step Hz σ)
    (fun _ σ' => by iintro _ _; ipureintro; exact randUnit_uniform_step Hz σ') Φ)
  isplitr
  · iintro !>; iempintro
  iframe Hj
  iintro %n ⟨-, Hj', %hn⟩
  iapply Hcnt $$ %n %hn Hj'

/-- **Adversarial same-bound coupling.** Both sides draw from `[0, z)` and `f`
links the draws; the caller spends the amortized credit `ε₁` up front and the
continuation is handed the per-draw credit `ε₂ n`. -/
theorem wp_couple_rand_rand_adv (z : Int) (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z)
    (hamort : (∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n) / (z.toNat : ENNReal) ≤ ε₁)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗ ↯ ε₁ ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ ↯ (ε₂ n) -∗
          (⤇ K.fill (pl(#(.int (f n))))) -∗ Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none := Exp.rand_toVal?_eq_none
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := Exp.rand_not_isValue
  iapply (wp_lift_prim_steps_coupl_adv_err_le_1 Hv)
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have HredR : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    .of_headStepSupport_fill K (.RandNoTapeS Hz (_root_.le_refl _) Hz) (by is_lc)
  set P : Cfg rT → Cfg rT → Int → Prop := fun ρ₁ ρ₂ n =>
    (0 ≤ n ∧ n < z) ∧ ρ₁ = (⟨pl(#(.int n)), σ₁⟩ : Cfg rT) ∧
      ρ₂ = (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)
  set X : Cfg rT → Cfg rT → ENNReal :=
    fun ρ₁ ρ₂ => 1 ⊓ ⨅ n, ⨅ (_ : P ρ₁ ρ₂ n), ε₂ n
  have hXgraph : ∀ n : Int, 0 ≤ n → n < z →
      X ⟨pl(#(.int n)), σ₁⟩ ⟨K.fill pl(#(.int (f n))), σ₁'⟩ = 1 ⊓ ε₂ n := by
    intro n h0 hn
    refine _root_.le_antisymm (inf_le_inf_left _ (iInf₂_le n ⟨⟨h0, hn⟩, rfl, rfl⟩))
      (le_inf inf_le_left (le_iInf₂ fun n' hn' => ?_))
    obtain ⟨-, h1, -⟩ := hn'
    obtain ⟨he, -⟩ := (Cfg.mk.injEq ..).mp h1
    simp only [Exp.lit.injEq, BaseLit.int.injEq] at he
    subst he
    exact inf_le_right
  have hXoff : ∀ ρ₁ ρ₂, (¬ ∃ n, P ρ₁ ρ₂ n) → X ρ₁ ρ₂ = 1 := fun ρ₁ ρ₂ h =>
    _root_.le_antisymm inf_le_left (le_inf le_rfl (le_iInf₂ fun n hn => absurd ⟨n, hn⟩ h))
  have Hkant : ExpCoupl ε₁ X (primStep (⟨pl(rand(#(.int z), #(.unit))), σ₁⟩ : Cfg rT))
      (primStep (⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩ : Cfg rT)) := by
    intro h₁ h₂ hm₁ hm₂ _ _ hle
    have hR : (∫⁻ b, h₂ b ∂(primStep (⟨K.fill pl(rand(#(.int z), #(.unit))), σ₁'⟩ : Cfg rT)))
        = ((z.toNat : ENNReal))⁻¹ *
            ∑ m ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int m)), σ₁'⟩ : Cfg rT) := by
      rw [primStep_fill Hv_rand, primStep_rand_unit Hz,
        MeasureTheory.lintegral_map hm₂
          (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
          (Ectx.fillCfg.measurable K),
        Cfg.lintegral_uniform' Hz σ₁'
          (φ := fun a : Cfg rT => h₂ ⟨K.fill a.expr, a.state⟩)
          (hm₂.comp (Ectx.fillCfg.measurable K))]
    rw [primStep_rand_unit Hz, Cfg.lintegral_uniform' Hz σ₁ hm₁, hR,
      ← Finset.sum_Ico_comp_of_bijOn hdom hbij
        (fun m => h₂ (⟨K.fill pl(#(.int m)), σ₁'⟩ : Cfg rT))]
    have hstep : ∑ n ∈ Finset.Ico (0 : Int) z, h₁ (⟨pl(#(.int n)), σ₁⟩ : Cfg rT) ≤
        (∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
          ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [Finset.mem_Ico] at hn
      refine (hle _ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)).trans ?_
      gcongr
      rw [hXgraph n hn.1 hn.2]
      exact inf_le_right
    calc ((z.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) z, h₁ (⟨pl(#(.int n)), σ₁⟩ : Cfg rT)
        ≤ ((z.toNat : ENNReal))⁻¹ *
            ((∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
              ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n) := by gcongr
      _ = ((z.toNat : ENNReal))⁻¹ *
            (∑ n ∈ Finset.Ico (0 : Int) z, h₂ (⟨K.fill pl(#(.int (f n))), σ₁'⟩ : Cfg rT)) +
          ((z.toNat : ENNReal))⁻¹ * ∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n := mul_add ..
      _ ≤ _ := by
          gcongr
          rwa [← ENNReal.div_eq_inv_mul]
  ihave %Hεle := ErrorCredit.supply_bound $$ Hε Herr
  ihave Hdec := ErrorCredit.supply_decrease $$ Hε Herr
  imod Hdec
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iexists X, ε₁, (ε - ε₁)
  isplitr; · ipureintro; exact _root_.le_of_eq (add_tsub_cancel_of_le Hεle)
  isplitr; · ipureintro; exact (randUnit_uniform_step Hz σ₁).1.toReducible
  isplitr; · ipureintro; exact HredR.toReducible
  isplitr; · ipureintro; exact fun _ _ => inf_le_left
  iframe %Hkant
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  by_cases hg : ∃ n : Int, P ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ n
  · obtain ⟨n, ⟨hn0, hnz⟩, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
    rw [hXgraph n hn0 hnz]
    by_cases hbig : (1 : ENNReal) ≤ (1 ⊓ ε₂ n) + (ε - ε₁)
    · imod Hclose
      imodintro
      ileft
      ipureintro
      exact hbig
    · rw [_root_.not_le] at hbig
      have hinf : (1 : ENNReal) ⊓ ε₂ n < 1 := _root_.lt_of_le_of_lt le_self_add hbig
      have hlt : ε₂ n < 1 := by
        by_contra hge
        exact absurd (inf_eq_left.mpr (_root_.not_lt.mp hge)) hinf.ne
      rw [inf_eq_right.mpr hlt.le]
      have hsum : (ε - ε₁) + ε₂ n < 1 := by
        rw [inf_eq_right.mpr hlt.le] at hbig
        rwa [add_comm]
      imod specProg_update
        (e3 := K.fill (pl(#(.int (f n))))) $$ Hs Hj with ⟨Hs', Hj'⟩
      imod ErrorCredit.supply_increase hsum $$ Hdec with ⟨HdecA, Hfrag⟩
      imod Hclose
      imodintro
      iright
      iframe Hσ Hs'
      isplitl [HdecA]
      · iapply ErrorCredit.extAuth (add_comm _ _)
        iexact HdecA
      iapply (wp_value_of_toVal rfl)
      iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hfrag Hj'
  · imod Hclose
    imodintro
    ileft
    ipureintro
    rw [hXoff _ _ hg]
    exact le_self_add

/-- Avoidance: both sides draw the same value from `[0, z)`, and the caller pays
`1/z` to learn that the value is not `bad`. -/
theorem wp_couple_rand_rand_avoid (z bad : Int) (Hz : 0 < z) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗ ↯ ((z.toNat : ENNReal))⁻¹ ∗
        (∀ (n : Int), (⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝) -∗
          (⤇ K.fill (pl(#(.int n)))) -∗ Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply (wp_couple_rand_rand_adv z id ((z.toNat : ENNReal))⁻¹
    (fun n => if n = bad then 1 else 0) id_dom_range id_bij_range Hz (avoid_one_amort bad) K E Φ)
  iframe Hj Herr
  iintro %n %hn Hec Hj'
  by_cases hb : n = bad
  · rw [if_pos hb]
    iexfalso
    iapply ErrorCredit.contradict (_root_.le_refl 1) $$ Hec
  · simp only [id_eq]
    iapply Hcnt
    · ipureintro; exact ⟨hn, hb⟩
    · iexact Hj'

/-- `wp_couple_tapes_bij`: presample both tapes in lockstep along a bijection
`f` on `[0, z)`. No program step and no error. -/
theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ appNatTape α z (ns ++ [n]) -∗
          specNatTape αₛ z (nsₛ ++ [f n]) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  icases appNatTape_unfold α z ns $$ Hα with ⟨%fs, %Hfs, Hα⟩
  icases specNatTape_unfold αₛ z nsₛ $$ Hαₛ with ⟨%fsₛ, %Hfsₛ, Hαₛ⟩
  iapply wp_couple_erasables
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ihave %hlk := app_state_lookup_tape $$ Hσ Hα
  ihave %hlk' := spec_auth_lookup_tape $$ Hs Hαₛ
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n : Int, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlk Hz
  isplitr; · ipureintro; exact ErasableExpr.tapePresample hlk' Hz
  isplitr; · ipureintro; exact tapePresample_addCoupl_bij hlk hlk' Hz f hdom hbij
  iintro %σ₂ %σ₂' %HR
  obtain ⟨n, hn0, hnz, rfl, rfl⟩ := HR
  imod app_state_update_tape
    (s := ⟨z, fs ++ [tapeIdxOf Hz n]⟩) $$ Hσ Hα with ⟨Hσ', Hα'⟩
  imod spec_auth_update_tape
    (s := ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩) $$ Hs Hαₛ with ⟨Hs', Hαₛ'⟩
  imod Hclose
  imodintro
  simp only [approxisWpGS_stateInterp_eq, approxisWpGS_specInterp_eq,
    ExtTreeMap.insert_eq_PartialMap_insert]
  iframe Hσ' Hs' Hε
  have hd := hdom n hn0 hnz
  ihave HnatA := appNatTape_fold (l := α) (ns := ns ++ [n])
    (by simp [← Hfs, tapeIdxOf_val Hz hn0 hnz]) $$ Hα'
  ihave HnatS := specNatTape_fold (l := αₛ) (ns := nsₛ ++ [f n])
    (by simp [← Hfsₛ, tapeIdxOf_val Hz hd.1 hd.2]) $$ Hαₛ'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ HnatA HnatS

/-- Labeled-rand coupling where both tapes have the wrong bound `M ≠ z`.
Both tapes are unchanged; the draw is uniform and `f` links the values. -/
theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx rT) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          appNatTape α M xs ∗ specNatTape α' M ys ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply (wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.lbl α))))
    (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α M xs ∗ specNatTape α' M ys)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by
      iintro Hσ ⟨HA, -⟩
      icases appNatTape_unfold α M xs $$ HA with ⟨%fs, -, Hb⟩
      ihave %hlk := app_state_lookup_tape (GF := GF) (σ := σ) $$ Hσ Hb
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeOtherS Hz hlk HneM (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_wrong Hz HneM σ α fs hlk⟩)
    (fun _ σ' => by
      iintro Hs ⟨-, HS⟩
      icases specNatTape_unfold α' M ys $$ HS with ⟨%fs', -, Hb'⟩
      ihave %hlk := spec_auth_lookup_tape (GF := GF) (σ := σ') $$ Hs Hb'
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeOtherS Hz hlk HneM (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_wrong Hz HneM σ' α' fs' hlk⟩) Φ)
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-- Fully labeled two-sided coupling via a bijection `f`, both tapes empty. -/
theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α α' : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗ specNatTape α' z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply (wp_couple_rand_core z f hdom hbij Hz (eL := pl(rand(#(.int z), #(.lbl α))))
    (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α z [] ∗ specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by
      iintro Hσ ⟨HA, -⟩
      icases appNatTape_unfold α z [] $$ HA with ⟨%fs, %hmap, Hb⟩
      obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
      ihave %hlk := app_state_lookup_tape (GF := GF) (σ := σ) $$ Hσ Hb
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_empty Hz σ α hlk⟩)
    (fun _ σ' => by
      iintro Hs ⟨-, HS⟩
      icases specNatTape_unfold α' z [] $$ HS with ⟨%fs', %hmap', Hb'⟩
      obtain rfl : fs' = [] := List.map_eq_nil_iff.mp hmap'
      ihave %hlk := spec_auth_lookup_tape (GF := GF) (σ := σ') $$ Hs Hb'
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_empty Hz σ' α' hlk⟩) Φ)
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ appNatTape α z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        (∀ (n : Int),
          appNatTape α z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl α)))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(appNatTape α z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by
      iintro Hσ HA
      icases appNatTape_unfold α z [] $$ HA with ⟨%fs, %hmap, Hb⟩
      obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
      ihave %hlk := app_state_lookup_tape (GF := GF) (σ := σ) $$ Hσ Hb
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_empty Hz σ α hlk⟩)
    (fun _ σ' => by iintro _ _; ipureintro; exact randUnit_uniform_step Hz σ') Φ

/-- Symmetric: couple LHS unit rand with RHS rand on empty tape. -/
theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α' : Loc) (Φ : Val rT → IProp GF) :
    iprop(▷ specNatTape α' z [] ∗
        (⤇ K.fill (pl(rand(#(.int z), #(.lbl α'))))) ∗
        (∀ (n : Int),
          specNatTape α' z [] ∗
            (⤇ K.fill (pl(#(.int (f n))))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by iintro _ _; ipureintro; exact randUnit_uniform_step Hz σ)
    (fun _ σ' => by
      iintro Hs HS
      icases specNatTape_unfold α' z [] $$ HS with ⟨%fs', %hmap', Hb'⟩
      obtain rfl : fs' = [] := List.map_eq_nil_iff.mp hmap'
      ihave %hlk := spec_auth_lookup_tape (GF := GF) (σ := σ') $$ Hs Hb'
      ipureintro
      exact ⟨.of_headStepSupport (.RandTapeEmptyS Hz hlk rfl (_root_.le_refl _) Hz rfl)
        (by is_lc), primStep_rand_lbl_empty Hz σ' α' hlk⟩) Φ

end CouplingRules

end ProbLang
