module

public import Metrology.TotalEris

@[expose] public section

/-!
# Basic TotalEris smoke tests

Tiny examples to validate the API surface:

* values introduce trivially via `twp_value`,
* allocation + load roundtrips via `twp_alloc` and `twp_load`,
* pure beta-reduction via `twp_pure_step_fupd`.

These don't use error credits and don't depend on adequacy. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris


variable {rT : Type _} [ProbLang.ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- Trivial value-return: `tglWp E v (fun w => ⌜w = v⌝)`. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iapply tglWp_value
  ipure_intro; rfl

/-- Alloc → load roundtrip: `let x = ref v in !x = v`.

The result expression here is `.load (.lit (.loc l))` post-step. Composing
this with `twp_load` via `tglWp_bind` would give the full
let-binding form. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.alloc (.ofVal v))
      (fun w => iprop(∃ l : Loc,
        ⌜w = ⟨.lit (.loc l), IsVal.lit⟩⌝ ∗ appHeapFrag l v)) := by
  iapply twp_alloc
  iintro %l Hl
  iexists l
  isplitr
  · ipure_intro; rfl
  iexact Hl

/-- `twp_rand_tape` round-trip: reading the head of a non-empty tape returns
the stored value and leaves the tape's tail in place. -/
example (E : CoPset) (l : Loc) (z : Int)
    (n : { z' : Int // 0 ≤ z' ∧ z' < z })
    (ns : List { z' : Int // 0 ≤ z' ∧ z' < z }) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, n :: ns⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w : Val rT => iprop(⌜w = ⟨.lit (.int n.val), IsVal.lit⟩⌝ ∗ l ↪ₐ ⟨z, ns⟩)) := by
  iintro Hl
  iapply twp_rand_tape
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  isplitr
  · ipure_intro; rfl
  iexact Hl'

/-- `twp_rand_tape_empty`: rand on an empty tape falls through to uniform
sampling and the empty tape is preserved. -/
example (E : CoPset) (l : Loc) (z : Int) (Hz : 0 < z) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, []⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w : Val rT => iprop(∃ n : Int,
          ⌜0 ≤ n ∧ n < z⌝ ∗ ⌜w = ⟨.lit (.int n), IsVal.lit⟩⌝ ∗ l ↪ₐ ⟨z, []⟩)) := by
  iintro Hl
  iapply (twp_rand_tape_empty Hz)
  isplitl [Hl]
  · iexact Hl
  iintro %n Hl' %Hbnd
  iexists n
  isplitr; · ipure_intro; exact Hbnd
  isplitr; · ipure_intro; rfl
  iexact Hl'

/-- `tglWp_mono`: weaken a `Φ`-post into a stronger `Ψ`-post via a Lean-level
pointwise entailment. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply ErisWpGS.tglWp_mono (Φ := fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
  · intro w
    iintro ⟨H, -⟩; iexact H
  iexact HW

/-- `tglWp_fupd`: a `|={E}=>` in the post is absorbed. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply ErisWpGS.tglWp_fupd
  iexact HW

/-- `tglWp_wand`: combine a WP with a spatial continuation wand. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v ∨ w = v⌝)) := by
  iintro HW
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %w %Hw
  ipure_intro
  exact Or.inl Hw

/-- `tglWp_strong_mono`: the fupd-aware variant. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_strong_mono
  isplitl [HW]; · iexact HW
  iintro %w %Hw
  imodintro
  imodintro
  ipure_intro; exact Hw

/-- `tglWp_bind_value`: the value-only specialization of bind. When the inner
expression is already a value, the bind collapses to running the outer
continuation under the original WP body. -/
example (E : CoPset) (v : Val rT) (K : Ectx rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w =>
        tglWp E (K.fill (.ofVal w)) (fun w' => iprop(⌜w' = v⌝))) -∗
      tglWp E (K.fill (Exp.ofVal v)) (fun w' => iprop(⌜w' = v⌝)) := by
  iintro HW
  iapply tglWp_bind_value
  iexact HW

/-- `ec_induction`: error-amplification induction (intuitionistic-wand form
re-exported from `ErrorCredit.Induction.increasing`). Demonstrates the
chain that geometric_total uses: from a persistent rule "given a bigger
credit `↯ε'` and the current credit `↯ε`, prove P", get `↯ε ⊢ P`. -/
example [ECGS GF] (ε : ENNReal) (ε' : NNReal) (P : IProp GF)
    (hε : 0 < ε) (hε' : ε < ε') :
    ⊢@{IProp GF} iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) -∗ iprop(↯ε -∗ P) := by
  iintro Hamp
  iapply (ec_induction hε hε')
  iexact Hamp

/-- `tglWp_bind`: full evaluation-context bind. -/
example (E : CoPset) (e : Exp rT) (K : Ectx rT) (φ : Val rT → Prop) :
    ⊢@{IProp GF} tglWp E e (fun v =>
        tglWp E (K.fill (.ofVal v)) (fun w => iprop(⌜φ w⌝))) -∗
      tglWp E (K.fill e) (fun w => iprop(⌜φ w⌝)) := by
  iintro HW
  iapply tglWp_bind
  iexact HW

/-- Worked example: `(λ x. !x) (alloc v) ⇓ v`.

Steps:
1. `tglWp_bind` with `K = [appR (λ. !0)]` to focus on the inner `alloc v`.
2. `twp_alloc` allocates and yields `l ↦ v`.
3. Beta-reduce `(λ. !0) #l` to `!#l` (a single pure step).
4. `twp_load` reads `v` from the heap.
5. Conclude `w = v`. -/
-- Original body preserved as a comment; after threading `rT` through the
-- examples, the pure-step `PureExec` typeclass synthesis no longer fires
-- for the beta-reduction step. Replaced with `sorry` pending a follow-up.
-- example (E : CoPset) (v : Val rT) :
--     ⊢@{IProp GF} tglWp E
--       (Exp.app (Exp.lam (Exp.load (Exp.bvar 0))) (Exp.alloc (Exp.ofVal v)))
--       (fun w => iprop(⌜w = v⌝)) := by
--   let K : Ectx rT := [EctxItem.appR (Exp.lam (Exp.load (Exp.bvar 0)))]
--   show ⊢@{IProp GF} tglWp E (K.fill (Exp.alloc (Exp.ofVal v))) _
--   iapply tglWp_bind
--   iapply twp_alloc
--   iintro %l Hl
--   simp only [K, Ectx.fill, List.foldl, flip, EctxItem.fillItem]
--   iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
--     (e₁ := Exp.app (Exp.lam (Exp.load (Exp.bvar 0)))
--       (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩))
--     (e₂ := Exp.open' (Exp.load (Exp.bvar 0))
--       (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩))
--     (Exp.ofVal ⟨.lit (.loc l), IsVal.lit⟩).isValue ⟨IsVal.lit⟩)
--   simp only [Exp.open', Exp.openRec, Exp.ofVal, ↓reduceIte]
--   iapply twp_load
--   isplitl [Hl]; · iexact Hl
--   iintro _
--   ipure_intro; rfl
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E
      (pl((fun x, !x) (alloc({Exp.ofVal v}))) : Exp rT)
      (fun w => iprop(⌜w = v⌝)) := by
  let K : Ectx rT := [EctxItem.appR (Exp.lam (Exp.load (Exp.bvar 0)))]
  show ⊢@{IProp GF} tglWp E (K.fill (Exp.alloc (Exp.ofVal v))) _
  iapply tglWp_bind
  iapply twp_alloc
  iintro %l Hl
  -- Unfold the `pl(...)` lambda's `Exp.close` into bvar form so `PureExec`
  -- on `app_lam` fires.
  simp only [K, Ectx.fill, List.foldl, flip, EctxItem.fillItem, Exp.ofVal]
  iapply (twp_pure_step_fupd (n := 1)
    (e₁ := Exp.app (Exp.lam (Exp.load (Exp.bvar 0))) (Exp.lit (.loc l) : Exp rT))
    (e₂ := Exp.open' (Exp.load (Exp.bvar 0)) (Exp.lit (.loc l)))
    (Exp.lit (.loc l) : Exp rT).isValue ⟨IsVal.lit⟩)
  simp only [Exp.open', Exp.openRec, ↓reduceIte]
  iapply twp_load
  isplitl [Hl]; · iexact Hl
  iintro _
  ipure_intro; rfl

/-- `fupd_tglWp`: a leading `|={E}=>` on a tglWp is absorbed. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} iprop(|={E}=> tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝))) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply fupd_tglWp
  iexact HW

/-- `tglWp_frame_l`: frame a (spatial) resource. -/
example (E : CoPset) (v : Val rT) (R : Prop) (HR : R) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜R⌝ ∗ ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_frame_l (R := iprop(⌜R⌝))
  isplitr [HW]; swap; · iexact HW
  ipure_intro; exact HR

/-- `twp_rand_exp` (the wrapper) smoke test on `rand 2 ()` with the
geometric-style error fn `F 0 = 0`, `F 1 = ε`. Continuation receives
the per-outcome credit. -/
example (E : CoPset) (ε : ENNReal) :
    ⊢@{IProp GF} ↯ε -∗
      tglWp E (.rand (.lit (.int 2)) (.lit .unit))
        (fun w : Val rT => iprop(∃ n : Int, ⌜0 ≤ n ∧ n < 2 ∧
          w = ⟨.lit (.int n), IsVal.lit⟩⌝)) := by
  iintro Hcr
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else ε
  iapply (twp_rand_exp (z := 2) (ε₁ := ε) (ε₂ := F)
    (Hz := by decide)
    (HSum := by
      simp only [F, show (2 : Int).toNat = 2 from rfl,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.reduceEqDiff, ↓reduceIte]
      rw [show ((2 : ℕ) : ENNReal) = 1 + 1 from by norm_num, add_mul, one_mul]
      exact le_self_add)) $$ Hcr
  iintro %n ⟨%Hn, _⟩
  iexists n
  ipure_intro
  exact ⟨Hn.1, Hn.2, rfl⟩

/-- `twp_rand_exp_nat` smoke test: `rand 1 ()` with zero error distribution.
The single outcome `n = 0` returns `↯0` to the continuation. -/
example (E : CoPset) (ε : ENNReal) :
    ⊢@{IProp GF} ↯ε -∗
      tglWp E (.rand (.lit (.int 1)) (.lit .unit))
        (fun w : Val rT => iprop(⌜w = ⟨.lit (.int 0), IsVal.lit⟩⌝)) := by
  iintro Hε
  iapply (twp_rand_exp_nat (z := 1) (ε₁ := ε) (ε₂ := fun _ => 0)
    (Hz := by decide) (Hbd := fun _ => zero_le _)
    (HSum := by simp)) $$ Hε
  iintro %n ⟨%Hn, _⟩
  -- `0 ≤ n < 1` forces `n = 0`.
  obtain ⟨Hn₁, Hn₂⟩ := Hn
  interval_cases n
  ipure_intro; rfl

/-! ## End-to-end adequacy smoke tests

These exercise the full chain `tglWp` triple → `Tgl` Prop bound at the
metalogic level, using the now-complete `twp_tgl` adequacy theorem. -/

section AdequacySmokeTests

variable {GF : BundledGFunctors.{0,0,0}}
  [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]

/-- A value at zero error has `Tgl = 0` after adequacy. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) ?_
  intro _; iintro _; iapply tglWp_value; ipure_intro; exact hφ

/-- Mass at ε = 0 for a value: `1 ≤ limExec _ Set.univ`. -/
example (v : Val rT) (σ : State rT) :
    1 ≤ (limExec ⟨Exp.ofVal v, σ⟩) Set.univ := by
  have h : Tgl (limExec ⟨Exp.ofVal v, σ⟩) (fun _ => True) 0 := by
    refine twp_tgl (GF := GF) (e := Exp.ofVal v) (σ := σ)
      (φ := fun _ => True) ?_
    intro _; iintro _; iapply tglWp_value; ipure_intro; trivial
  have := Tgl.termination_ineq h
  rwa [tsub_zero] at this

/-- ε-limit form (`twp_tgl_limit`): a value with the WP triple at every
`ε' > 0` yields `Tgl ... 0`. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl_limit (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) ?_
  intro _ _ _; iintro _; iapply tglWp_value; ipure_intro; exact hφ

/-- Pgl bound via adequacy: at ε = 0, the limit-exec measure of the
non-value-or-`¬φ` set is `0`. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v) :
    Pgl 0 (fun ρ => ∃ w, ρ.expr = Exp.ofVal w ∧ φ w)
      (limExec ⟨Exp.ofVal v, σ⟩) := by
  refine twp_pgl_lim (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) ?_
  intro _; iintro _; iapply tglWp_value; ipure_intro; exact hφ

end AdequacySmokeTests

end TotalEris
end ProbLang
