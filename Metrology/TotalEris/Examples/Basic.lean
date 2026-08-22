module

public import Metrology.TotalEris

@[expose] public section

/-!
# Basic TotalEris smoke tests

Tiny examples to validate the API surface:

* values introduce trivially via `twp_value`,
* allocation + load roundtrips via `twp_alloc` and `twp_load`,
* pure beta-reduction via `twp_pures`. -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- Trivial value-return: `tglWp E v (fun w => ⌜w = v⌝)`. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iapply tglWp_value
  itrivial

/-- `twp_alloc`: allocating `v` yields a fresh location `l` together with `l ↦ v`. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.alloc (.ofVal v))
      (fun w => iprop(∃ l : Loc,
        ⌜w = .loc l⌝ ∗ appHeapFrag l v)) := by
  iapply twp_alloc
  iintro %l $
  itrivial

/-- `twp_rand_tape` round-trip: reading the head of a non-empty tape returns
the stored value and leaves the tape's tail in place. -/
example (E : CoPset) (l : Loc) (z : Int)
    (n : { z' : Int // 0 ≤ z' ∧ z' < z })
    (ns : List { z' : Int // 0 ≤ z' ∧ z' < z }) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, n :: ns⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w : Val rT => iprop(⌜w = .int n.val⌝ ∗ l ↪ₐ ⟨z, ns⟩)) := by
  iintro Hl
  iapply twp_rand_tape
  iframe Hl
  iintro $
  itrivial

/-- `twp_rand_tape_empty`: rand on an empty tape falls through to uniform
sampling and the empty tape is preserved. -/
example (E : CoPset) (l : Loc) (z : Int) (Hz : 0 < z) :
    ⊢@{IProp GF} l ↪ₐ ⟨z, []⟩ -∗
      tglWp E (.rand (.lit (.int z)) (.lit (.lbl l)))
        (fun w : Val rT => iprop(∃ n : Int,
          ⌜0 ≤ n ∧ n < z⌝ ∗ ⌜w = .int n⌝ ∗ l ↪ₐ ⟨z, []⟩)) := by
  iintro Hl
  iapply (twp_rand_tape_empty Hz)
  iframe Hl
  iintro %n $ %Hbnd
  iframe %Hbnd
  itrivial

/-- `tglWp_mono`: weaken a `Φ`-post into a stronger `Ψ`-post via a Lean-level
pointwise entailment. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_mono (Φ := fun w => iprop(⌜w = v⌝ ∗ ⌜w = v⌝))
  · intro w; iintro ⟨$, -⟩
  · iexact HW

/-- `tglWp_fupd`: a `|={E}=>` in the post is absorbed. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝))
      -∗ tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) :=
  entails_wand tglWp_fupd

/-- `tglWp_wand`: combine a WP with a spatial continuation wand. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v ∨ w = v⌝)) := by
  iintro HW
  iapply tglWp_wand
  iframe HW
  iintro %w %Hw
  ipureintro
  exact Or.inl Hw

/-- `tglWp_strong_mono`: the fupd-aware variant. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(|={E}=> ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_strong_mono
  iframe HW
  iintro %w %Hw !> !> //

/-- `tglWp_bind_value`: the value-only specialization of bind. When the inner
expression is already a value, the bind collapses to running the outer
continuation under the original WP body. -/
example (E : CoPset) (v : Val rT) (K : Ectx rT) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w =>
        tglWp E (K.fill (.ofVal w)) (fun w' => iprop(⌜w' = v⌝))) -∗
      tglWp E (K.fill (Exp.ofVal v)) (fun w' => iprop(⌜w' = v⌝)) :=
  entails_wand tglWp_bind_value

/-- `ec_induction`: error-amplification induction (intuitionistic-wand form
re-exported from `ErrorCredit.Induction.increasing`). From a persistent rule
"given a bigger credit `↯ε'` and the current credit `↯ε`, prove P", get
`↯ε ⊢ P`. -/
example [ECGS GF] (ε : ENNReal) (ε' : NNReal) (P : IProp GF)
    (hε : 0 < ε) (hε' : ε < ε') :
    ⊢@{IProp GF} iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) -∗
      iprop(↯ε -∗ P) :=
  entails_wand (ErrorCredit.Induction.increasing hε hε')

/-- `tglWp_bind`: full evaluation-context bind. -/
example (E : CoPset) (e : Exp rT) (K : Ectx rT) (φ : Val rT → Prop) :
    ⊢@{IProp GF} tglWp E e (fun v =>
        tglWp E (K.fill (.ofVal v)) (fun w => iprop(⌜φ w⌝))) -∗
      tglWp E (K.fill e) (fun w => iprop(⌜φ w⌝)) :=
  entails_wand tglWp_bind

/-- Worked example: `(λ x. !x) (alloc v) ⇓ v`.

Steps:
1. `twp_bind` focuses the inner `alloc v` (discovering `K = [appR (λ x. !x)]`).
2. `twp_alloc` allocates and yields `l ↦ v`.
3. `twp_pures` β-reduces `(λ x. !x) #l` to `!#l`.
4. `twp_load` reads `v` from the heap. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} tglWp E
      (pl((fun x, !x) (alloc({Exp.ofVal v}))) : Exp rT)
      (fun w => iprop(⌜w = v⌝)) := by
  twp_bind (Exp.alloc (Exp.ofVal v))
  iapply twp_alloc
  iintro %l Hl
  twp_pures
  iapply twp_load
  iframe Hl
  iintro - //

/-- `fupd_tglWp`: a leading `|={E}=>` on a tglWp is absorbed. -/
example (E : CoPset) (v : Val rT) :
    ⊢@{IProp GF} iprop(|={E}=> tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝))) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) :=
  entails_wand fupd_tglWp

/-- `tglWp_frame_left`: frame a (spatial) resource. -/
example (E : CoPset) (v : Val rT) (R : Prop) (HR : R) :
    ⊢@{IProp GF} tglWp E (.ofVal v) (fun w => iprop(⌜w = v⌝)) -∗
      tglWp E (.ofVal v) (fun w => iprop(⌜R⌝ ∗ ⌜w = v⌝)) := by
  iintro HW
  iapply tglWp_frame_left (R := iprop(⌜R⌝))
  iframe HW %HR

/-- `twp_rand_exp'` smoke test on `rand 2 ()` with the geometric-style error
fn `F 0 = 0`, `F 1 = ε`. Continuation receives the per-outcome credit. -/
example (E : CoPset) (ε : ENNReal) :
    ⊢@{IProp GF} ↯ε -∗
      tglWp E (.rand (.lit (.int 2)) (.lit .unit))
        (fun w : Val rT => iprop(∃ n : Int, ⌜0 ≤ n ∧ n < 2 ∧
          w = .int n⌝)) := by
  iintro Hcr
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else ε
  have htoNat : (2 : Int).toNat = 2 := rfl
  have hF : ∑ n ∈ Finset.range 2, F n = ε := by simp [F, Finset.sum_range_succ]
  have hsplit : ((2 : ℕ) : ENNReal) = 1 + 1 := by norm_num
  have HSum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ENNReal) ≤ ε := by
    rw [ENNReal.div_le_iff' (by simp) (by simp), htoNat, hF, hsplit, add_mul, one_mul]
    exact le_self_add
  iapply (twp_rand_exp' (z := 2) (ε₁ := ε) (ε₂ := F) (Hz := by decide) (HSum := HSum)) $$ Hcr
  iintro %n ⟨%Hn, -⟩
  iexists n
  ipureintro
  exact ⟨Hn.1, Hn.2, rfl⟩

/-- `twp_rand_exp` smoke test: `rand 1 ()` with zero error distribution.
The single outcome `n = 0` returns `↯0` to the continuation. -/
example (E : CoPset) (ε : ENNReal) :
    ⊢@{IProp GF} ↯ε -∗
      tglWp E (.rand (.lit (.int 1)) (.lit .unit))
        (fun w : Val rT => iprop(⌜w = .int 0⌝)) := by
  iintro Hε
  iapply (twp_rand_exp (z := 1) (ε₁ := ε) (ε₂ := fun _ => 0)
    (Hz := by decide) (Hbd := fun _ => zero_le)
    (HSum := by simp)) $$ Hε
  iintro %n ⟨%⟨Hn₁, Hn₂⟩, -⟩
  interval_cases n
  itrivial

/-! ## End-to-end adequacy smoke tests

These exercise the full chain `tglWp` triple → `Tgl` Prop bound at the
metalogic level. -/

section AdequacySmokeTests

variable {GF : BundledGFunctors.{0,0,0}}
  [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]

/-- A value at zero error has `Tgl = 0` after adequacy. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) hφm ?_
  intro _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

/-- Mass at ε = 0 for a value: `1 ≤ limExec _ Set.univ`. -/
example (v : Val rT) (σ : State rT) :
    1 ≤ (limExec ⟨Exp.ofVal v, σ⟩) Set.univ := by
  have h : Tgl (limExec ⟨Exp.ofVal v, σ⟩) (fun _ => True) 0 := by
    refine twp_tgl (GF := GF) (e := Exp.ofVal v) (σ := σ)
      (φ := fun _ => True) (MeasurableSet.const True) ?_
    intro _
    iintro -
    iapply tglWp_value
    itrivial
  simpa using Tgl.termination_ineq h

/-- ε-limit form (`twp_tgl_limit`): a value with the WP triple at every
`ε' > 0` yields `Tgl ... 0`. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Tgl (limExec ⟨Exp.ofVal v, σ⟩) φ 0 := by
  refine twp_tgl_limit (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) hφm ?_
  intro _ _ _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

/-- Pgl bound via adequacy: at ε = 0, the limit-exec measure of the
non-value-or-`¬φ` set is `0`. -/
example (v : Val rT) (σ : State rT) (φ : Val rT → Prop) (hφ : φ v)
    (hφm : MeasurableSet {v : Val rT | φ v}) :
    Pgl 0 (fun ρ => ∃ w, ρ.expr = Exp.ofVal w ∧ φ w)
      (limExec ⟨Exp.ofVal v, σ⟩) := by
  refine twp_pgl_lim (GF := GF) (e := Exp.ofVal v) (σ := σ) (φ := φ) hφm ?_
  intro _
  iintro -
  iapply tglWp_value
  ipureintro
  exact hφ

end AdequacySmokeTests

end TotalEris
end ProbLang
