module

public import Metrology.TotalEris

@[expose] public section

/-!
# Uniform 1D random walk (total correctness)

Port of `clutch/theories/eris/examples/random_walk.v`. The target spec is
almost-sure termination of the symmetric 1D random walk starting at
position 1, using the presampling-via-RSM rule (`twp_presample_rsm`) to
amortize bookkeeping across recursive calls.

**Status: structural stub (`unif_rw_1d_terminate` is `sorry`).** The
program and the `final_pos` combinatorics are defined; the spec is
blocked on two independent issues.

⚠️ **Off-by-one degeneracy.** Rocq's `rand #1` samples `fin (S 1) =
{0,1}` — a genuine coin flip, which is *why* the Rocq proof needs the
rank-supermartingale (RSM) amplification machinery for a.s. termination.
The Lean `ProbLang` `rand z` instead samples `Finset.Ico 0 z` (`z`
values), so `rand 1` samples `{0}` **deterministically**. With the
program below (`rand 1`, `alloc 1`, tape bound `1`) every step reads
`0`, i.e. the walk always steps *down*: from position `1` it reaches `0`
in a single step. This is a degenerate deterministic descent, **not the
symmetric random walk**, so verifying it via `twp_presample_rsm` would
prove a vacuous instance. A faithful symmetric walk would use `rand 2` /
`alloc 2` (recovering the `{0,1}` flip) and then genuinely require RSM.

**Prerequisites not yet ported** (needed for the faithful `rand 2`
version):

* `twp_presample_rsm` and its supporting RSM machinery (see
  `clutch/theories/eris/presample_rules.v:1912`), which sits on the
  **entirely unported** `seq_amplification.v` (`εAmp`/`kwf`/`lt_1_k`),
  the `twp_presample_amplify_rsm{,_aux}` chain, and the `ec_ind_incr`
  error-induction principle — the "1000-line chase" the WISHLIST warns
  against.

✅ Already done: state-step disjunct of `glm` (`glmStateStep`,
`glm_state_step` intro), basic `twp_presample` *and*
`twp_presample_adv_comp` (both fully proved in `PresampleRules.lean`),
all pure `Tgl` state-step lemmas (`tgl_state_step`, `dbind_state_step`),
and the pure `final_pos` combinatorics below.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

set_option linter.unusedSectionVars false

variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-! ## The recursive random-walk body

  ```
  rec "f" "n" "α" :=
    if n < 1 then ()
    else let x = rand("α") 1 in
         if x < 1 then "f" (n - 1) "α"
                  else "f" (n + 1) "α"
  ```

  Locally-nameless encoding: outer `fix` binds `"f"` (bvar 2 inside the
  innermost body); the two `lam`s bind `"n"` (bvar 1) and `"α"` (bvar 0). -/

/-- The recursive body of the 1D random walk. -/
def unifRw1dRec : Exp rT :=
  -- rec "f" "n" "α"  ≡  fix (lam (lam body))
  Exp.fix <| Exp.lam <| Exp.lam <|
    -- if n < 1 then ()
    Exp.cond
      (Exp.binop .lt (Exp.bvar 1) (Exp.lit (.int 1)))
      (Exp.lit .unit)
      -- else let x = rand α 1 in (let-binds bvar 0 going forward; we use
      -- a `lam`+`app` desugar for `let x = e1 in e2`).
      (Exp.app
        (Exp.lam <|
          -- inner body with x = bvar 0, α = bvar 1, n = bvar 2, f = bvar 3.
          Exp.cond
            (Exp.binop .lt (Exp.bvar 0) (Exp.lit (.int 1)))
            -- f (n - 1) α
            (Exp.app
              (Exp.app (Exp.bvar 3)
                (Exp.binop .minus (Exp.bvar 2) (Exp.lit (.int 1))))
              (Exp.bvar 1))
            -- f (n + 1) α
            (Exp.app
              (Exp.app (Exp.bvar 3)
                (Exp.binop .plus (Exp.bvar 2) (Exp.lit (.int 1))))
              (Exp.bvar 1)))
        (Exp.rand (Exp.lit (.int 1)) (Exp.bvar 0)))

/-- Top-level program: `let α = alloc 1 in unifRw1dRec 1 α`. -/
def unifRw1d : Exp rT :=
  Exp.app
    (Exp.lam <|
      Exp.app
        (Exp.app unifRw1dRec (Exp.lit (.int 1)))
        (Exp.bvar 0))
    (Exp.alloc (Exp.lit (.int 1)))

/-! ## `final_pos` and the RSM scaffold

`final_pos p0 li` is the position after applying the binary-coded
walk `li` (where `0` is "step down", `1` is "step up") starting from
`p0`. Reaching `0` is absorbing. Rocq: `random_walk.v:30`. -/

/-- Position after applying a list of binary walk steps to a starting
position `p0`. `0` is absorbing. -/
def final_pos (p₀ : Nat) : List (Fin 2) → Nat
  | [] => p₀
  | x :: xs =>
      match p₀ with
      | 0 => 0
      | n + 1 =>
          if x = 0 then final_pos n xs
          else final_pos (n + 2) xs

/-- Appending a single step: explicit case split on `final_pos p₀ li`. -/
theorem final_pos_app (p₀ : Nat) (li : List (Fin 2)) (i : Fin 2) :
    final_pos p₀ (li ++ [i]) =
      match final_pos p₀ li with
      | 0 => 0
      | n + 1 => if i = 0 then n else n + 2 := by
  induction li generalizing p₀ with
  | nil => simp [final_pos]
  | cons a tl IH =>
    rcases p₀ with _ | n
    · simp [final_pos]
    · simp only [List.cons_append, final_pos]
      -- Case only on `a = 0`; do NOT use `split_ifs`, which would also
      -- split the `if i = 0` inside the match arm and break the `IH` match.
      by_cases h : a = 0
      · rw [if_pos h, if_pos h]; exact IH n
      · rw [if_neg h, if_neg h]; exact IH (n + 2)

/-- The RSM is just `final_pos` lifted to `ℝ≥0∞`. The actual RSM
machinery (decrease + boundedness lemmas) is in `presample_rules.v` and
remains to be ported. -/
noncomputable def final_pos_rsm (p₀ : Nat) (li : List (Fin 2)) : ENNReal :=
  (final_pos p₀ li : ENNReal)

/-- Termination condition: `final_pos = 0`. -/
def term_cond (p₀ : Nat) (li : List (Fin 2)) : Prop := final_pos p₀ li = 0

theorem term_cond_0 (p₀ : Nat) (li : List (Fin 2)) :
    term_cond (p₀ + 1) (0 :: li) ↔ term_cond p₀ li := by
  unfold term_cond
  simp [final_pos]

theorem term_cond_1 (p₀ : Nat) (li : List (Fin 2)) :
    term_cond (p₀ + 1) (1 :: li) ↔ term_cond (p₀ + 2) li := by
  unfold term_cond
  simp [final_pos]

/-- `final_pos_rsm` is non-negative (trivially, as a Nat coerced to ENNReal). -/
theorem final_pos_rsm_pos (li : List (Fin 2)) :
    0 ≤ final_pos_rsm 1 li :=
  zero_le _

/-- If the walk hasn't terminated yet, appending `0` (a "down" step)
strictly decreases `final_pos`. Rocq: `final_pos_dec_aux`. -/
theorem final_pos_dec_aux (p₀ : Nat) (li : List (Fin 2)) :
    ¬ term_cond p₀ li → final_pos p₀ (li ++ [0]) < final_pos p₀ li := by
  induction li generalizing p₀ with
  | nil =>
    intro Hterm
    rcases p₀ with _ | n
    · exact absurd rfl Hterm
    · simp [final_pos]
  | cons a tl IH =>
    intro Hterm
    rcases p₀ with _ | n
    · exact absurd rfl Hterm
    · simp only [final_pos, List.cons_append]
      split_ifs with h
      · refine IH n ?_
        intro Htc
        apply Hterm
        rw [show (a :: tl) = (0 :: tl) by rw [h]]
        exact (term_cond_0 n tl).mpr Htc
      · -- a is nonzero, so a = 1 in Fin 2.
        have ha : a = 1 := by
          fin_cases a
          · exact absurd rfl h
          · rfl
        refine IH (n + 2) ?_
        intro Htc
        apply Hterm
        rw [show (a :: tl) = (1 :: tl) by rw [ha]]
        exact (term_cond_1 n tl).mpr Htc

/-- From the starting position `1`, if not terminated, there exists a
choice that strictly decreases `final_pos`. Rocq: `final_pos_dec`. -/
theorem final_pos_dec (li : List (Fin 2)) :
    ¬ term_cond 1 li → ∃ c : Fin 2, final_pos 1 (li ++ [c]) < final_pos 1 li :=
  fun h => ⟨0, final_pos_dec_aux 1 li h⟩

/-! ## Termination spec

Mirrors `random_walk.v` Lemma `unif_rw_1d_terminate` (around line 250).
The proof uses `twp_presample_rsm` with the RSM `final_pos_rsm` to
amortize error credits across the recursion. -/

/-- Almost-sure termination of the 1D symmetric random walk starting
from position 1. Rocq: `unif_rw_1d_terminate`.

**Status: `sorry`.** Blocked on the RSM/`seq_amplification` port and the
`rand 1` off-by-one degeneracy — see the module docstring at the top of
this file for the full analysis. -/
theorem unif_rw_1d_terminate (E : CoPset) :
    ⊢@{IProp GF} tglWp (rT := rT) E unifRw1d
      (fun v => iprop(⌜v = ⟨.lit .unit, IsVal.lit⟩⌝)) := by
  sorry

end Examples
end TotalEris
end ProbLang
