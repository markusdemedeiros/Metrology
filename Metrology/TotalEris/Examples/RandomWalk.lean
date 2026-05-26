module

public import Metrology.TotalEris

@[expose] public section

/-!
# Uniform 1D random walk (total correctness)

Port of `clutch/theories/eris/examples/random_walk.v`. The target spec is
almost-sure termination of the symmetric 1D random walk starting at
position 1, using the presampling-via-RSM rule (`twp_presample_rsm`) to
amortize bookkeeping across recursive calls.

**Status: structural stub.** The program is defined; the `final_pos` /
RSM scaffolding and the spec lemmas are pending. The key prerequisites
not yet ported are:

* the state-step disjunct of `glm` (needed by any presampling rule),
* `twp_presample_rsm` and its supporting RSM machinery (see
  `clutch/theories/eris/presample_rules.v:1912`),
* the `final_pos` Lean definition (mirrors `random_walk.v:30`).

-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS hlc GF]

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
def unifRw1dRec : Exp :=
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
def unifRw1d : Exp :=
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
  | cons a as IH =>
    rcases p₀ with _ | n
    · simp [final_pos]
    · simp only [List.cons_append, final_pos]
      split_ifs with h
      · exact IH n
      · exact IH (n + 2)

/-- The RSM is just `final_pos` lifted to `ℝ≥0∞`. The actual RSM
machinery (decrease + boundedness lemmas) is in `presample_rules.v` and
remains to be ported. -/
noncomputable def final_pos_rsm (p₀ : Nat) (li : List (Fin 2)) : ENNReal :=
  (final_pos p₀ li : ENNReal)

/-- Termination condition: `final_pos = 0`. -/
def term_cond (p₀ : Nat) (li : List (Fin 2)) : Prop := final_pos p₀ li = 0

theorem term_cond_0 (p₀ : Nat) (li : List (Fin 2)) :
    term_cond (p₀ + 1) (0 :: li) ↔ term_cond p₀ li := by
  unfold term_cond final_pos
  simp

theorem term_cond_1 (p₀ : Nat) (li : List (Fin 2)) :
    term_cond (p₀ + 1) (1 :: li) ↔ term_cond (p₀ + 2) li := by
  unfold term_cond final_pos
  simp

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
  | cons a as IH =>
    intro Hterm
    rcases p₀ with _ | n
    · exact absurd rfl Hterm
    · simp only [final_pos, List.cons_append]
      split_ifs with h
      · refine IH n ?_
        intro Htc
        apply Hterm
        rw [show (a :: as) = (0 :: as) by rw [h]]
        exact (term_cond_0 n as).mpr Htc
      · -- a is nonzero, so a = 1 in Fin 2.
        have ha : a = 1 := by
          fin_cases a
          · exact absurd rfl h
          · rfl
        refine IH (n + 2) ?_
        intro Htc
        apply Hterm
        rw [show (a :: as) = (1 :: as) by rw [ha]]
        exact (term_cond_1 n as).mpr Htc

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

**Status: sorry.** Remaining prerequisites:
* `final_pos`, `final_pos_app`, `final_pos_rsm`, `term_cond` definitions
  and combinatorial lemmas (~50 Lean lines, pure Nat/List induction).
* `twp_presample_rsm` — the RSM-driven presampling Löb-style rule
  (~150 Rocq lines in `presample_rules.v:1912`, requires real RSM
  infrastructure).

✅ Already done: state-step disjunct of `glm` (`glmStateStep`,
`glm_state_step` intro), basic `twp_presample` (in `PresampleRules.lean`),
all pure `Tgl` state-step lemmas (`tgl_state_step`, `dbind_state_step`). -/
theorem unif_rw_1d_terminate (E : CoPset) :
    ⊢@{IProp GF} tglWp E unifRw1d
      (fun v => iprop(⌜v = ⟨.lit .unit, IsVal.lit⟩⌝)) := by
  sorry

end Examples
end TotalEris
end ProbLang
