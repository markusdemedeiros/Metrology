module

public import Metrology.TotalEris

@[expose] public section

/-!
# Uniform 1D random walk (total correctness)

The target spec is almost-sure termination of the symmetric 1D random walk
starting at position 1, using presampling against a rank supermartingale (RSM)
to amortize error credits across the recursive calls.

**Status: structural stub (`unifRw1d_terminate` is `sorry`).** The program and
the `finalPos` combinatorics are defined; the spec is blocked on two independent
issues.

⚠ **Off-by-one degeneracy.** `rand z` samples `Finset.Ico 0 z`, i.e. `z` values,
so `rand 1` samples `{0}` *deterministically*. With the program below (`rand 1`,
`alloc 1`, tape bound `1`) every step reads `0`: the walk always steps *down*, so
from position `1` it reaches `0` in a single step. That is a degenerate
deterministic descent, not the symmetric random walk, and verifying it would
prove a vacuous instance. A faithful symmetric walk uses `rand 2` / `alloc 2`,
recovering the `{0,1}` coin flip, and then genuinely needs the RSM machinery.

**Missing prerequisite** for the faithful `rand 2` version: a `twp_presample_rsm`
rule, which rests on unported sequential-amplification theory (`εAmp`, `kwf`) and
an error-induction principle.
-/

open Iris ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-! ## The recursive random-walk body -/

/-- The recursive body of the 1D random walk: from position `n`, stop once
`n < 1`, otherwise flip `rand 1` and step down or up. -/
def unifRw1dRec : Exp rT :=
  pl% rec f n α :=
        if n < #1 then #.unit
        else
          let x := rand(#1, α);
          if x < #1
            then f (n - #1) α
            else f (n + #1) α

/-- Top-level program: `let α = alloc 1 in unifRw1dRec 1 α`. -/
def unifRw1d : Exp rT :=
  pl% let α := alloc(#1); &unifRw1dRec #1 α

/-! ## `finalPos` and the RSM scaffold -/

/-- Position after applying a list of binary walk steps (`0` steps down, `1`
steps up) to a starting position `p₀`. Position `0` is absorbing. -/
def finalPos (p₀ : Nat) : List (Fin 2) → Nat
  | [] => p₀
  | x :: xs =>
      match p₀ with
      | 0 => 0
      | n + 1 =>
          if x = 0 then finalPos n xs
          else finalPos (n + 2) xs

theorem finalPos_append (p₀ : Nat) (li : List (Fin 2)) (i : Fin 2) :
    finalPos p₀ (li ++ [i]) =
      match finalPos p₀ li with
      | 0 => 0
      | n + 1 => if i = 0 then n else n + 2 := by
  induction li generalizing p₀ with
  | nil => simp [finalPos]
  | cons a tl IH =>
    obtain _ | n := p₀
    · simp [finalPos]
    · fin_cases a
      · simpa [finalPos] using IH n
      · simpa [finalPos] using IH (n + 2)

/-- The RSM is `finalPos` lifted to `ℝ≥0∞`. -/
noncomputable def finalPosRsm (p₀ : Nat) (li : List (Fin 2)) : ENNReal :=
  (finalPos p₀ li : ENNReal)

/-- Termination condition: the walk has reached the absorbing position `0`. -/
def termCond (p₀ : Nat) (li : List (Fin 2)) : Prop := finalPos p₀ li = 0

theorem termCond_cons_zero (p₀ : Nat) (li : List (Fin 2)) :
    termCond (p₀ + 1) (0 :: li) ↔ termCond p₀ li := by
  simp [termCond, finalPos]

theorem termCond_cons_one (p₀ : Nat) (li : List (Fin 2)) :
    termCond (p₀ + 1) (1 :: li) ↔ termCond (p₀ + 2) li := by
  simp [termCond, finalPos]

/-- If the walk has not terminated yet, appending a "down" step strictly
decreases `finalPos`. -/
theorem finalPos_dec_aux (p₀ : Nat) (li : List (Fin 2)) :
    ¬ termCond p₀ li → finalPos p₀ (li ++ [0]) < finalPos p₀ li := by
  intro h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [finalPos_append, hn]
  simp

/-- From the starting position `1`, if not terminated, there is a choice that
strictly decreases `finalPos`. -/
theorem finalPos_dec (li : List (Fin 2)) :
    ¬ termCond 1 li → ∃ c : Fin 2, finalPos 1 (li ++ [c]) < finalPos 1 li :=
  fun h => ⟨0, finalPos_dec_aux 1 li h⟩

/-! ## Termination spec -/

/-- Almost-sure termination of the 1D symmetric random walk starting from
position 1. -/
theorem unifRw1d_terminate (E : CoPset) :
    ⊢@{IProp GF} tglWp (rT := rT) E unifRw1d
      (fun v => iprop(⌜v = .unit⌝)) := by
  sorry

end Examples
end TotalEris
end ProbLang
