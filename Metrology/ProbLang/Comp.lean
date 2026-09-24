module

@[expose] public section

/-! # Evaluator computations as data

An evaluator step returns a `Comp`: a tree recording what the evaluator does next. `C` is
the type of recursive calls and `R` the type of results. The interpreter runs these trees
in `IO` (`Interp.drive`), and the proofs read them as measures (`Comp.interpM`), so both
act on the same trees.
-/

namespace ProbLang

/-- An evaluator computation with recursive calls in `C` and results in `R`. -/
inductive Comp (rT : Type u) (C R : Type u) where
  | ret (r : R)
  | bind (c : Comp rT C R) (k : R → Comp rT C R)
  /-- A recursive call of the evaluator. -/
  | call (c : C)
  /-- Get stuck, or `fail`. -/
  | stuck (msg : String)
  /-- Sample an integer uniformly from `[0, z)`, or return `-1` when `z ≤ 0`. -/
  | sample (z : Int) (k : Int → Comp rT C R)
  /-- Sample a real from `ProbLangℝ.unifUnit`. -/
  | sampleReal (k : rT → Comp rT C R)

end ProbLang
