import ProbLangSampleWidget
import Metrology.Code.Geometric
import Metrology.Code.Samplers
import Metrology.ProbLang.Syntax.Notation

open ProbLang TotalEris.Examples

#sample_session

#sample pl% urand
  with
    title := "Uniform sampler"
    runs := 1000000
    realFun := fun x => if 0 ≤ x && x ≤ 1 then 1 else 0

#sample pl% urand + urand
  with
    title := "Sum of two uniforms"
    bins := 50
    realFun := fun x => max 0 (1 - (x - 1).abs)

#sample pl% urand <= #(.real 0.5)
  with
    title := "Fair coin from Real"
    boolFun := fun _ => 0.5

#sample pl% &geometric #.unit
  with
    title := "Geometric sampler"
    intFun := fun n => if n < 0 then 0 else Float.pow 0.5 (n.toNat.toFloat + 1)

#sample pl%
    let x := rand(#4, #.unit);
    if x = #0 then #true else
    if x = #1 then urand else
    if x = #2 then #(.int (-3)) else
    fail
  with
    title := "Mixed-type sampler"

#sample pl% &Gauss #.unit
  with
    title := "Standard Gaussian",
    runs := 100000
    realFun := fun x => Float.exp (-x * x / 2) / Float.sqrt (2 * 3.141592653589793)

/-! ## Markov chain Monte Carlo

Metropolis–Hastings on `{0, …, 60}`, targeting three bumps over a low floor. ProbLang has no real
multiplication, so the chain is discrete: it proposes a step left or right, and accepts it with
probability `min 1 (w y / w x)`, which is exactly how often `rand(w x) < w y`.

The chain starts at the left edge, and crosses the valleys between the bumps only rarely. A short
chain has not mixed: the histogram piles up on the left while the target (the curve) puts most of
its mass in the middle. A longer chain has mixed, and fills in all three bumps. -/

/-- A triangular bump of height `r` at `c`: `max 0 (r - |x - c|)`. -/
def bump {rT : Type _} : Exp rT := pl%
  fun c, fun r, fun x,
    let d := (if x < c then c - x else x - c);
    if d < r then r - d else #0

/-- The target's weights: bumps at 12, 30 and 48 over a floor of `1` on `{0, …, 60}`, and `0`
elsewhere. -/
def weight {rT : Type _} : Exp rT := pl%
  fun z,
    if z < #0 then #0 else if #60 < z then #0
    else #1 + #3 * &bump #12 #6 z + #5 * &bump #30 #8 z + #4 * &bump #48 #6 z

/-- `weight`, in Lean, for the curve. -/
def weightFn (x : Int) : Int :=
  let bump (c r : Int) := max 0 (r - |x - c|)
  if x < 0 ∨ 60 < x then 0 else 1 + 3 * bump 12 6 + 5 * bump 30 8 + 4 * bump 48 6

/-- The target distribution. -/
def target (x : Int) : Float :=
  Float.ofInt (weightFn x) / Float.ofInt ((List.range 61).map (weightFn ·)).sum

/-- `n` Metropolis–Hastings steps from `x`. -/
def metropolis {rT : Type _} : Exp rT := pl%
  rec step n x :=
    if n = #0 then x
    else
      let y := x + #2 * rand(#2, #.unit) - #1;
      if rand(&weight x, #.unit) < &weight y then step (n - #1) y else step (n - #1) x

-- 5000 steps from `x = 0`: mixed. Each run takes five times as long, so watch it fill in.
#sample pl% &metropolis #5000 #0
  with
    title := "Metropolis–Hastings, 5000 steps"
    runs := 2000
    intFun := target
