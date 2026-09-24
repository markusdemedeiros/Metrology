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

/-! ## Markov chain Monte Carlo -/

/-- The weights: a sum of three Gaussians, quantized to integers. They round to `0` far from the
centres, so only finitely many are positive. -/
def weightFn (x : Int) : Int :=
  let gauss (c : Int) (a : Float) := a * Float.exp (-Float.ofInt ((x - c) ^ 2) / 18)
  .ofNat (1000 * (gauss (-18) 0.6 + gauss 0 1 + gauss 18 0.8)).round.toUInt64.toNat

/-- The integers where `weightFn` is positive: all within `[-40, 40]`. -/
def support : List Int := ((List.range 81).map (Int.ofNat · - 40)).filter (0 < weightFn ·)

/-- `weightFn` as a program: a table of its positive values, and `0` elsewhere. -/
def weight {rT : Type _} : Exp rT :=
  let table := support.foldr (init := pl% #0) fun x rest =>
    pl% if z = #(.int x) then #(.int (weightFn x)) else &rest
  .lam (table.close (.named "z"))

/-- The target distribution. -/
def target (x : Int) : Float :=
  Float.ofInt (weightFn x) / Float.ofInt (support.map weightFn).sum

def metropolis {rT : Type _} : Exp rT := pl%
  rec step n x :=
    if n = #0 then x
    else
      let y := x + #2 * rand(#2, #.unit) - #1;
      if rand(&weight x, #.unit) < &weight y then step (n - #1) y else step (n - #1) x

#sample pl% &metropolis #5000 #(.int (-24))
  with
    title := "Metropolis–Hastings, 5000 steps"
    runs := 2000
    intFun := target

-- A few blank lines so the last #sample doesn't collide with the restart file button
#eval IO.println "\u00a0\n\u00a0\n\u00a0\n\u00a0"
