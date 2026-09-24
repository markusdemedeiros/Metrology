import ProbLangSampleWidget
import Metrology.Code.Geometric
import Metrology.Code.Samplers
import Metrology.ProbLang.Syntax.Notation

open ProbLang TotalEris.Examples

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

#sample pl%
    &Gauss #.unit
  with
    title := "Standard Gaussian",
    runs := 100000
    realFun := fun x => Float.exp (-x * x / 2) / Float.sqrt (2 * 3.141592653589793)
