import Metrology.ProbLang.Interp.BigStepIO
import Metrology.ProbLang.Discrete
import Metrology.ProbLang.Syntax.Notation

/-! Benchmark for the big-step interpreter: `lake build bench && .lake/build/bin/bench [n ...]`.

Reuses the test-only `ProbLangℝ Int` instance from `BigStepIOTest.lean`. -/

open ProbLang ProbLang.Interp MeasureTheory

unsafe def testUnifUnitImpl : Measure Int := unsafeCast ()

@[implemented_by testUnifUnitImpl]
def testUnifUnit : Measure Int := instProbLangℝInt.unifUnit

instance (priority := high) testInst : ProbLangℝ Int where
  toMeasurableSpace := Int.instMeasurableSpace
  beq a b := decide (a = b)
  eq_of_beq := instProbLangℝInt.eq_of_beq
  rfl := instProbLangℝInt.rfl
  default := 0
  measurableSet_diagonal := instProbLangℝInt.measurableSet_diagonal
  instDecidableEq := Int.decEq
  unifUnit := testUnifUnit
  unifUnit_isProbabilityMeasure := instProbLangℝInt.unifUnit_isProbabilityMeasure
  unifUnitSupport := instProbLangℝInt.unifUnitSupport
  unifUnitSupportMeasurable := instProbLangℝInt.unifUnitSupportMeasurable
  unifUnitIsConcentrated := instProbLangℝInt.unifUnitIsConcentrated
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  measurable_realLt := instProbLangℝInt.measurable_realLt
  measurable_realLe := instProbLangℝInt.measurable_realLe
  realAdd a b := a + b
  realNeg a := -a
  realOfInt z := z
  realFrac _ := 0
  measurable_realAdd := instProbLangℝInt.measurable_realAdd
  measurable_realNeg := instProbLangℝInt.measurable_realNeg
  measurable_realFrac := instProbLangℝInt.measurable_realFrac

/-- On `Int`, `unifUnit` is uniform on `{0, 1}`. -/
instance : UnifUnitSampler Int := ⟨do return (← IO.rand 0 1)⟩

/-- Tail-recursive loop: `loop n acc = if n = 0 then acc else loop (n - 1) (acc + n)`. -/
def loopExp : Exp Int := pl(rec loop n := fun acc, if n = #0 then acc else loop (n - #1) (acc + n))

/-- Non-tail recursion: `sum n = if n = 0 then 0 else n + sum (n - 1)`. -/
def sumExp : Exp Int := pl(rec sum n := if n = #0 then #0 else n + sum (n - #1))

def time (label : String) (prog : Exp Int) : IO Unit := do
  let t0 ← IO.monoNanosNow
  match ← (run (.eval [] prog default) |>.toBaseIO) with
  | .ok r =>
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {repr r.val.rb} in {(t1 - t0) / 1000000} ms"
  | .error e => IO.println s!"{label}: error {e}"

def timeSubst (label : String) (prog : Exp Int) : IO Unit := do
  let t0 ← IO.monoNanosNow
  match ← (runSubst ⟨prog, default⟩ |>.toBaseIO) with
  | .ok ⟨v, _⟩ =>
    let t1 ← IO.monoNanosNow
    IO.println s!"{label} [subst]: {repr v} in {(t1 - t0) / 1000000} ms"
  | .error e => IO.println s!"{label} [subst]: error {e}"



def main (args : List String) : IO Unit := do
  let sizes := (args.map String.toNat!).toArray
  let sizes := if sizes.isEmpty then #[1000, 10000, 100000, 1000000] else sizes
  for n in sizes do
    time s!"loop {n}" pl({loopExp} #(.int n) #0)
    timeSubst s!"loop {n}" pl({loopExp} #(.int n) #0)
  for n in sizes do
    time s!"sum {n}" pl({sumExp} #(.int n))
    timeSubst s!"sum {n}" pl({sumExp} #(.int n))
