import Metrology.ProbLang.Interp.BigStepIO
import Metrology.ProbLang.Discrete
import Metrology.ProbLang.Syntax.Notation

/-! Benchmark for the big-step interpreter: `lake build bench && .lake/build/bin/bench [n ...]`. -/

open ProbLang ProbLang.Interp MeasureTheory

/-- Tail-recursive loop: `loop n acc = if n = 0 then acc else loop (n - 1) (acc + n)`. -/
def loopExp : Exp Float :=
  pl(rec loop n := fun acc, if n = #0 then acc else loop (n - #1) (acc + n))

/-- Non-tail recursion: `sum n = if n = 0 then 0 else n + sum (n - 1)`. -/
def sumExp : Exp Float := pl(rec sum n := if n = #0 then #0 else n + sum (n - #1))

def time (label : String) (prog : Exp Float) : IO Unit := do
  let t0 ← IO.monoNanosNow
  match ← (run (.eval [] prog default) |>.toBaseIO) with
  | .ok r =>
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {repr r.val.rb} in {(t1 - t0) / 1000000} ms"
  | .error e => IO.println s!"{label}: error {e}"

def timeSubst (label : String) (prog : Exp Float) : IO Unit := do
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
