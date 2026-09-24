import Metrology.ProbLang.Interp.Sample

/-! The sampler behind `#sample`: `problang-sample <engine> <runs> <ms>` reads a program as one
line of JSON on stdin, runs it `runs` times, and prints a `Summary` of the runs since the last
one as a line of JSON on stdout about every `ms` milliseconds, and at the end.

The caller holds stdin open while it wants results; the sampler stops as soon as stdin closes,
so that it never outlives a Lean server that crashed or was restarted. -/

open Lean ProbLang ProbLang.Interp.Sample

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let program ← stdin.getLine
  let [name, runs, ms] := args
    | IO.eprintln "usage: problang-sample <engine> <runs> <ms>"; return 1
  let some (_, run) := engines.find? (·.1 == name)
    | IO.eprintln s!"unknown engine: {name}"; return 1
  let (some runs, some ms) := (runs.toNat?, ms.toNat?)
    | IO.eprintln s!"not numbers: {runs} {ms}"; return 1
  match decodeProgram program with
  | .error err =>
    IO.eprintln s!"cannot read the program: {err}"
    return 1
  | .ok e =>
    -- Stop if the caller goes away.
    let _ ← IO.asTask (prio := .dedicated) do
      discard stdin.readToEnd
      IO.Process.exit (α := Unit) 1
    let stdout ← IO.getStdout
    draw run e runs ms fun s => do
      stdout.putStrLn s.toJson.compress
      stdout.flush
    -- Exit now rather than wait for the task above.
    IO.Process.exit 0
