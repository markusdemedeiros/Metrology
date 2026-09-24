module

public import Metrology.ProbLang.Test

@[expose] public section

/-- ProbLang test runner.

The `example` proofs in `DetStep_discrete` execute at elaboration time, so if this file
compiles the tests have passed. -/
def main : IO Unit := do
  IO.println "All ProbLang tests passed."
