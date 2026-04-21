import Metrology.Approxis.AppWeakestpre
import Metrology.Iris.AppProgram
import Metrology.Iris.SpecProgram
import Metrology.Iris.SpecUpdate
import Metrology.Iris.ErrorCredits

/-!
# Primitive Laws

Instantiates the abstract `ApproxisWpGS` at the concrete ProbLang ghost state
(program heap + tapes, spec heap + tapes, error credits) and proves the
primitive WP rules for each language primitive.

## Rocq source

`clutch/theories/approxis/primitive_laws.v`

## Concrete ghost-state instantiation

Rocq bundles program-side heap/tape ghost-maps + spec + error into a single
record `approxisGS` (primitive_laws.v:12–24), so all four γ-names are
allocated together and cannot alias. We reproduce the same guarantee by
bundling the three component GS classes into a single `ApproxisGS` class.

- `AppGS` (from `Metrology/Iris/AppProgram.lean`) — program heap + tapes γ's.
- `SpecGS` (from `Metrology/Iris/SpecProgram.lean`) — spec heap + tapes + prog γ's.
- `ECGS` (from `Metrology/Iris/ErrorCredits.lean`) — error-credit γ.

`ApproxisGS` extends all three (plus `InvGS_gen`). Downstream code should
depend on `[ApproxisGS GF]` alone; instances of `AppGS`/`SpecGS`/`ECGS` are
derived automatically. This (i) prevents γ-aliasing between program and spec
heaps (since any `ApproxisGS` instance instantiates all four γ-names at once)
and (ii) collapses the four-instance requirement at every call site to one.

**Status:** currently only the `ApproxisWpGS` instance is synthesized. The
actual primitive WP lemmas (`wp_alloc`, `wp_load`, ...) are the next
piece of work — see `clutch/theories/approxis/primitive_laws.v:162–505`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped AppGS

namespace ProbLang

/-! ## Bundled ghost-state class

Mirrors Rocq's `approxisGS` record. Extending all four components in one
class ensures joint allocation of γ-names and prevents accidental aliasing
of program and spec heaps. -/
class ApproxisGS (hlc : outParam Bool) (GF : BundledGFunctors)
    extends AppGS GF, SpecGS GF, ECGS GF, InvGS_gen hlc GF

/-! ## `ApproxisWpGS` instance synthesis

Given `[ApproxisGS hlc GF]`, package the concrete `stateInterp`/`errInterp`
as an `ApproxisWpGS` instance. Mirrors `approxisGS_irisGS` in
`primitive_laws.v:48–52`. -/

section ApproxisInstance

variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisGS hlc GF]

noncomputable instance approxisWpGS_of_components : ApproxisWpGS GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

end ApproxisInstance

end ProbLang
