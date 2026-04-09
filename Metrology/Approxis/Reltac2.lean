import Metrology.Approxis.Model
import Metrology.Approxis.AppRelRules
import Metrology.Approxis.RelTactics

/-!
# Relational Tactics v2

High-performance alternative to `RelTactics` using Ltac2. Syntactically traverses the goal
to find the unique redex. Automatically generates names from program variable names.
Provides `iredl`/`iredr` tactics for LHS/RHS symbolic evaluation.

## Rocq source
`clutch/theories/approxis/reltac2.v`

## External dependencies (not yet ported)
- `clutch.prelude` (stdpp_ext)
- `clutch.prob_lang` (lang, notation)
- Ltac2 (Ltac2, Printf, String, Char, Fresh, Ident)
- Stdlib (ZArith, String)
-/
