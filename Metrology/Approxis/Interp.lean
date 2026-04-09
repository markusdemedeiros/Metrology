import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model

/-!
# Type Interpretation

Interpretation of syntactic types as semantic types. Defines `interp : type -> lrel`
(a nonexpansive function mapping each syntactic type to a semantic logical relation
given a type-variable environment). Also proves `unboxed_type_sound` and `eq_type_sound`.

## Rocq source
`clutch/theories/approxis/interp.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (metatheory, lang)
- `clutch.prelude` (asubst, properness)
- `clutch.prob_lang.typing` (types, contextual_refinement)
- Iris (proofmode, algebra.list)
-/
