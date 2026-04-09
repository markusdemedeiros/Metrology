import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.PrimitiveLaws

/-!
# Semantic Model

Defines the semantic model for the binary logical relation. Key definitions:
`approxisRGS` typeclass, `lrel` (logical relation type = persistent iProp on value pairs),
`refines_def`, and type constructors (`lrel_unit`, `lrel_nat`, `lrel_bool`, `lrel_prod`,
`lrel_sum`, `lrel_arr`, `lrel_rec`, `lrel_forall`, `lrel_exists`, `lrel_ref`, `lrel_tape`).

## Rocq source
`clutch/theories/approxis/model.v`

## External dependencies (not yet ported)
- `clutch.common` (language, ectxi_language, locations)
- `clutch.prelude` (properness)
- `clutch.prob_lang` (notation, lang)
- Iris (na_invariants, proofmode)
-/
