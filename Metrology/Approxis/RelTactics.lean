import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.AppRelRules
import Metrology.Approxis.Proofmode

/-!
# Relational Tactics

Relational proof tactics: `rel_bind_l`, `rel_bind_r`, `rel_pure_l`, `rel_pure_r`,
`rel_values`, etc. Unification-based approach for relational symbolic execution.

## Rocq source
`clutch/theories/approxis/rel_tactics.v`

## External dependencies (not yet ported)
- `clutch.common` (language, ectxi_language, locations)
- `clutch.prob_lang` (class_instances, notation, tactics, lang)
- `clutch.prob_lang.spec` (spec_tactics)
- Iris (proofmode, invariants)
- clutch.prelude (stdpp_ext)
-/
