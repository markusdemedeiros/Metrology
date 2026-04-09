import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.EctxLifting

/-!
# Primitive Laws

Instantiates the abstract WP for `prob_lang`. Defines `approxisGS` (concrete ghost state:
heap, tapes, spec, error credits), heap/tape notations, and the `approxisWpGS` instance.

## Rocq source
`clutch/theories/approxis/primitive_laws.v`

## External dependencies (not yet ported)
- `clutch.base_logic` (error_credits)
- `clutch.prob_lang` (class_instances, tactics, lang, notation, metatheory)
- `clutch.prob_lang.spec` (spec_ra, spec_rules, spec_tactics)
- Iris (proofmode, ghost_map)
-/
