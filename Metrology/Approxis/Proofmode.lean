import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Lifting
import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.DerivedLaws

/-!
# Proof Mode

Registers Approxis WP with Iris proof mode tactics. Defines instances for WP tactics
(base, bind, pure, heap, tape).

## Rocq source
`clutch/theories/approxis/proofmode.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (lang, notation, class_instances, tactics, wp_tactics)
- Iris (proofmode)
-/
