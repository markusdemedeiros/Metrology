import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Proofmode
import Metrology.Approxis.Model
import Metrology.Approxis.RelTactics
import Metrology.Approxis.AppRelRules

/-!
# Compatibility Lemmas

Structural compatibility lemmas for the logical relation — one rule per language construct.
Key lemmas: `refines_pair`, `refines_injl`, `refines_injr`, `refines_app`, `refines_seq`,
`refines_pack`, `refines_if`, `refines_case`, `refines_fold`, `refines_unfold`.

## Rocq source
`clutch/theories/approxis/compatibility.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (notation, lang)
- stdpp (namespaces)
-/
