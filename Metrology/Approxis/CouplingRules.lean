import Metrology.Approxis.Lifting
import Metrology.Approxis.EctxLifting
import Metrology.Approxis.PrimitiveLaws

/-!
# Coupling Rules

Coupling rules for tapes and randomness. Key lemmas: `wp_couple_tapes` (couple two tapes
with error), `ARcoupl_steps_ctx_bind_r`. Contains concrete rules for coupling `rand`
operations between program and spec sides.

## Rocq source
`clutch/theories/approxis/coupling_rules.v`

## External dependencies (not yet ported)
- `clutch.prelude` (stdpp_ext, fin)
- `clutch.prob_lang` (lang, notation, tactics, metatheory, erasure)
- `clutch.prob_lang.spec` (spec_rules)
- Iris (proofmode)
- stdpp (namespaces)
-/
