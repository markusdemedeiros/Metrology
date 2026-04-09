import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.PrimitiveLaws

/-!
# Adequacy

Adequacy of the WP. Proves that WP entailments imply `ARcoupl` between execution
distributions. Key lemmas: `wp_adequacy_spec_coupl`, `wp_adequacy_prog_coupl`,
`wp_adequacy_val_fupd`, `wp_adequacy_error_lim`.

## Rocq source
`clutch/theories/approxis/adequacy.v`

## External dependencies (not yet ported)
- `clutch.prelude` (stdpp_ext, iris_ext)
- `clutch.prob_lang` (erasure, notation)
- `clutch.common` (language)
- `clutch.base_logic` (error_credits)
- `clutch.prob` (distribution, couplings_app)
- Iris (proofmode, ghost_map, invariants, fancy_updates, algebra.excl)
-/
