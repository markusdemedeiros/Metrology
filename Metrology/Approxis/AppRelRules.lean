import Metrology.Approxis.EctxLifting
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Proofmode
import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.CouplingRules

/-!
# Relational Rules

Core relational rules for symbolic execution. Key lemmas: `refines_pure_l`, `refines_pure_r`
(pure step on LHS/RHS), `refines_wp_l` (embed WP into refinement), `refines_atomic_l`
(atomic LHS steps), `refines_bind` (bind/sequencing), `refines_ret` (return values).

## Rocq source
`clutch/theories/approxis/app_rel_rules.v`

## External dependencies (not yet ported)
- `clutch.common` (language, ectx_language, ectxi_language, locations)
- `clutch.prelude` (fin)
- `clutch.prob_lang` (notation, lang)
- `clutch.prob_lang.spec` (spec_ra, spec_rules, spec_tactics)
- `clutch.base_logic` (spec_update)
- Iris (proofmode, algebra.list)
- stdpp (coPset, namespaces)
-/
