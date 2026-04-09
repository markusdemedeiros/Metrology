import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Lifting

/-!
# Evaluation Context Lifting

Derived lifting lemmas for evaluation-context-based languages.
Key lemmas: `wp_lift_head_step_prog_couple`, `wp_lift_head_step`,
`wp_lift_atomic_head_step_fupd`, `wp_lift_pure_det_head_step_no_fork`.

## Rocq source
`clutch/theories/approxis/ectx_lifting.v`

## External dependencies (not yet ported)
- `clutch.common` (ectx_language)
- Iris (proofmode)
-/
