/-!
# Approximate Weakest Precondition

Defines the approximate weakest precondition (WP) for the coupled program logic.
Key definitions: `spec_coupl` modality, `prog_coupl` modality, and the WP fixpoint.

## Rocq source
`clutch/theories/approxis/app_weakestpre.v`

## External dependencies (not yet ported)
- `clutch.prelude` (stdpp_ext, iris_ext, NNRbar)
- `clutch.common` (language, erasable)
- `clutch.base_logic` (spec_update)
- `clutch.prob` (couplings_app, distribution)
- Iris (fancy_updates, fixpoint_mono, big_op)
- Stdlib (Reals, Psatz)
-/
