import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Lifting

/-!
# Evaluation Context Lifting

Derived lifting lemmas for evaluation-context-based languages.

## Port status (2026-04-24): COMPLETE

All 6 lemmas from `clutch/theories/approxis/ectx_lifting.v` are already
ported directly into `Metrology/Approxis/AppWeakestpre.lean` (they were
written alongside the WP definition rather than in a separate file):

| Rocq lemma (line in ectx_lifting.v) | Lean location |
|---|---|
| `wp_lift_head_step_prog_couple` (21) | AppWeakestpre.lean:2749 |
| `wp_lift_head_step` (36)              | AppWeakestpre.lean:2770 |
| `wp_lift_atomic_head_step_fupd` (51)  | AppWeakestpre.lean:2795 |
| `wp_lift_atomic_head_step` (68)       | AppWeakestpre.lean:2819 |
| `wp_lift_pure_det_head_step` (85)     | AppWeakestpre.lean:2844 |
| `wp_lift_pure_det_head_step'` (95)    | AppWeakestpre.lean:2855 |

Rocq source: `clutch/theories/approxis/ectx_lifting.v` (106 lines).

This file imports the dependencies so downstream clients can
`import Metrology.Approxis.EctxLifting` per the Rocq layering without
pulling all of `AppWeakestpre` by hand; the lemmas themselves live in
`AppWeakestpre.lean`.
-/
