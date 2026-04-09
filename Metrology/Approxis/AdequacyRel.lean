import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Adequacy

/-!
# Relational Adequacy

Relational adequacy theorems. Key results:

```
Theorem approximates_coupling :
  (REL e1 << e2 @ E : A with error ε) ⟹ ARcoupl(lim_exec(e1,σ1), lim_exec(e2,σ2), φ, ε)

Corollary refines_coupling :
  (REL e1 << e2 @ E : A) ⟹ Deterministic coupling e1 e2
```

## Rocq source
`clutch/theories/approxis/adequacy_rel.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (lang)
- Iris (proofmode, na_invariants)
-/
