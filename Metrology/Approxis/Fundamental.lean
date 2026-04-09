import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.Compatibility
import Metrology.Approxis.AppRelRules
import Metrology.Approxis.RelTactics
import Metrology.Approxis.Interp

/-!
# Fundamental Theorem

Fundamental theorem of the logical relation: well-typed terms are related to themselves.
Key results: `bin_log_related_under_typed_ctx` (precongruence).

```
Theorem fundamental (Δ : type context) (Γ : term context) (e : expr) (τ : type) :
  Γ ⊢ₜ e : τ → ⊢ ⟨Δ;Γ⟩ ⊨ e ≤log≤ e : τ
```

## Rocq source
`clutch/theories/approxis/fundamental.v`

## External dependencies (not yet ported)
- `clutch.prelude` (stdpp_ext)
- `clutch.prob_lang` (metatheory, notation, lang)
- `clutch.prob_lang.typing` (types)
- Iris (invariants, proofmode)
-/
