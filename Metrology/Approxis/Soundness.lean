import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.AdequacyRel
import Metrology.Approxis.Interp
import Metrology.Approxis.Fundamental

/-!
# Soundness

Soundness of the logical relation w.r.t. contextual refinement. Key theorems:

```
Lemma refines_sound :
  (∀ `{approxisRGS}, REL e << e' : interp τ Δ) → e ≤ctx≤ e' : τ

Lemma refines_sound_open :
  (∀ `{approxisRGS}, ⟨Δ;Γ⟩ ⊨ e ≤log≤ e' : τ) → e ≤ctx≤ e' : τ
```

## Rocq source
`clutch/theories/approxis/soundness.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (notation, metatheory, lang)
- `clutch.prob_lang.typing` (contextual_refinement)
- Iris (proofmode)
- Stdlib (Reals)
-/
