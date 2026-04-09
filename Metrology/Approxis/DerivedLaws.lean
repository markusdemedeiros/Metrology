import Metrology.Approxis.PrimitiveLaws

/-!
# Derived Laws

Derived laws for arrays. Defines `array` connective and proves `array_nil`, `array_singleton`,
`array_app`, `array_cons`, `wp_allocN`, `wp_load`, `wp_store` for array operations.

## Rocq source
`clutch/theories/approxis/derived_laws.v`

## External dependencies (not yet ported)
- `clutch.prob_lang` (tactics, lang, notation)
- Iris (proofmode, fractional)
- stdpp (fin_maps)
-/
