# DiffTest TODO

## `elabDetHeadStep` cases to add

Each item corresponds to a `HeadStep` case in `Opsem.lean`.
Add a helper lemma (`DetHeadStep.xxx`) and a matching branch in `elabDetHeadStep`.

### Pure (state-independent, no proof obligations beyond value checks)

- [x] `snd (pair v1 v2)` → `v2`
- [x] `cond (lit (bool true)) et ef` → `et`
- [x] `cond (lit (bool false)) et ef` → `ef`
- [x] `binop op v1 v2` → `op.eval v1 v2`

- [x] `unop op v` → `op.eval v`
- [x] `app (letrec f x body) v` → `body[f ↦ letrec f x body][x ↦ v]`

### Sum types

- [x] `case (inl v) el er` → `el.app v`
- [x] `case (inr v) el er` → `er.app v`

### Heap (state-dependent — DetHeadStep modifies σ)

- [x] `alloc v` → `(lit (loc ℓ), σ')` — implemented
- [x] `load (lit (loc ℓ))` → `(ofVal v, σ)` — implemented with sorry for `hlookup`
- [x] `store (lit (loc ℓ)) v` → `(lit unit, σ')` — implemented with sorry for `hlookup`/`hnew`

- [ ] **Discharge heap lookup proofs** (`hlookup`, `hnew`):
  Currently using `sorryAx`. Need a way to prove `σ.heap[ℓ]? = some v` and
  `e.toValB? = some v` in meta-code.
  Options:
  - Add `Decidable` instances for `ExtTreeMap` lookup equality and use `decide`.
  - Use `Lean.Elab.Tactic.evalNativeDecide` / `mkNativeDecideProof` if available.
  - Use `ofEqTrue (by native_decide)` pattern after adding `DecidableEq Val`.

## Infrastructure / larger tasks

- [ ] **Multi-step tests**: add `det_exec_of` tests that reduce all the way to a value
  (requires `binop` and `app` cases above).

- [ ] **Differential testing harness**: compare `det_exec_of`-synthesized final `cfg2`
  against `Eval.run` on the same input; assert they agree.

- [ ] **`DetExec` to `PureExec` bridge**: if all `DetStep`s in the chain are pure
  (same state), lift to `nsteps PureStep`.

- [ ] **Automation**: wrap `det_exec_of` in a tactic that picks fuel automatically
  (e.g. iterate until stuck or value reached).
