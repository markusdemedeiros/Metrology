# TotalEris Wishlist

Long-running port target: total Eris from `clutch/theories/eris/` (Rocq) to
Lean 4 under `Metrology/TotalEris/`. Goal: the chosen total-WP **examples**
look similar to the Rocq versions but use Lean/Iris-Lean proofmode tactics and
locally-nameless syntax.

Authoritative agreements from the kickoff:

| Question | Answer |
|---|---|
| Partial scope | Port anything *below* the Eris WP (glm, `pgl_wp`, `erisWpGS`); skip partial primitive_laws / proofmode unless total stack reuses them. |
| Adequacy | Full total adequacy (port `total_adequacy.v`). |
| Target examples | `geometric_total` (tutorial) + `random_walk` (examples). |
| Layout | Everything under `Metrology/TotalEris/`. |

## Success criteria

1. `lake build Metrology.TotalEris` is green; no `sorry` along the dependency
   chain from each example back through the total adequacy theorem.
2. `Metrology/TotalEris/Examples/GeometricTotal.lean` proves the canonical
   geometric-termination spec using `wp_*` / `twp_*` tactics. The text/structure
   is recognizably the same as `geometric_total.v` modulo Lean syntax and the
   locally-nameless representation.
3. `Metrology/TotalEris/Examples/RandomWalk.lean` likewise, using the RSM
   presampling rule.
4. Tactics (`wp_pures`, `wp_apply`, `wp_bind`, `wp_lam`, `wp_pure`,
   `wp_alloctape`, and `iLöb`) work on `tgl_wp` goals — the examples should not
   need to bypass them.

## Current porting status (2026-05-25 — significant infrastructure complete)

Files in `Metrology/TotalEris/` — **all build green, zero sorries**:

| File | Status | Notes |
|---|---|---|
| `Glm.lean` | ✅ | 2 of 3 disjuncts (state_step deferred); `Pgl`, `ErisWpGS` class, `execStutter`, `glm`, `glmPre_mono`, `glm_unfold`, `glm_mono_pred`, `glm_prim_step`, `glm_credit_bump`. |
| `Weakestpre.lean` | ✅ | `pglWpPre`, `pglWp`, `Contractive` instance, unfold + value rules. (Strong_mono, bind, fupd deferred.) |
| `TotalWeakestpre.lean` | ✅ | `tglWp` via `bi_least_fixpoint` over `(CoPset × Exp)` (Φ outer). Unfold + value rules + simple induction principle (`tglWp_ind_simple`, fixed `E`/`Φ`). Marked `@[reducible]` so `iexact`/`iapply` see through `tglWp = bi_least_fixpoint ...` defeq. Per-branch unfolds: `tglWp_unfold_value`, `tglWp_unfold_step`, `tglWpPre_eq_value`, `tglWpPre_eq_step`. Derived: `tglWp_mono`, `tglWp_strong_mono` (fixed-mask, **spatial** fupd wand via `glm_strong_mono` + Q-as-pre trick), `tglWp_wand`/`_l`, `tglWp_fupd`, `fupd_tglWp`, `tglWp_frame_l`/`_r` (spatial), `tglWp_bind`, `tglWp_bind_value`, `tglWp_value_inv_with_state` (extract value-WP post under state). (Mass-changing `tglWp_strong_mono` still deferred.) |
| `Glm.lean` | ✅ | `Pgl`, `ErisWpGS` class, `execStutter`, `glm` (OT + prim_step disjuncts), `glm_unfold`, `glm_strong_mono` (spatial wand via `least_fixpoint_iter` + Q-as-pre), `glm_mono_pred` (intuitionistic), `glm_mono_grading` (ε ≤ ε' weakening, single-step), `glm_prim_step`, `glm_credit_bump`, `glm_bind` (Ectx-bind, derived via `partialInv K.fill` + `primStep_fill` pushforward, no `Hv` precondition required). |
| `TotalLifting.lean` | ✅ | All 8 lifting lemmas proved: `twp_lift_step_fupd_glm`, `twp_lift_step_fupd`, `twp_lift_atomic_step_fupd`, `twp_lift_pure_step`, `twp_lift_pure_det_step`, `twp_lift_atomic_head_step`, `twp_lift_pure_det_head_step`, `twp_lift_pure_det_step_of_pureStep`. **Plus `twp_pure_step_fupd`** (PureExec integration). |
| `ErisGS.lean` | ✅ | `ErisGS` class bundling `AppGS` + `ECGS` + `InvGS_gen`; auto `ErisWpGS` instance. |
| `TotalPrimitiveLaws.lean` | ✅ | `twp_alloc`, `twp_load`, `twp_store`, `twp_alloctape`, `twp_rand`, `twp_rand_tape`, `twp_rand_tape_empty`. |
| `ErrorRules.lean` | ✅ | All ec_* re-exports, `ec_induction`, `ec_ind_simpl_external`, `twp_err_pos`, `twp_err_incr`, `twp_rand_exp`, **`twp_rand_exp_nat`** — all proved, no `sorry`. |
| `Examples/RandomWalk.lean` | 🟥 | Programs `unifRw1dRec`/`unifRw1d` + the `final_pos` combinatorics defined; spec `unif_rw_1d_terminate` is **`sorry`**. Blocked on two issues. **(1) Off-by-one degeneracy:** Lean `rand 1` samples `Ico 0 1 = {0}` (deterministic), so the literal-`#1` port always steps down — a degenerate deterministic descent, *not* the symmetric walk. A faithful walk needs `rand 2`/`alloc 2`. **(2) RSM:** the faithful version then needs `twp_presample_rsm`, which sits on the unported `seq_amplification.v` + `twp_presample_amplify_rsm{,_aux}` + `ec_ind_incr` (the "1000-line chase" — deliberately deferred). State-step `glm` disjunct and `twp_presample`/`twp_presample_adv_comp` are done; the blocker is purely the RSM stack. |
| `Examples/GeometricTotal.lean` | ✅ | **Fully proved & building green** (zero `sorry`). NB: the whole `Examples/` dir was in *no build target* (the root `Metrology.lean` never imported `Metrology.TotalEris`), so it had silently bit-rotted; getting it green again required: pinning the section `GF` to universe `0` (`BundledGFunctors.{0,0,0}` — adequacy is concrete-model/universe-0), passing `(GF := GF)` to `twp_tgl`, and `iapply hwp` (not `iexact`) for the Lean-term entailment. Both theorems — `geo_nonneg` (the unconditional spec) and `geo_nonneg_pos_err` (with positive credit) — are fully mechanized. The proof mirrors `clutch/theories/eris/tutorial/geometric_total.v` structurally: error induction (`ec_ind_simpl_external` with `k = 3/2`), β-reduction via explicit `twp_pure_step_fupd` (or the `twp_pure_at` macro), `twp_bind` for the cond/rand context, `twp_rand_exp` with the error fn `F(n) = if n=0 then 0 else (3/2)*ε`, `interval_cases` on the sampled value, and recursive use of the IH via `tglWp_wand` + `ec_eq`. The example builds green; once `twp_rand_exp_nat` is filled in, the chain becomes unconditional. |
| `Proofmode.lean` | ✅ | Macros `twp_value`, `twp_pure`, `twp_pures`, `twp_lam`, `twp_apply` + `wp_*` aliases. `twp_pure` uses `twp_pure_step_fupd`. |

**Smoke tests**: `Examples/Basic.lean` now exercises `twp_rand_exp_nat` (z=1, ε₂≡0) and `twp_rand_exp` (z=2, geometric-style F) as regressions for the just-proved expectation-preserving sample rule.

**Build wiring (2026-05-27)**: the entire `TotalEris` tree was orphaned from the default build — the root `Metrology.lean` never imported `Metrology.TotalEris`, and nothing imported the `Examples/`. They bit-rotted undetected (`GeometricTotal`/`Basic` did not compile; `RandomWalk` had parse errors + broken combinatorial proofs). Fixed: `Metrology.lean` now imports `Metrology.TotalEris` and the new aggregator `Metrology/TotalEris/Examples.lean` (which can't live in `TotalEris.lean` itself — the examples import it, so that would cycle). The whole stack + examples are now in `@[default_target] lean_lib Metrology`, so `lake build` keeps them honest. Only remaining `sorry`: `unif_rw_1d_terminate`.

Still to write (in priority order, as of 2026-05-26):

✅ `twp_err_pos` (proved) — derives from `twp_err_incr` + `ec_zero` via the `iapply fupd_tglWp ; ihave HzBupd : iprop(|==> ↯0) ; · iapply ec_zero ; imod HzBupd with Herr ; imodintro` lift.

✅ `twp_err_incr` (proved) — ~50 lines, the long port from `error_rules.v:881`. Key tricks: (a) `errInterp_supply_increase` wrapper to bypass the ECGS typeclass diamond; (b) keep the leading `|={∅}=>` so `elimModal_bupd_fupd` fires; (c) the `tglWp_bind`-style `ihave ... $$ [...] ; · rw [← tglWpPre_eq_step Hnv] ; iexact ...` pattern to expose the glm form; (d) `conv_rhs => rw [← heqEps]` to avoid looping on `← add_tsub_cancel_of_le`.

✅ `geo_nonneg`, `geo_nonneg_pos_err` (proved modulo `twp_rand_exp_nat` stub).

✅ **`twp_rand_exp`** (FULLY PROVED) — wrapper around `twp_rand_exp_nat`. Applies the base lemma with clamped `F n := min (ε₂ n) 1`. The HSum side condition is a calc chain: tsum mono via clamp + `ENNReal.tsum_le_tsum`, tsum-to-finset collapse via `tsum_eq_sum`, range-subset monotonicity via `Finset.sum_le_sum_of_subset`, sum-div via `Finset.induction_on` + `ENNReal.add_div`, mass cancellation via `ENNReal.mul_div_cancel_right` + `ENNReal.natCast_ne_top`. The continuation handles `↯(min ε₂n 1) → ↯(ε₂ n)` by case-split: if `ε₂ n ≤ 1` use `ec_eq`; else use `ec_contradict` with the unreachable-credit hypothesis.

✅ **`twp_rand_exp_nat`** — FULLY PROVED (zero sorries). **All 5 sub-goals closed**:
- ✅ **Reducibility** (`Reducible (rand z) σ₁`): closed.
- ✅ **`X₂ ≤ ε_now - ε₁ + 1`**: closed using gcongr + case split.
- ✅ **Integral bound** `∫⁻ ρ, X₂ ρ ∂primStep ≤ ε_now`: CLOSED. After the off-by-one fix (HSum now divides by `z.toNat` to match Lean's `Cfg.uniform z σ` over `Finset.Ico 0 z`), the bound was discharged via `primStep_eq_headStep` → `Cfg.uniform` unfold → `lintegral_map` → PMF computation + Int→Nat reindexing.
- ✅ **`Pgl 0 R`**: closed via `Pgl.mono_pred` + `Pgl.zero_positive` + `primStep_eq_headStep` + `headStep_support_iff`.
- ✅ **Per-outcome continuation**: CLOSED. Pattern: subst the outcome, `dif_pos` to reduce X₂, `errInterp_supply_decrease` to drop supply by ε₁, case-split on whether new supply + ε₂ n < 1, `execStutter_spend` in the bad case, `errInterp_supply_increase` + `tglWp_value_of_toVal (rfl)` + feed `Hcont` in the good case.

**Off-by-one note**: Lean's `Cfg.uniform z σ` samples from `Finset.Ico 0 z` (z values), while the original Rocq `rand z` samples `fin (S z)` (z+1 values). The HSum side condition (and the `twp_rand_exp` wrapper) have been adjusted to use `z.toNat` divisor to match Lean semantics. This changed the Geometric example's HSum proof obligation from `≤ 3*ε` to `≤ 2*ε` (which still holds for the geometric `F`).

✅ State-step disjunct of `glm` — **done**. `getActive`, `tapePresample` in `ProbLang/Erasure.lean`; `Tgl.tgl_lift_prob`, `Tgl.tgl_state_step`, `Tgl.dbind_state_step` proved in `TotalAdequacy.lean`; the state-step disjunct is in `glmPre` and cascades through `glmPre_mono`, `glm_strong_mono`, `glm_mono_grading`, `glm_mono_pred`, `glm_bind`, `glm_implies_tgl`.

✅ `PresampleRules.lean` — **done, zero sorries**. `twp_presample` (slack-free presample) and `twp_presample_adv_comp` (per-outcome error spending) both fully proved. The adv-comp integral side condition reduces to `HSum` via `tapePresample_lintegral` → `hPointwise` → `tapeIndexUniform_lintegral_eq_cfg_uniform` (reusing the proven `Cfg.uniform` computation) → `Finset.sum_image`/`sum_attach` matching.

🟥 `twp_presample_rsm` + the `random_walk` spec — **deferred** (the "1000-line chase" the *Things to actively avoid* section warns against). Two blockers: **(a) off-by-one** — Lean `rand z` samples `Ico 0 z` (`z` values), so the literal `rand #1` port is deterministic and degenerate; a faithful symmetric walk needs `rand 2`/`alloc 2`. **(b)** the rule sits on the unported `seq_amplification.v` (`εAmp`/`kwf`/`lt_1_k`), the `twp_presample_amplify_rsm{,_aux}` chain, and the `ec_ind_incr` error-induction principle. See `Examples/RandomWalk.lean`'s module docstring for the full analysis.

✅ `TotalAdequacy.lean` — **`twp_tgl` FULLY PROVED**. Substantive case closes via `twp_step_fupd_tgl` (~70 lines, ind on `tglWp` via `tglWp_ind_simple` + per-`e'` value/non-value case split + `glm_implies_tgl` for the non-value glm extraction) + `fupd_soundness_no_lc` for the pure-Prop extraction. `[AppPreGS GF] [ECPreGS GF] [InvGpreS GF]` preconditions are now threaded through all five user-facing adequacy theorems (`twp_tgl`, `twp_mass_lim_exec`, `twp_pgl_lim`, `twp_tgl_limit`, `twp_mass_lim_exec_limit`, `twp_pgl_lim_limit`), plus `Examples/GeometricTotal.lean`'s `geo_tgl` and `geo_mass_one`. The Hwp signatures now fix `hlc=false` to match the soundness extraction path. Original cascade-failure on `twp_tgl_limit`/`twp_pgl_lim` is resolved by updating all dependents consistently.

✅ `FupdPlainlyForall.lean` — `iProp_fupd_plainly_forall_2_no_lc` and the `..._pure_impl_no_lc` corollary, both proved at the `IProp GF` model level via the `ihave #>` plain-context-duplication trick (iris-Lean's abstract `BIFUpdatePlainly` typeclass ships only the weaker `fupd_plainly_sForall_2`; the strong forall form needed for adequacy is not derivable at the BI level but holds concretely on the `IProp GF` model).

## Module layout (under `Metrology/TotalEris/`)

Following the Approxis template (`Metrology/Approxis/*` already exists and is
the closest analog — copy its style for `WpGS` class, ghost state setup,
`bi_least_fixpoint`-based modalities, and the proofmode tactic macros).

Bottom-up dependency order (also the porting order):

```
                            ┌── Glm.lean              ← glm modality (least fp)
Metrology/TotalEris/        ├── Weakestpre.lean       ← erisWpGS class + pgl_wp def + core lemmas
                            ├── Lifting.lean          ← wp_lift_* glue
                            ├── EctxLifting.lean
                            ├── PrimitiveLaws.lean    ← state_interp setup + wp_alloc/load/store/rand
                            ├── DerivedLaws.lean      ← array laws (only if examples need)
                            ├── TotalWeakestpre.lean  ← tgl_wp def + ind + unfold + monotonicity
                            ├── TotalLifting.lean
                            ├── TotalEctxLifting.lean
                            ├── TotalPrimitiveLaws.lean
                            ├── TotalDerivedLaws.lean (only if needed)
                            ├── ErrorRules.lean       ← selective port (see below)
                            ├── PresampleRules.lean   ← selective port (see below)
                            ├── Proofmode.lean        ← wp_pures / wp_apply / wp_bind / wp_lam / wp_alloctape macros
                            ├── Adequacy.lean        (optional — only if total_adequacy reuses)
                            ├── TotalAdequacy.lean    ← twp_tgl, twp_mass_lim_exec, twp_pgl_lim_limit
                            └── Examples/
                                ├── GeometricTotal.lean
                                └── RandomWalk.lean
```

Top-level index `Metrology/TotalEris.lean` re-exports the public surface.

## Selective porting in the heavy files

`error_rules.v` (1727 lines) and `presample_rules.v` (2322 lines) are too big
to port wholesale. Port only what the chosen examples actually use, plus any
prerequisites that come up.

| File | Must-port lemmas | Reason |
|---|---|---|
| `error_rules.v` | `twp_err_pos`, `twp_rand_exp_nat`, `twp_rand_exp_fin`, `ec_aux`, `ec_split`/`ec_combine`/`ec_eq`/`ec_induction`/`ec_contradict` | geometric_total + ec utility |
| `presample_rules.v` | `twp_presample_rsm` and its supporting RSM machinery | random_walk |
| `seq_amplification.v` | only if `twp_rand_exp_*` proofs need it | check during porting |

If a tempting auxiliary lemma turns out to be a dead end or pulls in another
1000-line chase, leave the dependency as `sorry` and move on. **Do not port
partial-WP `wp_apply` chains in `proofmode.v`** unless the total proofmode
literally needs them.

## Tactics (`Proofmode.lean`)

Build proofmode-style macros directly on top of the lifting lemmas
(`twp_lift_pure_step`, `tgl_wp_bind`, `tgl_wp_value`, etc.). Use Approxis's
`RelTactics.lean` as the structural template:

- `wp_pure` / `wp_pures` — single/repeat pure reductions
- `wp_lam` / `wp_rec` — beta-step on lambdas/recursive functions
- `wp_bind` — focus a redex
- `wp_apply <term>` — `wp_bind` + `iapply`
- `wp_alloc` / `wp_load` / `wp_store` / `wp_rand` / `wp_alloctape` — heap/tape
- These should be generic over `wp` vs `twp` if practical. If not, prefix
  total versions with `twp_*`; either is acceptable as long as the example text
  stays readable.

## Locally-nameless caveat

`Metrology/ProbLang/Syntax/Syntax.lean` uses `fvar`/`bvar` and `Exp`. When
porting code that pattern-matches or unfolds programs, write Lean expressions
in the existing notation (see `Metrology/ProbLang/Test/Notation.lean`). Where
the Rocq proof uses `wp_lam`/`wp_rec`, the Lean tactic should produce the
corresponding substitution under locally-nameless conventions — likely via the
already-existing `open_*`/`subst_*` lemmas in `Syntax/LocallyClosed.lean`.

## Stretch goals (only after the above is green)

- Port `basic_eris.v` tutorial (mostly partial-WP; would force more partial
  primitive laws — skip unless time permits).
- Port `rec_toss.v` / `spline.v` examples.
- Tighten any `sorry`s left in `presample_rules` / `error_rules` ports.

## Things to actively avoid

- Wholesale porting of `error_rules.v` and `presample_rules.v`.
- Porting partial-WP `derived_laws` / `proofmode` if the total stack does not
  reuse them.
- Adding new abstractions or "improvements" over the Rocq structure — the goal
  is a faithful port that survives future maintenance, not a redesign.
- Per `CLAUDE.md`: never delete commented-out Rocq blocks; keep the file
  compiling after each edit; ask for help if stuck instead of spinning.
