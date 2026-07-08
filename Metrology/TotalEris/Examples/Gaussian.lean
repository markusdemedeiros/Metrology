module

public import Metrology.TotalEris.Examples.Gaussian.RealDecrTrial
public import Metrology.TotalEris.Examples.Gaussian.HalfBernNegExp
public import Metrology.TotalEris.Examples.Gaussian.BernGeo
public import Metrology.TotalEris.Examples.Gaussian.BernIter
public import Metrology.TotalEris.Examples.Gaussian.NegExp
public import Metrology.TotalEris.Examples.Gaussian.Selector
public import Metrology.TotalEris.Examples.Gaussian.Gauss
public import Metrology.TotalEris.Examples.Gaussian.Laplace

@[expose] public section

/-!
# Gaussian / Laplace samplers — scaffolding (continuous-uniform port)

Aggregator for the `urand`-based port of the Gauss/Laplace sampler stack from
`clutch/theories/eris/examples/{gauss,laplace}.v` (branch `elementary-infinite`).

Dependency layering (bottom-up):

```
RealDecrTrial ── decreasing trial (init→urand, cmp→real <, presample→twp_urand_exp)
  ├── HalfBernNegExp (LeHalf, BNEHalf)        ── concrete base-½ Bernoulli
  └── NegExp                                   ── Laplace magnitude sampler
BernGeo (GeoTrial) / BernIter (IterTrial)      ── generic combinators over AbstractBernoulli
Selector (C, Bii, S, S0, B)                    ── integer-part selection
Gauss   (G1, G2)   ← BNEHalf, GeoTrial, IterTrial, B
Laplace (Laplace0, Laplace) ← NegExp
```

**Status: stub.** Every file contains programs + specifications only; all
proofs are `sorry`. Fixed at `rT = ℝ`.

Two language extensions are deferred to the proof phase (flagged in-file):
* real comparison `<`/`≤` in `BinOp.eval` (needed by every sampler), and
* a real power-of-two op for `Laplace`'s `R_mulPow`.

Deliberately **not** imported by `Examples.lean`, so these stubs stay out of
the default build target until the proofs land.
-/
