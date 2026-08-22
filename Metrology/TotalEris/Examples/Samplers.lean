module

public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Metrology.TotalEris.Examples.Samplers.Selector
public import Metrology.TotalEris.Examples.Samplers.Gauss
public import Metrology.TotalEris.Examples.Samplers.GaussianAdequacy

@[expose] public section

/-!
# Gaussian samplers

Aggregator for the `urand`-based Gauss sampler stack.

Dependency layering (bottom-up):

```
RealDecrTrial ── decreasing trial (urand init, real `<` compare, twp_urand_exp presample)
  ├── HalfBernNegExp (LeHalf, BNEHalf)  ── concrete base-½ Bernoulli
  ├── NegExp                            ── negative-exponential sampler
  └── Selector (C, Bii, S, S0, B)       ── integer-part selection
BernoulliGeometric (AbstractBernoulli, GeometricTrial)
  └── BernIter (AbstractBernoulliI, IterTrial, AbstractBernoulli.toAbstractBernoulliI)
Gauss (G1, G2)  ← BNEHalf, GeometricTrial, IterTrial, B
  └── GaussianAdequacy  ← DistributionAdequacy
```

Every WP spec here is complete and `sorry`-free, and fixed at `rT = ℝ`.

Laplace is not included: its value reconstruction and scaling need real-arithmetic
and real-power-of-two `BinOp.eval` extensions the language does not yet have.
-/
