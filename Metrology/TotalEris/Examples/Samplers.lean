module

public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Metrology.TotalEris.Examples.Samplers.Selector
public import Metrology.TotalEris.Examples.Samplers.Gauss
public import Metrology.TotalEris.Examples.Samplers.GaussianAdequacy
public import Metrology.TotalEris.Examples.Samplers.GaussianConcentration
public import Metrology.TotalEris.Examples.Samplers.Gaussian

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
  └── Gaussian (Gauss)                       ── real assembly + sign flip ⇒ N(0,1)
        └── GaussianAdequacy  ← DistributionAdequacy
              └── GaussianConcentration          ── Chebyshev/Chernoff/Mills tails
```

Every WP spec here is complete and `sorry`-free, and fixed at `rT = ℝ`.

`G2` samples the half-normal as a pair `(x, k)`; `Gauss` assembles the real
`x + k` in the object language (via the `toReal` coercion and real addition),
flips a fair coin, and negates on heads, giving a sampler whose limiting
execution is distributed exactly as `gaussianReal 0 1`.

Laplace is still not included: its value reconstruction needs real scaling by
powers of two, which `BinOp.eval` does not yet have (real `+`, unary `-` and the
`toReal` coercion do exist).
-/
