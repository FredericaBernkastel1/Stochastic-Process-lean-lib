# Pinned Mathlib audit

Baseline: Lean `v4.33.0`, Mathlib input revision `v4.33.0`, resolved commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Searches were run against the pinned checkout before adding public declarations. This file records
the relevant duplicate decisions.

| Topic / search terms | Pinned Mathlib result | Decision |
| --- | --- | --- |
| `pgf`, `probability generating function` | No canonical PGF for `PMF ℕ` | Add `PMF.pgf` and law bridge in StochLean |
| `poissonMeasure`, `PoissonLimitThm` | Canonical Poisson measure and binomial point-probability limit exist | Re-export the upstream limit theorem; do not duplicate it |
| `PMF.bind`, `PMF.map` | Canonical law-level mixture and mapping operations exist | Define convolution and random sums using these operations |
| `HasIndepIncrements` | Canonical process predicate exists | Reuse it inside `IsPoissonProcess` |
| `TendstoInMeasure` | Only the global measure notion is canonical | Add the finite-restriction local predicate in `ForMathlib` |
| `UnifIntegrable`, `tendsto_Lp_finite_of_tendstoInMeasure` | Canonical finite-measure Vitali theorem exists | Define only the local restriction bridge |
| `UnifTight`, `tendstoInMeasure_iff_tendsto_Lp` | Canonical non-finite-measure Vitali theorem exists | Reuse upstream for global convergence; avoid a duplicate theorem |
| `empiricalCDF`, `GlivenkoCantelli` | No matching empirical-CDF or GC declaration found | Add finite-sample API; GC proof remains scheduled |
| `GaltonWatson`, `branching`, `extinctionProbability` | No matching law recursion or extinction fixed-point API found | Add StochLean law-level definitions and proofs |
| `PoissonProcess` | Poisson distributions and independent increments exist, but no matching counting-process package | Add a function-based predicate and deterministic construction cores |

## Public-domain checks

- `PMF.pgf` takes a `unitInterval`; no divergent outside-domain value is part of the API.
- `PMF.ext_pgf` uses analyticity and the identity principle, not coefficient extraction from an
  unproved boundary derivative.
- `TendstoLocallyInMeasure` requires measurability and finiteness for every restriction set.
- `DivergentArrivalSequence.count` is constructed from a divergence witness.
- No theorem relies on a conclusion-shaped hypothesis.
