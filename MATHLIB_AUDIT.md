# Pinned Mathlib audit

Baseline: Lean `v4.33.0`, Mathlib input revision `v4.33.0`, resolved commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Searches were run against the pinned checkout before adding public declarations. This file records
the relevant duplicate decisions.

| Topic / search terms | Pinned Mathlib result | Decision |
| --- | --- | --- |
| `pgf`, `probability generating function` | No canonical PGF for `PMF ℕ` | Add `PMF.pgf` and law bridge in StochLean |
| `poissonMeasure`, `PoissonLimitThm` | Canonical Poisson measure and i.i.d. binomial point-probability limit exist | Re-export the upstream result; add only the non-i.i.d. Bernoulli triangular-array theorem and its PGF bridge |
| finite independent Bernoulli sum law, `poissonBinomial` | `PMF.poissonBinomial` exists, but no theorem connects a generic finite independent Bernoulli family to that law | Add a PGF/independent-integration bridge in `PoissonApproximation.lean`; use it in the dyadic converse |
| probability multinomial distribution / Poisson splitting | Only the combinatorial `Nat.multinomial` and finite product-measure primitives exist; no probability multinomial law or Poisson-mixing theorem was found | Build the generic finite categorical-count law before completing Klenke 5.35; do not hide it in the Poisson-process namespace |
| `PMF.bind`, `PMF.map` | Canonical law-level mixture and mapping operations exist | Define convolution and random sums using these operations |
| `HasIndepIncrements` | Canonical process predicate exists | Reuse it inside `IsPoissonProcess` |
| `TendstoInMeasure` | Only the global measure notion is canonical | Add the finite-restriction local predicate in `ForMathlib` |
| local convergence exhaustion metric, `spanningSets` | No metric or pseudometric inducing sigma-finite local convergence in measure found | Add Klenke's normalized geometric exhaustion pseudometric on raw strongly measurable maps and a genuine metric on `AEEqFun` |
| local fast convergence, local Cauchy criterion | No sigma-finite local Borel--Cantelli convergence or Cauchy-completeness package found | Add summable-bad-set and fast-Cauchy theorems, then prove the complete-target local Cauchy equivalence |
| `UnifIntegrable`, `tendsto_Lp_finite_of_tendstoInMeasure` | Canonical finite-measure Vitali theorem exists | Reuse it on every finite restriction |
| `UnifTight`, `tendstoInMeasure_iff_tendsto_Lp` | Canonical non-finite-measure Vitali theorem exists, but it uses global convergence in measure | Reuse its uniform-absolute-continuity/tightness components and add the missing local-to-global `Lᵖ` bridge required by Klenke |
| de la Vallée-Poussin envelope criterion | No superlinear-envelope bridge to Mathlib UI predicates found | Add the generic sufficient direction in `ForMathlib`; leave the converse envelope construction explicit |
| `empiricalCDF`, `GlivenkoCantelli` | No matching empirical-CDF or GC declaration found | Add strict/non-strict finite-sample APIs; derive common-event threshold strong laws from Mathlib `strong_law_ae`; use right values and strict left limits to prove full uniform GC for arbitrary real laws |
| `GaltonWatson`, `branching`, `extinctionProbability` | No matching law recursion or extinction fixed-point API found | Add StochLean law-level definitions and proofs |
| `PoissonProcess`, interval-count characterization | Poisson distributions and independent increments exist, but no matching counting-process or P1–P5 characterization package | Add a function-based predicate, exact interval-axiom API, proved forward characterization, converse mean-linearity and P5-limit foundations, and deterministic construction cores |

## Public-domain checks

- `PMF.pgf` takes a `unitInterval`; no divergent outside-domain value is part of the API.
- `PMF.ext_pgf` uses analyticity and the identity principle, not coefficient extraction from an
  unproved boundary derivative.
- `TendstoLocallyInMeasure` requires measurability and finiteness for every restriction set.
- `DivergentArrivalSequence.count` is constructed from a divergence witness.
- No theorem relies on a conclusion-shaped hypothesis.
