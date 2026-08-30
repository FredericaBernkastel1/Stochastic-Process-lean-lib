# Source map

This ledger records the complete disposition of the normative Klenke Chapters 01-08 handoff.
Klenke is the mathematical coverage source; the book is not distributed in this repository.
`Implemented` means kernel-checked StochLean code, `Upstream` means pinned Mathlib v4.33.0 is the
canonical implementation, and `Deferred` is an explicit non-blocking destination authorized by the
handoff.

## Chapters 1, 2, and 4: compatibility coverage

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 1.1-1.23 | Upstream | Mathlib set, measurable-space, topology/Borel, generated-space, and product APIs. Real generators use `Mathlib.MeasureTheory.Constructions.BorelSpace.Real`; no chapter wrapper was needed. |
| 1.27-1.61 | Upstream | Mathlib measure construction, continuity, extensionality, Stieltjes/CDF, and product-measure APIs. `Measure.ext_of_generateFrom_of_cover` is the generator uniqueness anchor. |
| 1.65 | Upstream | Exact pinned declaration `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` in `MeasureTheory/Measure/MeasuredSets.lean`. |
| 1.68-1.106 | Upstream | Mathlib completion/restriction, measurability, `FactorsThrough`, `Measure.map`, `IdentDistrib`, CDF, density, and change-of-variables infrastructure. Random variables remain functions. |
| 2.3-2.39 | Upstream | Mathlib `Indep`, `iIndep`, `IndepFun`, `iIndepFun`, Borel-Cantelli, zero-one, convolution, and regrouping APIs. Exact downstream anchors include `iIndepSet.indep_generateFrom_of_disjoint`, `IndepFun.hasLaw_add`, and `IndepFun.map_add_eq_map_conv_map₀`. |
| 2.40-2.45, 2.47 | Application | Percolation is recorded as textbook coverage and is not part of the stochastic-process foundation. |
| 2.46 | Deferred external | Kesten's theorem is cited rather than proved by Klenke; it is not imported into the trust boundary. |
| Exercise 2.2.3 | Implemented | `Probability/Distributions/Multinomial.lean`: `PMF.multinomial`, categorical counts, and `iIndepFun.hasLaw_categoricalCounts`. |
| 4.1-4.26 | Upstream | Mathlib simple/Bochner/Lebesgue integration, monotone convergence, Fatou, `Lp`, density, and `MeasureTheory/Integral/Layercake.lean`. No Chapter 4 project module was created. |

## Chapter 3: generating functions and branching

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 3.1 | Implemented | `Probability/GeneratingFunction/Basic.lean`: law-first `PMF.pgf` on `unitInterval`, real mass API, and measure/law bridge. |
| 3.2 | Implemented | `Analytic.lean`: continuity, interior smoothness, analytic uniqueness, `factorialMoment`, exact arbitrary-order derivative series, and the extended-value left-boundary theorem `PMF.tendsto_factorialDerivativeSeries`. |
| 3.3 | Implemented / bridge | Law-level `PMF.pgf_convolution`; random-variable bridge `ProbabilityTheory.IndepFun.integral_pow_add_eq_pgf_mul`; upstream `IndepFun.hasLaw_add` remains the canonical sum-law theorem. |
| 3.5 | Upstream | Mathlib generalized binomial/power-series analysis; no probability-specific duplicate. |
| 3.6 | Implemented | `Probability/Convergence/Discrete.lean`: atomwise-to-PGF, PGF-to-atomwise, their equivalence, and the discrete Scheffé bridge `PMF.tendsto_setMassReal_of_tendsto_mass` for arbitrary sets. |
| 3.7 | Implemented | `Probability/LimitTheorems/PoissonApproximation.lean`: non-i.i.d. Bernoulli triangular arrays under square-smallness or maximum-smallness, reusing Mathlib `PoissonLimitThm` for the i.i.d. binomial case. |
| 3.8 | Implemented | `Probability/GeneratingFunction/RandomSum.lean`: generic convolution powers, law-level random sums, and PGF composition. |
| 3.9-3.11 | Implemented | `Probability/Branching/Basic.lean` and `Extinction.lean`: generation-law iteration, finite extinction laws, and the corrected least-fixed-point theorem. |

## Chapter 5: moments, LLN, and Poisson processes

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 5.1, 5.3-5.8 | Upstream / implemented gap | Mathlib moments and independence integration are reused. `Probability/Moments/RandomSum.lean` supplies the absent Wald identity `integrable_stoppedSum_and_integral_eq_mul`. |
| 5.10 | Implemented | `Probability/Moments/RandomSum.lean`: `memLp_stoppedSum_and_variance_eq`, the Blackwell-Girshick variance identity with its `L²` conclusion. |
| 5.11-5.20 | Upstream | Mathlib Markov/Chebyshev and `Probability/StrongLaw.lean`, including `strong_law_ae`; no parallel LLN predicate. The quantitative weak-law specialization is a direct variance/Chebyshev reuse. |
| 5.22-5.23 | Implemented | `Probability/EmpiricalProcess/{CDF,StrongLaw,GlivenkoCantelli}.lean`: finite-sample APIs, common-event threshold laws, and full arbitrary-CDF Glivenko-Cantelli, including jump laws. |
| 5.25-5.27 | Deferred | Entropy/source coding belongs to a future `InformationTheory` package. |
| 5.28 | Implemented after audit | `Probability/MaximalInequality/Kolmogorov.lean`: square-submartingale core and independent centered square-integrable specialization. |
| 5.29 | Implemented | `Probability/MaximalInequality/StrongLawRate.lean`: dyadic Borel-Cantelli proof and the exact Klenke logarithmic rate. |
| 5.30, 5.32 | Deferred external | Rademacher-Menshov and Baum-Katz are cited external results and have no hidden dependency. |
| 5.33 | Implemented | `Probability/Process/{Path/Monotone,Path/RightContinuous,StationaryIncrements}.lean` and `Process/Poisson/Basic.lean`; the corrected common-a.s. monotone/right-continuous path condition is part of `IsPoissonProcess`. |
| 5.34 | Implemented | `Process/Poisson/{IntervalAxioms,IntervalAxiomsConverse,IntervalAxiomsConverseLaw}.lean`: P1-P5 forward direction and the full dyadic Bernoulli/Poisson-binomial converse. |
| 5.35 | Implemented | `Probability/Distributions/{Multinomial,Poissonization}.lean` and `Process/Poisson/UniformPoint.lean`: generic categorical-count laws and Poisson mixing yield joint independent Poisson counts for every finite interval partition of `[0,1]`. |
| 5.36 | Implemented | `ForMathlib/MeasureTheory/{SimplexVolume,CumulativeSumVolume,WithDensityEquiv}.lean` and `Process/Poisson/{ExponentialArrivalLaw,ArrivalTimes,FiniteIncrementLaw}.lean`: arbitrary finite ordered partitions, boundary-nullity, exact product law, and `isPoissonProcess_arrivalCountProcess_of_iid_exp`. |
| Exercise 5.1.1 | Implemented | `Probability/Moments/PaleyZygmund.lean`, including multiplicative and quotient forms. |
| Exercise 5.2.1 | Deferred | Bernstein-Chernoff is a concentration extension, not a Ch01-08 blocker. |
| Exercise 5.5.1 | Application | Recorded as the later successive-unit-interval consumer; no extra foundation declaration is required. |

## Chapters 6 and 7: convergence and `Lp`

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 6.1, 6.8, 6.20-6.23, 6.26-6.28 | Upstream / bridge | Mathlib measurable-distance, `L1`/`Lp`, Egorov, dominated convergence, and parametric-integral APIs. The 6.28 domain correction is recorded; no erroneous wrapper was added. |
| 6.2 | Implemented | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean`: all finite restrictions and finite-measure compatibility. |
| 6.7, Ex. 6.2.1 | Implemented | `LocalConvergenceMetric.lean`: exhaustion pseudometric on raw maps and genuine metric on `AEEqFun`, both characterizing local convergence. |
| 6.12-6.15 | Implemented | `FastConvergenceLocal.lean`, `ConvergenceInMeasureLocal.lean`, and `CauchyInMeasureLocal.lean`: Borel-Cantelli, subsequence, every-subsequence, and complete-target Cauchy theorems. |
| 6.16-6.18 | Implemented | `UniformIntegrableEnvelope.lean`, `DeLaValleePoussin.lean`, and `UniformIntegrableEnvelopeCompatibility.lean`: literal envelope/tail forms, finite compatibility, algebra, finite-family, and domination closure. |
| 6.19 | Implemented | `DeLaValleePoussin.lean`: both sufficient direction and finite-measure converse `UniformIntegrable.exists_superlinearEnvelope`. |
| 6.24 | Implemented | `uniformIntegrableByTailEnvelope_iff_klenkeUniformIntegrableByDensity` and the uniform-absolute-continuity/tightness characterization. |
| 6.25 | Implemented | `Probability/Convergence/LocalVitali.lean`: exact sigma-finite Vitali equivalence for local convergence plus envelope UI. |
| 7.1-7.2, 7.4-7.46 | Upstream | Mathlib `Lp`, Holder/Minkowski/Jensen, Fischer-Riesz, Hilbert projection, Radon-Nikodym, Lebesgue decomposition, signed-measure, and variation APIs. The 7.25 sign erratum is avoided by canonical reuse. |
| 7.3 | Implemented bridge | `LpLocalConvergence.lean`: `tendstoLocallyInMeasure_and_poweredEnvelope_iff_tendsto_eLpNorm`. |
| 7.47, 7.49, 7.50 | Deferred after audit | No exact general `Lp` dual representation theorem was found in pinned Mathlib. Per the handoff, this moves to general functional-analysis/ForMathlib work and does not block the stochastic-process foundation. |

## Chapter 8 and semantic regression gate

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 8.2-8.22 | Upstream / thin guard | Mathlib conditional expectation, conditional Jensen/contraction, kernels, Bayes/total probability, and independence APIs. `Probability/Conditional/SemanticGuard.lean` adds positive-mass `ConditionableEvent` instead of exposing a zero-mass fallback. |
| 8.24-8.38 | Upstream / thin guard | Mathlib `Kernel`, `condDistrib`, `StandardBorelSpace`, and `condExp_ae_eq_integral_condDistrib`. `conditionalKernel_ae_eq_of_compProd_eq` records law-a.e. version uniqueness. |
| Exercises 8.2.5-8.2.6 | Upstream | Conditional Markov/Cauchy-Schwarz follow canonical conditional Jensen/`Lp` APIs; no duplicate theorem survived the audit. |

Mandatory regressions compile in `Probability/GeneratingFunction/SemanticRegression.lean`,
`Probability/Convergence/SemanticRegression.lean`, `Probability/Conditional/SemanticGuard.lean`,
`Probability/EmpiricalProcess/GlivenkoCantelli.lean`, `Process/Poisson/Basic.lean`,
`FiniteIncrementLaw.lean`, and `ArrivalTimes.lean`. In particular, the exponential-arrival
construction has the explicit four-increment application
`fourIncrementLaw_arrivalCountProcess_of_iid_exp`.
