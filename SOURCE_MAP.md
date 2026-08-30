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

# Process Core and Information Flow

This ledger is the complete disposition of the Process Core handoff. The package continues to use
functions `X : T → Ω → E`; it introduces no parallel process structure.

## Process laws, equivalence, and stationarity

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Klenke 9.6 process law | Upstream | `Measure.map`, `IdentDistrib`, and `Mathlib.Probability.Process.FiniteDimensionalLaws`; no local law structure. |
| Klenke 9.7(ii)-(iv) | Upstream | `HasIndepIncrements`, Mathlib Gaussian-process modules, and coordinatewise `Integrable`/`MemLp`; no wrapper predicates. |
| Klenke 9.7(v) stationary process | Implemented | `Probability/Process/Stationarity.lean`: `IsStationary` is equality of the full coordinate-product law under every shift, with coordinate and finite-coordinate consequences. |
| Klenke 9.7(vi) stationary increments | Inherited | `Probability/Process/StationaryIncrements.lean`, completed in the Ch01-08 milestone. |
| Klenke 21.1 modification / indistinguishability | Implemented | `Probability/Process/Equivalence.lean`: distinct quantifier orders, relation API, finite-coordinate law and coordinate-product law bridges. |
| Klenke 21.5(i) countable collapse | Implemented | `IsModification.indistinguishable_of_countable`, using Mathlib's `ae_all_iff`. |
| Klenke 21.5(ii) right-continuous collapse | Implemented | `IsModification.indistinguishable_of_rightContinuous`, using one countable dense sequence and right limits. |

## Paths, filtrations, and information flow

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Continuous/right/left path predicates | Implemented / inherited | `Path/Continuous.lean`, `Path/RightContinuous.lean`, and `Path/Cadlag.lean`; every a.s. property uses one common full-measure trajectory event. |
| Klenke 21.21 cadlag | Implemented | `IsCadlagPath` and `HasCadlagPaths`: right continuity plus an existential finite strict-left limit at every `t ≠ ⊥`; no totalized left-limit value. |
| Full Skorokhod topology | Deferred | Assigned to Functional Weak Convergence and Path-Space Limits; no topology is implied by the cadlag predicate. |
| Klenke 9.9-9.10 filtration/adaptedness | Upstream | `MeasureTheory.Filtration`, `Adapted`, and `StronglyAdapted`. |
| Klenke 9.11 natural filtration | Upstream / thin bridge | Mathlib `Filtration.natural` and `Filtration.stronglyAdapted_natural`; local `natural_le_of_stronglyAdapted` records exact minimality. |
| Klenke 9.12 / 25.5 predictable | Upstream | `Filtration.predictable`, `IsStronglyPredictable.isStronglyProgressive`, `.stronglyAdapted`, and `.iff_measurable_add_one`. |
| Klenke 21.22 right continuation | Upstream | `Filtration.rightCont`, `le_rightCont`, and `Filtration.IsRightContinuous`. |
| Klenke 21.22 usual conditions | Implemented | `Filtration.IsUsual`: right continuity plus containment of every ambient null set in the initial sigma-algebra. |
| Klenke 21.23 usual augmentation | Implemented | `Filtration/Augmentation.lean`: adjoin all null sets, move to `NullMeasurableSpace Ω P` with `P.completion`, then apply `rightCont`; `usualAugmentation_isUsual` proves both conditions. |
| Klenke 25.5(i) product measurable | Implemented | `IsProductMeasurable` is exactly measurability of `Function.uncurry X`, with coordinate/path/process bridges. |
| Klenke 25.5(ii) progressive | Upstream | Mathlib `IsProgressive` and `IsStronglyProgressive`. |
| Klenke 25.5(iii), Thm. 25.8 predictable chain | Upstream | Mathlib's predictable-to-progressive and predictable-to-adapted theorems; compile-time regression checks both and the discrete `n+1`/`n` characterization. |
| Klenke Remark 25.7 | Deferred external after audit | No approved theorem for adapted plus product-measurable implying a progressive modification was found. Klenke cites an external source; no unsupported converse is claimed. |
| Klenke Thm. 25.8 regular paths | Implemented bridge | `StronglyAdapted.isStronglyProgressive_of_rightContinuous` and `_of_leftContinuous`, proved by countable-range ceiling/floor grids. The right-continuous theorem also supplies global joint measurability. |
| Klenke Thm. 25.8 a.s. regular paths | Implemented | Under `Filtration.IsUsual`, the two `exists_isStronglyProgressive_modification_of_has...Paths` theorems replace the process by zero on the one common null event of bad trajectories. |

## Random times and stopping

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Klenke 9.15 stopping time | Upstream | Mathlib `IsStoppingTime` with codomain `WithTop T`; infinity is never represented by a finite sentinel. |
| Klenke 9.16 countable characterization | Upstream | `IsStoppingTime.measurableSet_eq` and `isStoppingTime_of_measurableSet_eq`. |
| Klenke 9.18 closure operations | Upstream | `IsStoppingTime.min`, `.max`, `.add_const`, and `.add` with their exact order/countability hypotheses. |
| Klenke 9.19 / 9.21 stopped information | Upstream | `IsStoppingTime.measurableSpace`, `measurableSpace_mono`, and related bound theorems. |
| Klenke 9.22-9.23 stopped value/process | Upstream / thin bridge | Mathlib `stoppedValue`, `stoppedProcess`, and `measurable_stoppedValue`; local `measurable_stoppedValue_of_rightContinuous` exposes the regular-path information-flow chain. |
| Hitting times | Upstream | `Mathlib.Probability.Process.HittingTime`: `hittingBtwn`, `hittingAfter`, and the adaptedness-to-stopping-time theorems with their required discrete/order assumptions. |
| Doob regularization | Deferred | Assigned to the later martingale/path-regularity package, as required by the handoff. |

## Process Core semantic regression gate

`Probability/Process/SemanticRegression.lean` formally checks the diagonal-spike modification that
is not indistinguishable, equality of its coordinate-product law with zero, the Boolean
Rademacher counterexample with equal one-time marginals but nonstationary pair law, natural
filtration minimality, predictable/progressive/adapted chains, a right-continuous filtration that
is not usual, an always-infinite stopping time on a probability-one event, and common-event cadlag
semantics. The right/left grid theorems, stopping-value bridge, and completed usual augmentation
provide the remaining positive acceptance chains.

# Discrete Martingale Calculus and Exchangeability

This is the complete disposition of the third handoff. All `BUILD` rows are kernel-checked; no
item is represented by a conclusion-shaped premise or a weakened surrogate statement.

## Part I: discrete martingale calculus

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Martingale/submartingale adapters | Implemented / upstream | `Martingale/Adapters.lean` retains Mathlib's canonical predicates and supplies only exact conversion bridges. |
| Discrete stochastic integral | Implemented | `Martingale/DiscreteIntegral.lean`: named transform, zero/successor/sum formulas, predictability interface, integrability, and martingale preservation. |
| Pathwise quadratic variation and predictable bracket | Implemented | `Martingale/QuadraticVariation.lean`: square increments, conditional bracket increments, square-minus-bracket martingale, and stopped-process compatibility. |
| Optional sampling | Implemented / upstream | Canonical bounded optional sampling is reused; `OptionalSampling/UniformIntegrable.lean` proves UI stopped values and the a.s.-finite conditional-expectation identity. |
| Doob inequalities | Implemented / upstream | Mathlib maximal inequality is reused; `Inequalities/DoobLp.lean` exposes the sharp `p/(p-1)` real-valued norm form with `1 < p`. |
| Martingale representation | Implemented with structural domain | `Representation/Binary.lean` proves representation from explicit binary splitting data; no unrestricted false representation theorem is claimed. |
| Reverse martingales | Implemented | `Martingale/Reverse.lean`: reverse conditional expectations and a.e./`L¹` convergence to the infimum sigma-field. |
| Klenke 11.14 | Implemented | `Convergence/QuadraticVariation.lean`: predictable cutoff localization proves a.s. convergence on the event of finite predictable quadratic variation. |

## Part II: exchangeability and de Finetti

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Exchangeability | Implemented | `Exchangeability/Basic.lean`: equality of every ordered finite-dimensional law at distinct indices, plus finite-permutation and reindexing bridges. |
| Finite symmetrization | Implemented | `Symmetrization.lean`: linear idempotent averaging projection and exact permutation invariance. |
| Exchangeable and tail sigma-fields | Implemented | `SigmaFields.lean`: decreasing prefix-invariant fields, their infimum, tail fields, and the raw inclusion `T ≤ E`. |
| Conditional expectation and means | Implemented | `ConditionalExpectation.lean` and `Means.lean`: symmetric conditional expectations, reverse-martingale sample means, a.e./`L¹` limits, prefix symmetrization, and exchangeable LLNs. |
| Empirical probability measure | Implemented | `EmpiricalMeasure.lean`: nonempty finite samples, multiplicities, integral/CDF bridges, and recovery of the unordered tuple from its empirical measure. |
| Symmetric-statistic factorization | Implemented | `IsPermutationInvariant.exists_factorThrough_empiricalProbabilityMeasure` gives the plain set-theoretic factorization; measurable factorization remains explicitly a separate Doob-Dynkin question. |
| Conditional iid / de Finetti | Implemented with approved dependency | `ConditionalIID.lean` exposes a structural product-mixture representation and equivalence; `Bernoulli.lean` gives the Boolean parameter specialization. |
| Invariant field equals tail modulo law | Implemented | `InvariantTail.lean`: finite-coordinate conditional expectations are moved beyond every cutoff and closed in `L¹`, yielding `exchangeableMeasurableSpace_eq_tail_modulo`. |
| Hewitt-Savage | Implemented | `hewittSavage_zero_one` combines the modulo-tail theorem with Mathlib's Kolmogorov zero-one law. |

## Third-milestone regression gate

`Martingale/SemanticRegression.lean` checks predictability indexing, transform recursion,
`WithTop` stopping, sharp Doob hypotheses, structural binary representation, and the finite-bracket
criterion. `Exchangeability/SemanticRegression.lean` checks exchangeable-but-dependent and
equal-marginal-but-nonexchangeable models, nonempty empirical measures, empirical factorization,
modulo-tail equality, Hewitt-Savage, and the Bernoulli de Finetti facade.
