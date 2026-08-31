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

# Measure Convergence and Projective Construction

This is the complete disposition of the fourth handoff. Weak convergence is Mathlib's ordinary
topology on `ProbabilityMeasure`; no local synonym such as `Weak` or `WeaklyConverges` is defined.
Likewise, projective families and limits use only Mathlib's `IsProjectiveMeasureFamily` and
`IsProjectiveLimit` vocabulary.

## Part I: convergence of probability and locally finite measures

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Weak convergence | Upstream | Ordinary `Tendsto` in `ProbabilityMeasure`, characterized by `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. |
| Portmanteau | Upstream | Reuse open/closed liminf/limsup criteria and `tendsto_measure_of_null_frontier_of_tendsto`; no local duplicate. |
| Tightness and Prokhorov | Upstream | Reuse `IsTightMeasureSet`, `isCompact_closure_of_isTightMeasureSet`, and `isTightMeasureSet_of_isCompact_closure`. |
| Convergence in distribution | Upstream | Reuse `TendstoInDistribution`, `TendstoInMeasure.tendstoInDistribution`, continuous mapping, and Slutsky theorems. |
| A.e.-continuous mapping | Implemented gap | `Probability/MeasureConvergence/Mapping.lean`: Portmanteau bridge `ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous`. |
| Vague convergence | Implemented distinct gap | `ForMathlib/MeasureTheory/Measure/VagueConvergence.lean`: locally finite `TendstoVaguely`, weak-to-vague, compact-space equivalence, and escaping-Dirac convergence. |
| Weak/vague boundary | Implemented regression | `escapingDirac_tendstoVaguely_zero`, `escapingDirac_not_isTightMeasureSet`, and `escapingDirac_not_tendsto_probabilityMeasure` formally exhibit loss of mass at infinity. |
| CDF convergence criterion | Upstream / implemented consumer | Mathlib's rational `Ioo` convergence-determining pi-system is consumed by `tendsto_empiricalProbabilityMeasurePM_ae`. |
| Empirical weak convergence | Implemented | `Probability/MeasureConvergence/Empirical.lean` bundles the milestone-three empirical measure and proves almost-sure weak convergence to the common law from the strict and non-strict empirical CDF laws. |
| Levy continuity and characteristic functions | Upstream | Reuse `MeasureTheory/Measure/LevyConvergence.lean`; no parallel characteristic-function convergence theorem. |
| Functional/path-space weak convergence | Deferred | Assigned to the later Skorokhod/path-space package; the present milestone makes no topology on path predicates. |

## Part II: products, kernels, and projective extension

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Product coordinates and cylinders | Upstream | `measurable_pi_apply`, `measurableCylinders`, `cylinder`, and `generateFrom_measurableCylinders`. |
| Arbitrary probability products | Upstream | `Measure.infinitePi`, `isProjectiveMeasureFamily_pi`, `isProjectiveLimit_infinitePi`, `infinitePi_map_restrict`, and `infinitePi_cylinder`. |
| Kernels and Ionescu--Tulcea | Upstream | Reuse `Kernel.traj`, `Kernel.trajMeasure`, their Markov/probability instances, finite-trajectory recovery, and conditional-distribution theorem. |
| Projective vocabulary | Upstream | Only `IsProjectiveMeasureFamily` and `IsProjectiveLimit`; the regression pins the direction `P J = (P I).map (Finset.restrict₂ hJI)`. |
| Arbitrary-index standard-Borel extension | Implemented facade over approved external | `MeasureTheory/Constructions/KolmogorovExtension.lean`: `projectiveLimitOfStandardBorel`, finite/probability instances, finite-dimensional recovery, uniqueness, and `∃!` theorem. |
| Public domain | Implemented | The facade requires only measurable spaces plus `StandardBorelSpace`; temporary Polish topologies from `upgradeStandardBorel` remain proof-local and no topology occurs in public types. |
| Empty index type | Implemented and tested | Probability preservation and unique existence compile for `ι = Empty`; no `Nonempty ι` assumption is introduced. |
| Canonical process | Reused representation | The process is exactly `fun i ω ↦ ω i` on the product space; no process structure or path topology is added. |
| Probability vs finite mass | Implemented regression | `twoMassFiniteFamily` and `twoMassLimit` form a finite projective system of mass two and formally fail `IsProbabilityMeasure`. |
| Downstream de Finetti | Regression reuse | The already completed `IsExchangeable.hasDeFinettiRepresentation` remains part of the full build and axiom audit after the new projective dependency is added. |

## Mandatory semantic regressions

| # | Acceptance case | Formal resolution |
| ---: | --- | --- |
| 1 | `δ_n` tends vaguely to zero but has no probability weak limit | `escapingDirac_tendstoVaguely_zero`; non-tightness and no weak probability limit are separate theorems. |
| 2 | `δ_(1/(n+1)) ⇒ δ_0`, while mass of `{0}` does not converge | `shrinkingDirac_tendsto_dirac_zero` and `shrinkingDirac_singleton_mass_not_tendsto`. |
| 3 | Measurable discontinuous mapping can destroy weak convergence | `zeroDetector_not_continuousAt_zero` and `zeroDetector_mapped_shrinkingDirac_not_tendsto`. |
| 4 | Convergence in probability implies convergence in distribution, not conversely | Canonical implication compiles; `boolFlip_tendstoInDistribution` plus `boolFlip_not_tendstoInMeasure` proves the converse false. |
| 5 | Weakly convergent sequences are controlled by tightness/Prokhorov | The escaping-Dirac contradiction invokes `isTightMeasureSet_of_isCompact_closure`. |
| 6 | Weak and vague convergence stay distinct, with an exact compact bridge | `ProbabilityMeasure.tendstoVaguely_of_tendsto` and `tendsto_iff_tendstoVaguely`. |
| 7 | Empirical CDF results feed an actual empirical weak limit | `tendsto_empiricalProbabilityMeasurePM_ae`; `empiricalProbabilityMeasure_Iic` and `_Iio` are the reused interfaces. |
| 8 | Coordinate maps are measurable and cylinders generate the product sigma-field | Compile-time examples in `MeasureTheory/Constructions/SemanticRegression.lean`. |
| 9 | Projectivity direction is not reversed | Direct typed example of `hP I J hJI`. |
| 10 | A concrete three-coordinate system recovers all prescribed marginals | `threeCoinFamily_isProjective` and `threeCoin_projectiveLimit_recovers`. |
| 11 | Empty index type needs no `Nonempty` assumption | `emptyIndex_projectiveLimit_isProbability` and `emptyIndex_existsUnique_projectiveLimit`. |
| 12 | Singleton and arbitrary finite marginals are recovered | Generic `projectiveLimitOfStandardBorel_map_restrict`, instantiated by the three-coordinate regression. |
| 13 | Independent arbitrary products use the canonical product measure | Direct regressions for `infinitePi_map_restrict` and `infinitePi_cylinder`. |
| 14 | Abstract standard-Borel coordinates require no chosen topology | A public-domain compile example has only `MeasurableSpace` and `StandardBorelSpace` assumptions. |
| 15 | External implementation names do not leak into public declarations | Facade declarations and axiom audit expose only `MeasureTheory` names; source scan finds the external module only in the private import boundary. |
| 16 | Different compatible Polish upgrades cannot change the result | `IsProjectiveLimit.eq_projectiveLimitOfStandardBorel` reduces any candidate to Mathlib's unique finite projective limit. |
| 17 | Arbitrary-index extension uses the approved exact external theorem | Facade implementation imports commit `7d76e184c3d2138a2741baf923b57e9a01b9cf25`; manifest and audit ledger pin it. |
| 18 | Extension is not inferred from finite products or Ionescu--Tulcea | The dependency boundary is explicit: arbitrary-index facade uses the audited extension theorem; product and sequential-kernel examples remain separate. |
| 19 | A finite projective family is not automatically probabilistic | `twoMassLimit_not_isProbabilityMeasure`. |
| 20 | A probability projective family infers a probability limit | Facade probability instance and the three-coordinate/empty-index instance checks. |
| 21 | External revision, license, holes, and build are audited | Exact Git revision, Apache-2.0 license, empty `sorry`/`admit`/`axiom`/`unsafe` scan, and 1773-job external build recorded in `MATHLIB_AUDIT.md`. |
| 22 | Existing de Finetti work remains compatible | Full `StochLean` build and `Audit/Axioms.lean` recheck `IsExchangeable.hasDeFinettiRepresentation`. |
| 23 | No path regularity is manufactured by a coordinate product law | Public output is only a raw product-space measure and coordinate recovery; path topology remains deferred. |

The mandatory cases compile in `Probability/MeasureConvergence/SemanticRegression.lean` and
`MeasureTheory/Constructions/SemanticRegression.lean`. All new milestone declarations are also
listed in `Audit/Axioms.lean`.

# Markov Processes, Kernels, Semigroups, and Convergence

This section is the complete joint disposition of the two Markov handoffs. Public APIs use raw
process functions and Mathlib kernels. No bundled Markov-chain/process type, duplicate kernel,
duplicate irreducibility predicate, or duplicate projective-limit construction is introduced.

## Information, transitions, and canonical laws

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Future information | Implemented | `Process/Filtration/Future.lean`: `futureMeasurableSpace`, antitonicity, the discrete `tailFromMeasurableSpace` bridge, and the infimum identity for the canonical tail sigma-field. |
| Forward transition systems | Implemented | `Markov/TransitionSystem.lean`: proof-indexed kernels exist only for `r <= s`; diagonal identity and `K r t = K s t comp K r s` use Mathlib's chronological composition order. |
| Homogeneous semigroups | Implemented | `Markov/Semigroup.lean`: `IsMarkovSemigroup`, commuting/opposite-order laws, kernel powers, and the natural-time transition-system bridge. |
| Kernel-free Markov property | Implemented | `Markov/Transition.lean`: event conditional expectations are primary; integrable future functions, bounded state tests, finite cylinders, and conditional-independence bridges are derived. |
| Transition representation | Implemented | `HasTransitionSystem` remains separate from `HasMarkovProperty`; it implies the kernel-free property and supports the exact countable-time strong-Markov event theorem. |
| Discrete canonical path law | Implemented / upstream | `Chain/PathLaw.lean` is a thin homogeneous specialization of Mathlib `Kernel.traj`; finite histories, one-time kernel-power marginals, adjacent-coordinate laws, and measurable state-map functoriality are proved. |
| General canonical coordinate law | Reused | Arbitrary-index Standard-Borel existence and uniqueness are the previous milestone's `projectiveLimitOfStandardBorel` and `existsUnique_isProjectiveLimit_of_standardBorel`; the process is the raw coordinate map. No Markov-private KET wrapper is added. |

## Countable chains, recurrence, invariance, and periodicity

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Reachability | Implemented bridge | Mathlib `Kernel.IsIrreducible Measure.count` remains canonical; `CanReach` is bridged to positive kernel powers without confusing its zero-time diagonal case with positive return. |
| Hitting and return times | Implemented | `Countable/Hitting.lean` uses `hittingAfter ... 1`, preserves `WithTop` infinity, and defines extended mean return time. |
| Recurrence / transience | Implemented | `Countable/Recurrence.lean` defines statewise recurrence, transience, positive and null recurrence and proves communication propagation. |
| Green kernel | Implemented | `Countable/Green.lean`: the ENNReal occupation series, path-law occupation identity, and recurrence criteria. |
| Renewal and hitting probabilities | Implemented | `Renewal.lean`, `HittingProbability.lean`, and `SetHitting.lean` prove first-return renewal equations, killed/safe kernel recursions, and almost-sure hitting under irreducibility plus an invariant probability. |
| Excursion occupation | Implemented | `Excursion.lean` and `Invariant.lean` construct the occupation measure, prove its singleton/mass formulas and invariance, and normalize it in the positive recurrent case. |
| Invariant probability and Kac | Implemented | Invariant probability implies positive recurrence, is unique under irreducibility, satisfies Kac's formula, and exists exactly in the irreducible positive recurrent case. |
| Periodicity | Implemented | `Periodicity.lean`: return-time gcd, communication invariance of period, eventual positivity on admissible residue classes, and the global aperiodicity interface. |

## Coupling and Klenke 18.11--18.13

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Generic coupling | Implemented | `Probability/Coupling/Basic.lean` defines only the marginal relation and event/full-TV bounds. |
| TV normalization correction | Implemented | `Coupling/TotalVariation.lean` uses the full signed-measure convention and proves the factor-2 mismatch bound; mutually singular Boolean Dirac laws regress to distance `2`. |
| Path coupling | Implemented | Couplings are measures on pairs of canonical path laws; successful coupling is the tail-mismatch condition and is equivalent to a.s. eventual equality. |
| Independent coalescent | Implemented semantically | `Coalescent.lean` uses the product kernel away from the diagonal and an absorbing diagonal, avoiding the corrupted OCR case split. |
| Klenke 18.11 | Implemented | `Klenke.lean` proves diagonal hitting for the independent product and semantic coalescent chains from irreducibility, aperiodicity, and an invariant probability. |
| Klenke 18.12 | Implemented | `Convergence.lean` turns successful coalescence into full-TV convergence between arbitrary rows, with the corrected factor `2`. |
| Klenke 18.13 | Implemented | `Equilibrium.lean` proves the full equivalence among aperiodicity, convergence from every state, convergence from some state, and convergence from every initial probability. |

## Bounded Q-matrices and Feller semigroups

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Q-matrix | Implemented | `Generator/QMatrix.lean` uses off-diagonal nonnegativity and summability, diagonal row balance, `exitRate`, and singleton right derivatives in `HasQMatrix`. |
| Uniformization | Implemented | `Generator/Uniformization.lean` constructs the one-step kernel and Poisson-mixture semigroup, including the mandatory safe `Lambda = 0` identity branch, semigroup law, and generator recovery. |
| Rate independence / canonical uniqueness | Implemented | `Generator/Uniqueness.lean` proves the exact lazy-kernel relation, Poisson Cauchy convolution, independence from any two valid dominating rates, and unique existence of `IsCanonicalBoundedQSemigroup`. This is law-level uniqueness of the canonical bounded-Q construction, not raw equality of processes on unrelated sample spaces. |
| Poisson acceptance | Implemented | `Generator/Poisson.lean` proves the pure-birth Q-matrix, recovers `poissonMeasure (rate * t)` from zero at positive rate, checks the zero-rate law, and recovers the generator. |
| Klenke Feller predicate | Implemented | `Feller.lean` uses Mathlib `ZeroAtInftyContinuousMap`, includes the Markov semigroup laws, pointwise continuity at zero, C0 preservation, contraction operators, and correct operator composition order. |
| Weak/stochastic continuity | Implemented | The Feller interface reuses the measure-convergence layer for vague transition measures, weak probability laws on compact spaces, state-variable weak continuity, and convergence to `dirac x` at time zero. |
| Feller pointwise-to-sup-norm equivalence | Deferred by source protocol | Klenke 21.26 points outward; Revuz--Yor, Chapter III, Proposition 2.4 is the locator to audit. The proof text was not available in the local source set, so no original substitute is attempted. |
| Klenke 21.27 RCLL strong-Markov realization | Deferred by source protocol | Klenke points to Rogers--Williams Vol. 1, Chapter III.7ff/8ff and Revuz--Yor Chapter III, Theorem 2.7. Those proof texts were not locally accessible, so realization is not claimed. |

## Markov source corrections and semantic regressions

- Kernel orientation is pinned by an explicit noncommuting deterministic-kernel regression:
  `eta comp kappa` means first `kappa`, then `eta`.
- `CanReach x x` uses time zero, while positive return and recurrence use `hittingAfter ... 1`.
- The coalescent kernel is defined by product/absorbing semantics, not the OCR piecewise formula.
- Full TV has diameter `2`; coupling mismatch bounds therefore carry a factor `2`.
- The Poisson Q-matrix regression has a positive successor entry and a negative diagonal entry,
  pinning the OCR-sensitive `x != y` condition.
- Zero-rate domination forces the zero Q-matrix and gives the identity semigroup; no division by
  zero is used.
- Two distinct valid domination rates give definitionally different construction inputs but the
  same semigroup by `uniformizedSemigroup_rate_independent`.
- `IsFellerSemigroup` remains Klenke's pointwise-at-zero predicate; no second strong-continuity
  definition is introduced.

## Blocker and deferred-dependency ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| MK-B01 | RESOLVED | Process Core supplied natural/usual filtrations, common-event path predicates, progressive measurability, and stopping-time APIs consumed by the Markov layer. |
| MK-B02 | RESOLVED | Measure Convergence and Projective Construction supplied weak/vague convergence, Ionescu--Tulcea, and the Standard-Borel projective-limit facade. |
| MK-B03 | RESOLVED | Bounded-Q construction and canonical semigroup uniqueness are proved by uniformization and rate independence, including `Lambda = 0`; Poisson is the cross-package acceptance case. |
| MK-B04 | DEFERRED | Future Feller/functional-analysis owner. Revuz--Yor III, Proposition 2.4 must be concretely retrieved and audited before the pointwise-to-sup-norm theorem is added. Current C0 preservation, contraction, operator, weak, and stochastic-continuity APIs are unaffected. |
| MK-B05 | DEFERRED | Future path-regularization owner. Retrieve/audit Rogers--Williams III.7ff/8ff or Revuz--Yor III, Theorem 2.7 before adding the RCLL strong-Markov realization. No current theorem claims every realization is RCLL. |
| MK-D01 | DEFERRED | Semimartingales and stochastic integration belong to the later package planned in this repository. |
| MK-D02 | DEFERRED | Stochastic differentials and SDEs belong to the separate package stated in `README.md`. |
| MK-D03 | DEFERRED | MCMC applications and spectral rates belong to a future application/finite-state layer and do not block the foundation. |

All implemented Markov declarations are included in the full build and representative
load-bearing results are inspected in `Audit/Axioms.lean`. The authorized external rows are the
only deferred items; neither is replaced by a placeholder declaration.

# Fourier Probability and Classical Limit Theorems

This is the current disposition of
`StochLean_FourierProbability_ClassicalLimitTheorems_Design_v0.1.pdf`. The milestone is **not
complete**: the files listed as implemented below provide canonical foundations, not surrogate
statements of the missing limit theorems.

## Characteristic functions and classical limits

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Characteristic functions and independent sums | Reused | Mathlib's measure-first `charFun`, `IndepFun.charFun_map_add_eq_mul`, and finite-family characteristic-function product API. No StochLean characteristic-function object was added. |
| Weak convergence and Levy continuity | Reused | Ordinary `Tendsto` on `ProbabilityMeasure` and `ProbabilityMeasure.tendsto_iff_tendsto_charFun` from `Mathlib.MeasureTheory.Measure.LevyConvergence`. |
| Scalar iid CLT | Reused | `tendstoInDistribution_inv_sqrt_mul_sum` and its centered form from `Mathlib.Probability.CentralLimitTheorem`. |
| Multivariate Gaussian laws | Reused | Mathlib's positive-semidefinite covariance Gaussian construction, including singular covariance. |
| Cramer--Wold / multivariate iid CLT bridge | STILL-BLOCKED | No exact active-pin projection criterion or ready multivariate CLT declaration was found. A duplicate scalar/Fourier proof has not been introduced. |
| Polya criterion | STILL-BLOCKED | No exact active-pin/local theorem with the frozen continuity/evenness/range/convexity assumptions was found. |
| Moment determinacy and even-derivative converse | STILL-BLOCKED | The duplicate audit found no exact probability-facing declarations; generic owner and natural moment hypotheses still require proof design. |
| Bochner theorem | DEFERRED | Klenke delegates the proof; the exact cited proof has not been recovered and audited. |
| Berry--Esseen | DEFERRED | Klenke's external source has not been recovered and audited; no independent replacement is declared. |

## Triangular arrays, Lindeberg, and ordered series

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Raw triangular arrays and nonempty rows | Implemented foundation | `LimitTheorems/TriangularArray.lean`: `TriangularArray` and the separate `HasNonemptyRows` predicate. |
| Measurability, row independence, centering, normalization | Implemented foundation | Separate predicates; no cross-row independence or hidden centering/normalization. |
| Row-sum variance | Implemented | `variance_triangularRowSum_eq_sum` and `variance_triangularRowSum_eq_one`. |
| Null arrays | Implemented | Finite-row maximum-tail definition, entry bound, eventual-uniform formulation, and `isNullArray_iff_eventual`. A sum of tail probabilities is not used as the definition. |
| Positive-scale Lindeberg/Lyapunov predicates | Implemented foundation | `LimitTheorems/Lindeberg.lean`; ENNReal nonnegative expectations and explicit positive scales avoid division by zero. |
| Lyapunov implies Lindeberg | STILL-BLOCKED | The moment-tail inequality and ENNReal scaling proof remain to be formalized. |
| Lindeberg implies null array | Implemented | `SatisfiesUnitLindeberg.isNullArray` proves the unit-scale result by a restricted-measure Markov bound; `SatisfiesLindeberg.isNullArray` applies it to independent normalized rows. |
| Lindeberg--Feller forward CLT | STILL-BLOCKED | The mandatory characteristic-function/finite-measure proof is not implemented. No converse or false `iff` is exported. |
| Lindeberg--Feller converse | DEFERRED | Klenke cites source [155], Theorem III.4.3; its proof has not been recovered and audited. |
| Ordered series semantics | Implemented foundation | `Series/ThreeSeries.lean`: ordinary prefix sums, common-event a.s. random convergence, exact `abs <= K` truncation, and the three source conditions. |
| Kolmogorov three-series theorem | STILL-BLOCKED | The equivalence and its finite-variance martingale helper remain unproved. This remains a hard blocker for Levy--Khintchine existence. |

## FP-LT blocker and deferred ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| FP-B01 | RESOLVED | Active-pin characteristic-function, Levy-continuity, scalar-CLT, Gaussian, independence, and weak-topology APIs were mapped to Mathlib. |
| FP-B02 | RESOLVED | No local overlap was found; final raw triangular-array public names are implemented. |
| FP-B03 | STILL-BLOCKED | Polya and moment/derivative gaps require generic proofs after exact statement design. |
| FP-B04 | DEFERRED | Recover and audit [155], Theorem III.4.3 before any Lindeberg--Feller converse. |
| FP-B05 | DEFERRED | Recover and audit Klenke's cited Bochner proof before adding a theorem. |
| FP-B06 | DEFERRED | Recover and audit [155], Chapter III, Section 11 before Berry--Esseen. |
| FP-B07 | STILL-BLOCKED | Kolmogorov three-series is absent from the active pin and local tree; its full proof is required before LSII Levy--Khintchine existence. |
| FP-B08 | STILL-BLOCKED | No exact active-pin Cramer--Wold/multivariate-CLT bridge was found. |
| FP-D01 | DEFERRED | Infinite divisibility and Levy--Khintchine are owned by LSII below. |
| FP-D02 | DEFERRED | Convolution semigroups and SII are owned by LSII below. |
| FP-D03 | DEFERRED | Donsker and topological path-space weak convergence belong to Functional Weak Convergence. |
| FP-D04 | DEFERRED | Brownian construction/path regularity belongs to BM-PR below. |

`LimitTheorems/SemanticRegression.lean` currently pins predicate separation, maximum rather than
sum semantics, the null-array equivalence, positive scales, the Lindeberg-to-nullity bridge, and
the inclusive truncation boundary.
It does not count as the missing theorem proofs.

# Levy and Stationary Independent Increments Foundations

This is the current disposition of
`StochLean_Levy_StationaryIndependentIncrements_Design_v0.1.pdf`. The milestone is **not
complete**, chiefly because FP-B07 and the real Levy--Khintchine proof chain remain open.

## Law and process foundations

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Probability-law convolution and powers | Implemented | `Convolution/Semigroup.lean` closes Mathlib measure convolution in `ProbabilityMeasure` and proves associativity, commutativity, Dirac laws, and additive convolution powers. |
| Basic/continuous convolution semigroups | Implemented foundation | The basic predicate contains only the semigroup law; the positive-time weak limit at zero is a separate refinement. |
| Exercises 14.4.1--14.4.4 | Partially implemented | `convPow_root` gives the exact semigroup roots and `roots_tendsto_zero` proves their weak convergence to `δ₀`; general continuity propagation and nonnegative-support closure remain open. |
| SII predicate | Implemented | `Process/StationaryIndependentIncrements.lean` combines the existing `HasStationaryIncrements` and Mathlib `HasIndepIncrements` without a bundled Levy-process type. |
| SII to convolution semigroup | Implemented | `HasStationaryIndependentIncrements.isConvolutionSemigroup` uses genuine increment independence and stationary laws. |
| Semigroup to coordinate SII process | STILL-BLOCKED | The corrected `NNReal`/`Nat` projective construction through the StochLean KET facade remains to be implemented. |
| Infinite divisibility | Implemented foundation | Law-first positive-integer roots; every full-time convolution-semigroup marginal is infinitely divisible without a continuity assumption. |
| Compound Poisson | Implemented foundation | Genuine Poisson mixture over convolution powers, explicit zero-rate law, and zero-safe `ofFiniteMeasure`; the latter recovers the rate/jump presentation on `r • μ`. |
| Compound-Poisson intensity addition and ID | Implemented | `CompoundPoisson.law_add` proves the convolution law by Tonelli and Poisson addition; the induced convolution semigroup proves `CompoundPoisson.isInfinitelyDivisible`, including zero intensity. |
| Compound-Poisson characteristic function | STILL-BLOCKED | The mandatory exponential characteristic-function formula remains open. |
| Compound-Poisson approximation of ID laws | STILL-BLOCKED | Klenke 16.5 and its weak-topology bridge remain open. |

## Levy measures, triplets, and stable laws

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Minimal Levy measure | Implemented foundation | Atom zero plus finite `lintegral (min 1 (x^2))`; `IsLevyMeasure.sigmaFinite` is derived from finite level sets and is not installed globally. |
| Infinite-activity acceptance example | STILL-BLOCKED | The required explicit infinite-total-mass Levy measure regression has not yet been formalized. |
| Fixed truncation and triplet data | Implemented foundation | `levyTruncation x = x` exactly on `abs x < 1`; `LevyTriplet` contains only Gaussian variance, drift, jump measure, and its Levy-measure proof. |
| Levy exponent integrability | STILL-BLOCKED | Small-jump complex Taylor domination and large-jump finiteness are not yet proved. |
| Real Levy--Khintchine existence and uniqueness | STILL-BLOCKED | No theorem is declared. Existence depends on FP-B07; uniqueness and nonvanishing/log corollaries remain downstream. |
| ID to continuous semigroup and SII | STILL-BLOCKED | Corollary 16.10 awaits the unique triplet/exponent layer and the semigroup-to-process construction. |
| Stable predicates | Implemented foundation | Non-Dirac broad, strict, and indexed predicates with genuinely positive affine scale; strict-to-broad bridges and zero-safe `signedLogAbs`. |
| Broad stable implies ID | Implemented | `IsStableInBroadSense.isInfinitelyDivisible` explicitly inverts the positive affine witness and divides the translation among the positive number of convolution roots. |
| Triplet affine transformation | STILL-BLOCKED | The exact truncation drift correction is not yet implemented; the current `nsmul` data operation is not claimed as Levy--Khintchine transformation theorem. |
| Stable classification and explicit exponent | STILL-BLOCKED | Klenke 16.22--16.25, including the `alpha != 1` versus `alpha = 1` branches, remain open. |
| Null-array ID limit theorems 16.12--16.13 | DEFERRED | Klenke's cited external proof has not been recovered and audited. |
| Domains of attraction 16.26--16.30 | DEFERRED | Entire block belongs to `StableLimitTheory`; no orphan predicate was added. |

## LSII blocker and deferred ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| LS-B01 | RESOLVED | Canonical Mathlib measure convolution was reused and the probability-law closure/powers were added. |
| LS-B02 | RESOLVED | Existing stationary- and independent-increment predicates were reused. |
| LS-B03 | STILL-BLOCKED | Correct semigroup-to-SII projective construction is missing. |
| LS-B04 | RESOLVED | No exact active/local compound-Poisson law existed; the zero-safe finite-intensity foundation, intensity-addition law, and infinite divisibility are implemented. |
| LS-B05 | STILL-BLOCKED | Minimal declarations are fixed, but Levy--Khintchine existence/uniqueness remains the central unresolved theorem. |
| LS-B06 | STILL-BLOCKED | Required complex Taylor and Levy-integrand domination lemmas remain open. |
| LS-B07 | STILL-BLOCKED | Stable affine-triplet and real-power scaling API remains open. |
| LS-B08 | STILL-BLOCKED | Gamma/trigonometric identities for the explicit stable exponent remain open. |
| LS-D01--LS-D05 | DEFERRED | Cadlag Levy realization, PPP/Levy--Ito, Skorokhod weak convergence, Levy stochastic integration, and multidimensional/LCA Levy--Khintchine retain their later owners. |
| LS-D06 | DEFERRED | External null-array ID theorem proof not available. |
| LS-D07 | DEFERRED | Stable domains of attraction move together to `StableLimitTheory`. |

# Brownian Motion and Path Regularity Foundations

This is the current disposition of `StochLean_BrownianMotion_PathRegularity_Design_v0.2.pdf`.
The active pin supplies the canonical law predicates and transformations, but the package is **not
complete**.

## Canonical reuse and implemented bridges

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Pre-Brownian/Brownian predicates | Reused | Mathlib `IsPreBrownianReal` and `IsBrownianReal`; no StochLean Brownian structure was added. |
| Gaussian laws, covariance, independent increments | Reused | Active Mathlib Brownian and Gaussian modules, including `eval_zero_ae_eq_zero`, increment laws, covariance, shift independence, negation, scaling, shift, and upstream inversion. |
| Brownian SII and marginal ID | Implemented bridge | `Brownian/Transformations.lean` proves SII, the Gaussian increment-law convolution semigroup, and infinite divisibility. |
| Time inversion natural-domain bridge | Implemented | Explicit piecewise value at zero, positive-time formula, equality to upstream, and pre-Brownian preservation. |
| Kolmogorov--Chentsov conclusion | STILL-BLOCKED | Active Mathlib has only `IsKolmogorovProcess` foundations. The audited external source contains the required theorem, but its exact snapshot does not compile unchanged against stable v4.33 because it redeclares an active Mathlib theorem. A minimal adapted port is still required. |
| Continuous/Holder Brownian representative | STILL-BLOCKED | Depends on the KC port; no false path-regularity claim is derived from finite-dimensional laws. |
| Gaussian covariance characterization | Reused | Mathlib's `IsGaussianProcess.isPreBrownianReal_of_covariance` exactly reconstructs the canonical pre-Brownian finite-dimensional law from centered Gaussian marginals and covariance. |
| Brownian bridge | Implemented foundation | `brownianBridge` has a Gaussian-process proof, a.s. zero initial endpoint, pointwise zero terminal endpoint, centered marginals, and covariance `min s t - s*t` on the unit interval. |
| Blumenthal, PWZ, strong Markov, reflection, arcsine | STILL-BLOCKED | No corresponding implementation was present in the audited external snapshot; the staged StochLean proofs remain open. |
| Haar/Schauder Brownian construction | STILL-BLOCKED | The distinction between deterministic-time `L2` convergence and special a.s.-uniform convergence remains enforced but unimplemented. |
| Deterministic Wiener integral | STILL-BLOCKED | Basis-independent `L2` linear isometry and Section 21.5 applications remain open; no Ito-integral surrogate is declared. |

## Exact external audit and blocker ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| BM-X01 | STILL-BLOCKED | `RemyDegenne/brownian-motion` at `314f04a34ff75e18fd383917ae7fe7d77beb1b6f`, Apache-2.0, was checked out and scanned: the 27-module relevant closure has no `sorry`, `admit`, or project axiom. Stable-v4.33 source compilation fails at the already-upstream `Set.indicator_apply_apply`; a minimal canonical-owner port must remove the duplicate and revalidate the remaining closure. |
| BM-B01 | RESOLVED | Active Mathlib v4.33 supplies canonical `IsPreBrownianReal`/`IsBrownianReal` and the basic transformation layer. |
| BM-B02 | STILL-BLOCKED | Full KC conclusion/minimal external port is unresolved. |
| BM-B03 | STILL-BLOCKED | Holder covering and exponent-monotonicity API awaits the port. |
| BM-B04 | STILL-BLOCKED | Brownian stopping-field limit and Blumenthal modulo-law transfer proofs remain open. |
| BM-B05 | STILL-BLOCKED | First-passage/supremum/last-zero measurable APIs remain open. |
| BM-B06 | STILL-BLOCKED | Hilbert/Lp/ONB/Haar/deterministic-Wiener overlap remains to be audited and built. |
| BM-B07 | RESOLVED | Sections 21.1--21.3 and 21.5 source boundary is frozen by the handoff. |
| BM-D01--BM-D07 | DEFERRED | Doob/general SII regularization, Feller realization, functional weak convergence/Donsker, continuous quadratic variation, LIL/Skorohod, and Ito integration retain the owners specified by the design. |

The Brownian semantic regression currently checks the a.s. zero law, explicit inversion zero case,
SII bridge, marginal infinite divisibility, the Gaussian covariance characterization, the bridge
endpoint/covariance layer, and the nonzero scaling hypothesis. It does not stand in for the missing
common-event Holder, strong-Markov, reflection, arcsine, or Wiener theorems.

# Cross-milestone reproducibility blocker

The historical root manifest does not list the inherited `checkdecls` dependency of the pinned
`exchangeability` package. Regenerating the manifest forces a source rebuild of that package,
whose pinned revision targets pre-v4.33 Mathlib APIs and fails against the active v4.33 pin.
Previously cached oleans allow unrelated modules to be checked, but are not accepted as a clean
build proof. The repository lockfile has therefore been restored rather than silently updating or
vendoring an unaudited patch. Resolving this requires a compatible exact exchangeability revision
or a reproducible, attribution-preserving minimal port of its used theorem closure.
