# Pinned Mathlib audit

Baseline: Lean/Mathlib `v4.33.0`, resolved Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Searches covered the pinned checkout, the complete
local tree, and the approved-external ledger before each public gap was added.

## Global external-source rule

Mathlib is the only external Lean package permitted in the final dependency graph. An external
repository may be used only as an implementation reference after exact-revision statement,
dependency, proof-hole, axiom, build, provenance, and license review. Accepted code is copied into
the StochLean source tree, adapted to StochLean's mathematical owner and public API, and compiled
without an import or Lake dependency on the source repository. External names and module layouts
have no normative force. This is a permanent project rule for every present and future design
document.

## Reuse and gap decisions

| Topic / design row | Pinned result | Decision |
| --- | --- | --- |
| Ch.1 generated spaces and measure uniqueness | Mathlib generated measurable spaces and `Measure.ext_of_generateFrom_of_cover` | Reuse; no compatibility wrapper required. |
| Klenke 1.65 semiring approximation | Exact theorem `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` in `MeasureTheory/Measure/MeasuredSets.lean` | Reuse; audit-first row closed as upstream. |
| Ch.2 independence/generators/regrouping | Canonical `Indep`, `iIndep`, `IndepFun`, `iIndepFun`; anchors include `iIndepSet.indep_generateFrom_of_disjoint` and `iIndepFun.indepFun_finset` | Reuse. |
| Laws of independent sums | Generated additive theorems `IndepFun.hasLaw_add` and `IndepFun.map_add_eq_map_conv_map₀` | Reuse for laws; add only the thin PGF expectation specialization. |
| Probability generating functions | No canonical PGF for `PMF ℕ` | Add `PMF.pgf`, the measure/law bridge, analytic layer, and safe-domain semantics. |
| PGF factorial derivative/moment boundary | General iterated-derivative, locally uniform sum, monotone-convergence, and ENNReal tools exist, but no probability theorem connects them | Add generic arbitrary-order derivative identification and `ℝ≥0∞` boundary theorem in `Analytic.lean`. |
| Discrete setwise convergence | PMF coefficient and summability APIs exist; no direct arbitrary-set convergence theorem from atomwise convergence | Add `PMF.setMassReal` and the tight-tail/discrete-Scheffé theorem `PMF.tendsto_setMassReal_of_tendsto_mass`. |
| Discrete PGF convergence | No matching atomwise/PGF equivalence | Add in `Probability/Convergence/Discrete.lean`. |
| `PoissonLimitThm` | Canonical i.i.d. binomial point-probability limit exists | Re-export upstream; add only the non-i.i.d. Bernoulli triangular-array result. |
| Finite independent Bernoulli sum law | `PMF.poissonBinomial` exists, but no generic family-to-law bridge | Add `iIndepFun.hasLaw_fintype_sum_bernoulli`. |
| Random sums | `PMF.bind` and `PMF.map` exist; no law-level random-sum PGF API | Build convolution powers and random sums from canonical monadic operations. |
| Galton-Watson | No matching construction/PGF/extinction fixed-point API | Add law-level branching modules. |
| Probability multinomial law | Only `Nat.multinomial` and product-measure primitives; no categorical-count PMF theorem | Add generic `PMF.multinomial` and `iIndepFun.hasLaw_categoricalCounts`. |
| Poissonized multinomial splitting | Poisson laws and characteristic functions exist; no finite categorical Poisson-mixing theorem | Add `PMF.poissonizedMultinomial_eq_independentPoissonCounts`. |
| Wald 5.5 / Blackwell-Girshick 5.10 | Independence integration and moment primitives exist; no matching random-count identities found | Add generic stopped-sum theorems in `Probability/Moments/RandomSum.lean`. |
| Paley-Zygmund exercise | Holder/Cauchy-Schwarz primitives exist; no matching zero-threshold probability inequality | Add multiplicative and quotient forms. |
| Empirical CDF / Glivenko-Cantelli | No matching empirical-CDF or GC declaration | Add strict/non-strict CDF APIs and full arbitrary-law uniform theorem; reuse `strong_law_ae`. |
| Kolmogorov maximal inequality 5.28 | Martingale maximal APIs exist, but no exact independent centered square-integrable specialization with the textbook bound | Add the square-submartingale bridge and Kolmogorov specialization. |
| Strong-law rate 5.29 | Borel-Cantelli exists; no exact Klenke dyadic/logarithmic rate theorem | Add the rate package after the maximal inequality. |
| Process representation and independent increments | Canonical processes are functions; `HasIndepIncrements` exists | Reuse and introduce no process structure. |
| Stationary increments | No exact generic predicate found | Add one function-based reusable predicate. |
| Poisson process / P1-P5 characterization | Poisson measures and independent increments exist, but no counting-process predicate or interval-axiom equivalence | Add corrected common-event path semantics and both directions of Klenke 5.34. |
| Klenke 5.35 uniform points | No probability multinomial/Poissonization package | Reuse the new generic distribution modules; keep process-specific code thin. |
| Klenke 5.36 exponential arrivals | Exponential measures exist; no arbitrary finite ordered-partition arrival/count law or needed simplex-volume bridge | Add generic simplex/cumulative-coordinate measure results and the full construction theorem. |
| Local convergence in measure | Mathlib `TendstoInMeasure` is global | Add `TendstoLocallyInMeasure` by finite restrictions. |
| Exhaustion metric and local completeness | No inducing pseudo/metric or sigma-finite Cauchy-completeness package | Add raw pseudometric, `AEEqFun` metric, fast convergence, subsequences, and completeness. |
| Uniform integrability / finite Vitali | Mathlib `UniformIntegrable`, `UnifTight`, `tendsto_Lp_finite_of_tendstoInMeasure`, and `tendstoInMeasure_iff_tendsto_Lp` exist | Reuse on finite restrictions and as canonical compatibility targets. |
| Klenke sigma-finite envelope UI | No exact literal envelope/tail/density package | Add separately named predicates and equivalences; do not shadow Mathlib UI. |
| de la Vallee-Poussin | No full superlinear-envelope bridge/converse found | Add sufficient and finite-measure converse theorems. |
| Klenke 7.3 | Mathlib `Lp` completeness exists; no local-convergence plus powered-envelope characterization | Add one generic bridge in `LpLocalConvergence.lean`. |
| Klenke 7.47/7.49/7.50 `Lp` dual representation | Holder pairing exists, but no exact general dual representation theorem was found | Explicitly defer to general functional-analysis/ForMathlib, as authorized by the handoff. |
| Conditional expectation and distributions | Canonical `condExp`, `Kernel`, `condDistrib`, `StandardBorelSpace`, and `condExp_ae_eq_integral_condDistrib` exist | Reuse; add only natural-domain and law-a.e. uniqueness guards. |
| External results 2.46, 5.30, 5.32 | No approved external dependency was admitted | Explicitly deferred; no hidden trust-boundary dependency. |

## Semantic and public-domain checks

- `PMF.pgf` accepts only `unitInterval`; the heavy-tail regression proves no outside-domain
  convergence is assumed.
- `PMF.factorialMoment` and the derivative boundary theorem use `ℝ≥0∞`, preserving infinite
  factorial moments.
- `TendstoLocallyInMeasure` is distinguished from global `TendstoInMeasure`; raw functions use
  a pseudometric and only a.e. classes receive a metric.
- The corrected Poisson process has one common full-measure monotone/right-continuous path event.
- The exponential-arrival proof establishes every finite partition and compiles an explicit
  four-increment application.
- `DivergentArrivalSequence.count` requires a divergence witness.
- Conditional-event APIs require positive mass, and conditional-kernel uniqueness is law-a.e.
- No project theorem relies on a conclusion-shaped premise, `sorry`, `admit`, or a
  project-defined axiom.

## Process Core duplicate audit

The Process Core audit used the same pinned commit and searched the full current local tree before
adding declarations.

| Topic / design row | Pinned result | Decision |
| --- | --- | --- |
| Process laws and finite-dimensional laws | `IdentDistrib`; `Measure.map`; `map_restrict_eq_of_forall_ae_eq`; `map_eq_of_forall_ae_eq` in `Mathlib.Probability.Process.FiniteDimensionalLaws` | Reuse. Local bridges only name the distinct modification semantics and explicitly avoid path-space-law claims. |
| Independent increments | `ProbabilityTheory.HasIndepIncrements` | Reuse the canonical predicate. |
| Gaussian process | `ProbabilityTheory.IsGaussianProcess` in `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.{Def,Basic,Independence}` | Reuse; no local predicate. |
| Modification / indistinguishability | No matching process predicates found | Add `IsModification` and `Indistinguishable`, relation operations, countable collapse, and the dense right-continuous collapse. |
| Stationarity | No generic full-shift process-law predicate found | Add `IsStationary` by coordinate-product law, not marginal equality. |
| Natural filtration | `Filtration.natural` and `Filtration.stronglyAdapted_natural` exist; no direct order-minimality theorem found | Add only `Filtration.natural_le_of_stronglyAdapted`. |
| Predictable processes | `Filtration.predictable`; `IsStronglyPredictable.isStronglyProgressive`; `.stronglyAdapted`; `.measurable_add_one`; `.iff_measurable_add_one` | Reuse completely. |
| Right-continuous filtration | `Filtration.rightCont`, `le_rightCont`, `rightCont_self`, and `Filtration.IsRightContinuous` | Reuse. |
| Usual conditions | No combined right-continuity plus initial-completeness property found | Add `Filtration.IsUsual` with completeness relative to all ambient null sets. |
| Completed right continuation | `MeasureTheory.NullMeasurableSpace`, `Measure.completion`, and `Filtration.rightCont` exist separately; no filtration augmentation combining them was found | Add `nullSets`, `withNullSets`, and `usualAugmentation` on the genuinely completed ambient type. |
| Product/joint measurability | No process-level predicate found; ordinary `Measurable (Function.uncurry X)` is canonical | Add the thin name `IsProductMeasurable` and direct coordinate/path/process consequences. |
| Progressive measurability | Mathlib `IsProgressive` and `IsStronglyProgressive` | Reuse; no second predicate. |
| Continuous adapted process is progressive | `StronglyAdapted.isStronglyProgressive_of_continuous` | Reuse for continuous paths. |
| Right/left-continuous adapted process is progressive | No exact theorem found in pinned Mathlib | Add ceiling/floor-grid theorems for `ℝ≥0`; also add joint measurability for right-continuous paths. |
| A.s. regular paths give a progressive version | No exact theorem found | Add explicit modification constructions under usual completeness, changing the process only on the one common null event. |
| Adapted plus product measurable gives progressive modification | No approved Mathlib/local/external implementation found; Klenke attributes the result externally | Explicitly defer; no hidden dependency or unsupported theorem. |
| Stopping times and stopped sigma-algebras | `IsStoppingTime`, `.measurableSet_eq`, `isStoppingTime_of_measurableSet_eq`, `.min`, `.max`, `.add_const`, `.add`, `.measurableSpace`, and `.measurableSpace_mono` | Reuse. |
| Stopped process/value | `stoppedProcess`, `stoppedValue`, `IsStronglyProgressive.stoppedProcess`, and `measurable_stoppedValue` | Reuse; add one right-continuous adapted evaluation bridge. The theorem does not interpret Mathlib's total fallback at `τ = ∞`. |
| Hitting times | `hittingBtwn`, `hittingAfter`, `Adapted.isStoppingTime_hittingBtwn`, and `Adapted.isStoppingTime_hittingAfter` | Reuse with exact order/path hypotheses. |
| Cadlag path predicate | No generic common-a.s. predicate found | Add trajectory predicates only; defer Skorokhod topology. |
| Doob regularization and path-space topology | No Process Core implementation authorized | Explicitly defer to their designated later packages. |

## Process Core semantic checks

- The diagonal spike on the unit interval is a modification of zero but is not indistinguishable;
  its coordinate-product map law still agrees with zero.
- A Boolean Rademacher process has equal one-time marginals at all times but fails full
  stationarity because its first pair and shifted pair have different equality laws.
- A constant trivial filtration is right-continuous but is not usual for a Dirac probability on a
  nontrivial ambient measurable space.
- `usualAugmentation` changes to `NullMeasurableSpace Ω P` and `P.completion`, contains the original
  information, and is proved usual; no same-ambient completion is asserted.
- Right- and left-continuous adapted paths imply progressive measurability by countable-range
  approximations. Under usual conditions the a.s. variants produce explicit modifications.
- Predictable-to-progressive-to-adapted and the discrete `F n` measurability of `X (n+1)` use exact
  Mathlib declarations.
- The always-infinite stopping time retains `WithTop` infinity on a probability-one event.

## Discrete martingale and exchangeability duplicate audit

| Topic / design row | Pinned result or approved source | Decision |
| --- | --- | --- |
| Martingale predicates and conditional expectation | Mathlib `Martingale`, `Submartingale`, `condExp`, stopped processes, and filtration APIs | Reuse; local adapters do not define a second martingale notion. |
| Discrete stochastic integral | No named exact Klenke-indexed transform API found | Add `discreteStochasticIntegral` and prove its algebraic/probabilistic interface. |
| Quadratic variation / bracket | Mathlib has square-integrability and conditional expectation primitives but no matching discrete predictable-bracket package | Add pathwise and predictable processes with exact stopped compatibility. |
| Optional sampling | Bounded stopping theorems exist upstream | Reuse them; add only UI and a.s.-finite limit bridges. |
| Doob `L^p` | General upstream maximal inequality exists | Reuse and expose the exact sharp real-valued specialization; preserve `1 < p`. |
| Finite-bracket convergence | No exact predictable-bracket criterion found | Add predictable localization and derive Klenke 11.14 from ordinary martingale convergence. |
| Exchangeability | No pinned Mathlib finite-dimensional exchangeability predicate | Add the f.d.d.-correct local predicate; do not use equality of marginals as a surrogate. |
| Reverse conditional expectation | Upstream conditional expectation and martingale convergence exist | Add the antitone-filtration interface and exact infimum-field convergence. |
| de Finetti | No pinned Mathlib theorem with the required standard-Borel product-mixture statement | Maintain the audited proof closure internally under `StochLean/Internal/Exchangeability` and expose only the structural StochLean facade. |
| Empirical measure and symmetric factorization | No exact finite-tuple empirical-measure recovery/factorization API found | Add nonempty empirical measures, multiplicity recovery, permutation reconstruction, and plain factorization. |
| Invariant vs tail sigma-field | Raw `T ≤ E` is deterministic; no exact modulo-law equality was found upstream or in the audited source closure | Add the `L¹` finite-block relocation proof and explicit `MeasurableSpace.EqModulo`. |
| Hewitt-Savage | Mathlib has Kolmogorov zero-one, not Hewitt-Savage | Derive Hewitt-Savage through the modulo-tail theorem; no duplicate Kolmogorov proof. |

The exchangeability/de Finetti proof lineage was audited for its exact source revision, license,
dependency closure, and placeholder scan before being ported into the project. Original copyright
and Apache-2.0 attribution are retained in every internal source file. Project-facing milestone
declarations are rechecked independently in `Audit/Axioms.lean`.

## Measure convergence and projective construction duplicate audit

| Topic / design row | Pinned Mathlib or approved source result | Decision |
| --- | --- | --- |
| Standard Borel vocabulary | Mathlib `StandardBorelSpace`; distinct from `BorelSpace` | Reuse; define no local Borel-space class. |
| Weak convergence | Topology of `ProbabilityMeasure` with `tendsto_iff_forall_integral_tendsto` | Reuse ordinary `Tendsto`; define no `Weak` predicate. |
| Portmanteau | Closed/open limsup/liminf criteria and null-frontier set-mass convergence | Reuse completely. |
| Tightness / Prokhorov | `IsTightMeasureSet`, compact-closure implications in both directions on the canonical hypotheses | Reuse completely. |
| Convergence in distribution / Slutsky | `TendstoInDistribution`, `TendstoInMeasure.tendstoInDistribution`, `.continuous_comp`, `.prodMk_of_tendstoInMeasure_const`, and related corollaries | Reuse completely. |
| A.e.-continuous mapping | No theorem with exactly a measurable map and limit-law-null discontinuity set found | Add the Portmanteau bridge `ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous`. |
| Vague convergence | No canonical convergence-against-`C_c` predicate found | Add `TendstoVaguely` with local finiteness built into its semantics; add weak-to-vague and compact-space equivalence bridges. |
| Levy continuity | Pinned `Mathlib.MeasureTheory.Measure.LevyConvergence` contains the canonical characteristic-function/tightness package | Reuse; add no theorem. |
| Empirical weak convergence | Rational-interval pi-system criterion exists, but no theorem consumes StochLean's empirical object | Add only `tendsto_empiricalProbabilityMeasurePM_ae`, reusing the existing empirical CDF and measure APIs. |
| Cylinders / product sigma-field | `measurableCylinders`, `generateFrom_measurableCylinders`, coordinate measurability | Reuse. |
| Arbitrary product measure | `Measure.infinitePi`, projectivity, finite restriction, and cylinder formulas | Reuse. |
| Kernels / Ionescu--Tulcea | `ProbabilityTheory.Kernel.traj`, `trajMeasure`, and their finite-prefix/conditional-law API | Reuse. |
| Projective family and limit | Mathlib `IsProjectiveMeasureFamily` and `IsProjectiveLimit`, including finite uniqueness and probability preservation without nonempty index | Reuse the vocabulary and consequences. |
| Arbitrary-index standard-Borel extension | Not present in the pinned Mathlib checkout; `RemyDegenne/kolmogorov_extension4` supplied the audited reference construction | Internalize the proof under `StochLean.Internal.KolmogorovExtension` and expose a minimal StochLean facade; temporary Polish upgrades remain implementation-only, and no external package remains in the dependency graph. |
| Process/canonical path wrapper | Product coordinates are already functions and no path topology follows from projective construction | Add nothing; use `fun i ω ↦ ω i`. |

### Audited Kolmogorov-extension implementation reference

- Repository: `https://github.com/RemyDegenne/kolmogorov_extension4.git`.
- Exact audited commit: `7d76e184c3d2138a2741baf923b57e9a01b9cf25`. This revision records
  provenance only; it is not present in `lakefile.toml` or `lake-manifest.json`.
- License: Apache License 2.0.
- Audit checkout: `D:\Math\external-audit\kolmogorov_extension4-7d76e184c3d2138a2741baf923b57e9a01b9cf25`;
  its audited source is content-equal to the clean Git checkout at the pinned commit (line-ending
  normalization is the only byte-level difference).
- Placeholder/trust scan: no Lean occurrence of a declaration beginning with `axiom` or `unsafe`,
  and no `sorry` or `admit`.
- Independent reference build: successful, 1773 jobs.
- Project-facing axiom audit: `isProjectiveLimit_projectiveLimit` and every facade theorem depend
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- Internalization boundary: the adapted modules are compiled from
  `StochLean/Internal/KolmogorovExtension`; imports and namespaces were redirected to project
  owners. Public signatures contain only Mathlib/StochLean types and namespaces, and the external
  project is neither imported nor linked.

The complete fourth-milestone semantic gate is recorded as 23 numbered cases in `SOURCE_MAP.md`.

## Markov-process duplicate and source audit

| Topic / design row | Pinned Mathlib or approved project result | Decision |
| --- | --- | --- |
| Kernels and composition | Mathlib `ProbabilityTheory.Kernel`, `Kernel.comp`, powers, sums, maps/comaps, `compProd`, and deterministic kernels | Reuse completely; local declarations are relations or specialized constructions over the canonical kernel. |
| Transition systems / semigroups | No pinned forward-pair transition-system or homogeneous kernel-semigroup predicate with the required orientation was found | Add raw-function predicates `TransitionSystem`, `IsMarkovTransitionSystem`, and `IsMarkovSemigroup`; pin `K r t = K s t comp K r s`. |
| Future sigma-field | Mathlib tail sigma-field exists for sequences, but no generic time-indexed future sigma-field | Add `futureMeasurableSpace`; prove the discrete bridge to Mathlib's tail construction. |
| Markov property | No exact kernel-free event conditional-expectation predicate and transition-representation split was found | Add `HasMarkovProperty` and `HasTransitionSystem`; reuse Mathlib `condExp`, `CondIndep`, filtrations, and kernels in all bridges. |
| Discrete path law | Mathlib `Kernel.traj`, `partialTraj`, projective-limit correctness, and conditional-trajectory theorems | Add only the homogeneous specialization `markovChainPathKernel`/`markovChainLaw` and its kernel-power marginal interface. |
| General canonical path law | StochLean's audited Standard-Borel Kolmogorov facade and Mathlib `IsProjectiveLimit` | Reuse; add no Markov-private product-measure or projective-limit object. |
| Irreducibility | Mathlib `Kernel.IsIrreducible Measure.count` and `Kernel.CanReach` | Reuse as the only irreducibility/reachability notions; add strict-positive-return bridges where Klenke differs on the diagonal. |
| Hitting times | Mathlib `hittingAfter` and `WithTop` random-time APIs | Reuse; define only Markov-specific return/hitting events and extended means. |
| Recurrence / Green / excursion | No exact countable-chain statewise package found | Add the Klenke-level predicates and occupation constructions, using canonical path laws and ENNReal sums. |
| Invariant / reversible measures | Mathlib `Kernel.Invariant` and `Kernel.IsReversible` | Reuse unchanged; add normalization, uniqueness, positive-recurrence, and Kac bridges. |
| Periodicity | No countable-kernel return-time gcd interface found | Add `transitionTimes`, `period`, communication propagation, and aperiodicity without a second irreducibility notion. |
| Generic couplings | No exact measure marginal relation plus the required full-TV convention was found | Add the thin coupling relation and event/full-TV bounds; retain Mathlib signed-measure variation as the normalization source. |
| Coalescent chain | No semantic independent-coalescent kernel found | Add product-off-diagonal/absorbing-diagonal construction; do not copy the corrupted Klenke OCR formula. |
| Klenke 18.11--18.13 | No matching countable-chain coupling-to-full-TV equivalence package found | Build from canonical irreducibility, invariant measures, periods, path couplings, and total variation. |
| Q-matrix | No conservative countable-state Q-matrix predicate or kernel-semigroup right-derivative relation found | Add `IsQMatrix`, `exitRate`, and `HasQMatrix`; off-diagonal nonnegativity explicitly requires unequal states. |
| Uniformization | Poisson measures and kernel powers exist; no bounded-Q Poisson-mixture semigroup or safe zero-rate construction | Add the mixture, semigroup/generator proofs, rate-independence theorem, and canonical uniqueness predicate. |
| Feller functions | Mathlib `ZeroAtInftyContinuousMap` | Reuse exactly; define no local C0 type. |
| Feller semigroup | No exact Klenke 21.26 predicate was found | Add the pointwise-at-zero/C0-preserving predicate and induced contraction operator. Do not redefine it by sup-norm continuity. |
| Feller strong-continuity equivalence | Klenke cites external literature; exact Revuz--Yor III, Proposition 2.4 proof text unavailable locally | DEFERRED under the mandatory external-proof policy; no independent replacement proof. |
| Feller RCLL strong-Markov realization | Klenke cites Rogers--Williams III.7ff/8ff and Revuz--Yor III, Theorem 2.7; proof text unavailable locally | DEFERRED under the mandatory external-proof policy; no realization theorem is declared. |

The Markov source scan found no alternative approved implementation of the new predicates or
theorems at the pinned revision. The two external Feller rows are recorded as deferred rather than
treated as permission to invent a proof. All other decisions and source corrections are mirrored
in the final Markov section of `SOURCE_MAP.md`.

## Fourier probability and classical-limit duplicate audit

The active v4.33 pin supplies the canonical measure-first characteristic function, independent-sum
product identities, Gaussian characteristic functions, Levy continuity through
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`, and the scalar iid CLT through
`tendstoInDistribution_inv_sqrt_mul_sum`. These are reused directly. Searches of the pinned
Mathlib tree and full local StochLean tree found no exact Kolmogorov three-series theorem,
Lindeberg/Lyapunov triangular-array package, Lindeberg--Feller theorem, Polya criterion, or exact
multivariate Cramer--Wold CLT bridge.

The surviving local declarations therefore own raw dependent triangular arrays, separated
hypothesis predicates, the finite variance identity, maximum-tail nullness and its eventual form,
positive-scale Lindeberg/Lyapunov conditions, Lyapunov-to-Lindeberg and Lindeberg-to-nullity,
the forward Lindeberg--Feller theorem, ordered-series/truncation semantics, the complete
Kolmogorov three-series equivalence, and a thin PSD multivariate iid CLT bridge. The forward
Lindeberg--Feller proof is an attribution-preserving internal port of the audited Apache-2.0
StatLean proof lineage at exact commit `dd2c4bbc72b7c643e62985d77c84755b31aec9f5`; it imports no
external package. Klenke's externally delegated converse and Berry--Esseen theorem remain deferred
pending recovery of the exact cited proofs.

An independent finite-dimensional Bochner implementation was also audited at Apache-2.0 commit
`58405ecd328cf8383a1c0b53d37605fe61a0b3f6`. Its source closure contains no proof holes or project
axioms, but it is not Klenke's cited proof and targets a different Mathlib revision (plus an
unrelated package dependency in its project manifest). Under the source protocol it is retained
only as a reference: StochLean neither imports it nor exposes its names. Pólya and the exact
moment-determinacy/even-derivative converse remain explicitly identified generic candidates; no
stronger replacement theorem is claimed.

## Levy/SII duplicate audit

| Topic | Active-pin/local result | Decision |
| --- | --- | --- |
| Convolution | Mathlib `Measure.conv` is canonical but does not close the operation in `ProbabilityMeasure` | Add the thin probability-law closure and convolution powers; do not define another measure convolution. |
| Stationary/independent increments | StochLean `HasStationaryIncrements` and Mathlib `HasIndepIncrements` | Reuse and combine only as a predicate; no `LevyProcess` bundle. |
| Convolution semigroup | No exact law-family predicate with the frozen basic/continuous split | Add the two thin predicates without a hidden identity-at-zero assumption. |
| Infinite divisibility | No exact active-pin probability-law predicate | Add positive-integer existential convolution roots. |
| Compound Poisson | Poisson measures and measure bind exist; no finite-intensity compound-Poisson probability law | Add a genuine bind mixture and zero-safe finite-measure entry point; prove common-jump intensity addition by Tonelli and derive infinite divisibility from the resulting semigroup. |
| Levy measure/triplet | No canonical active-pin definitions | Add the minimal atom/integral predicate, derive sigma-finiteness, validate infinite activity with an explicit infinite-mass geometric atomic example, and add data-only fixed-truncation triplets. |
| Levy--Khintchine | No exact active-pin theorem | Implemented entirely inside StochLean: triplet-to-law approximation, weighted canonical-root converse extraction, uniqueness, and the nonnegative specialization. No external Lean package is linked. |
| Stable laws | No matching active-pin law predicates/classification | Project-owned non-Dirac broad/strict/indexed predicates, affine/triplet scaling, index existence and bound, homogeneous jump density, Gaussian endpoint, corrected centering branches, and source-safe exponent expressions are implemented. |

The finite-intensity compound-Poisson API handles `ν = 0` before normalization and proves
`ofFiniteMeasure (r • μ.toFiniteMeasure) = law r μ`; the proof does not use a zero denominator.
The Levy-measure predicate does not store sigma-finiteness and does not install a global instance.

The LS-B08 audit searched the pinned Mathlib Gamma, beta, Mellin, improper-integral, and
trigonometric-integral modules, the complete local tree, and public Lean source search. No existing
oscillatory Gamma integral implementation suitable for the active pin was found. Direct inspection
of Klenke Remark 16.23 exposed a more fundamental source defect: an arbitrary translation keeps
the same Levy measure but adds `i*d*t` to the exponent. `StableExponent.lean` therefore internalizes
the two printed Gamma/trigonometric expressions as project-owned, zero-safe APIs, proves continuity
of the exceptional logarithmic term, supplies the explicit location correction, and proves the
translation obstruction. It deliberately exports no false theorem claiming that a jump measure
alone determines the complete exponent. This resolves the audit item as a source correction; no
external package, namespace, or API is retained.

## Brownian/path-regularity duplicate and external audit

The active Mathlib pin contains `ProbabilityTheory.IsPreBrownianReal` and
`ProbabilityTheory.IsBrownianReal` in `Mathlib.Probability.BrownianMotion.Basic`, together with
evaluation laws, covariance, independent increments, Gaussian characterization components,
negation, nonzero scaling, shifts, whole-past shift independence, time inversion, and the exact
centered-Gaussian covariance characterization. StochLean therefore adds no parallel Brownian
object. Its current Brownian module supplies SII/law-level bridges, an explicit piecewise
time-inversion theorem at zero, and the source-facing Gaussian Brownian-bridge transform with its
endpoint, mean, and covariance laws.

The generic active-pin `Mathlib.Probability.Process.Kolmogorov` defines
`IsKolmogorovProcess`/`IsAEKolmogorovProcess` and their measurable representatives, but not the
Kolmogorov--Chentsov Holder-modification conclusion required by the handoff.

The approved external repository `https://github.com/RemyDegenne/brownian-motion` was checked out
at exact commit `314f04a34ff75e18fd383917ae7fe7d77beb1b6f`:

- license: Apache-2.0;
- relevant transitive source closure: 27 Lean modules, 6459 source lines;
- proof-hole/trust scan: no `sorry`, `admit`, declaration beginning with `axiom`, or unsafe
  declaration in that closure;
- exact revision was confirmed by Git;
- a direct stable-v4.33 source build does not pass unchanged because
  `BrownianMotion/Auxiliary/Algebra.lean` redeclares `Set.indicator_apply_apply`, which is already
  present in the active Mathlib pin.

The useful proof closure was subsequently internalized under `StochLean/Internal/Brownian` at that
exact audited revision. Active-pin duplicates such as `Set.indicator_apply_apply` were removed,
imports and namespaces were redirected to StochLean/Mathlib owners, and the resulting source was
rebuilt as part of the ordinary project graph. The external repository is neither imported nor
linked; its exact revision and Apache-2.0 provenance are recorded in the internal directory.

The remaining Brownian document results are project-owned constructions over this foundation and
the pinned Mathlib Brownian API: the canonical continuous coordinate realization, simultaneous
subcritical Holder regularity, covariance characterization, bridge and conditional bridge laws,
Blumenthal zero--one, finite-stopping-time strong Markov cylinders, strict/closed reflection,
Levy's full arcsine CDF, pointwise Paley--Wiener--Zygmund nowhere differentiability, Schauder
uniform convergence, and the basis-independent deterministic Wiener linear isometry.

## Clean-build reproducibility audit

The external `exchangeability` package and inherited `checkdecls` dependency have been removed
from both `lakefile.toml` and `lake-manifest.json`. The used reverse-martingale and de Finetti proof
closure now lives under `StochLean/Internal/Exchangeability` and compiles against the pinned
Mathlib v4.33.0 environment. The public reverse-martingale, conditional-IID, de Finetti, Bernoulli,
and exchangeability regression modules are built from those local sources, so the build no longer
depends on cached external oleans.
