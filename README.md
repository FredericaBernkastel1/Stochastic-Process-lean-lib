# StochLean

StochLean is a Lean 4 library for probability theory and stochastic processes. Its purpose is to
provide a reusable, kernel-checked layer between Mathlib's measure/probability foundations and
larger developments in martingales, Markov processes, Brownian motion, Levy processes, stochastic
integration, and probabilistic applications.

The mathematical coverage baseline is Achim Klenke's *Probability Theory: A Comprehensive Course*,
third edition. Klenke is a coverage and statement source, not a code dependency: canonical Mathlib
APIs are reused whenever they already provide the required semantics.

## Normative specifications and implementation order

Development follows these reviewed handoff specifications:

1. [Klenke Chapters 01-08](docs/StochLean_Klenke_Ch01-08_Design_v0.1.pdf) - probability foundations
   and the first stochastic-process consumers.
2. [Process Core and Information Flow](docs/StochLean_ProcessCore_InformationFlow_Design_v0.1.pdf) -
   process equivalence, stationarity, path semantics, filtrations, measurability, and random times.
3. [Discrete Martingale Calculus and Exchangeability](docs/StochLean_DiscreteMartingaleCalculus_Design_v0.1.pdf) -
   discrete martingale calculus first, followed by exchangeability, reverse martingales, and de
   Finetti theory.
4. [Measure Convergence and Projective Construction](docs/StochLean_MeasureConvergence_ProjectiveConstruction_Design_v0.1.pdf) -
   weak/vague convergence infrastructure, tightness and Prokhorov reuse, kernels and
   Ionescu-Tulcea, and Kolmogorov projective construction.

This order is mandatory. A later package consumes earlier canonical APIs and must not introduce
temporary duplicates merely to compile.

## Fixed global rules

These rules apply to every module and are not relaxed to finish a proof:

- **Pinned baseline:** Lean and Mathlib are pinned to `v4.33.0`. An upgrade triggers a new duplicate
  and semantic audit.
- **No duplicates:** before adding a public declaration, search the pinned Mathlib revision, the
  complete local library, and the approved-external ledger, in that order. A usable canonical
  result forbids a parallel implementation.
- **Functional organization:** files and namespaces are organized by mathematical purpose, never
  by textbook chapter.
- **Canonical representations:** processes remain functions `X : T -> Omega -> E`. Reuse
  Mathlib's `Measure`, `ProbabilityMeasure`, `Kernel`, `Lp`, `Filtration`, `Adapted`,
  `IsProgressive`, `IsStoppingTime`, `HasIndepIncrements`, martingale, and conditional-expectation
  infrastructure.
- **Semantic precision:** pointwise and a.e. statements, modification and indistinguishability,
  one-time/f.d.d./coordinate-product/path-space laws, global and local convergence in measure,
  predictable bracket and pathwise quadratic variation, and bounded and a.s.-finite stopping
  times are kept distinct.
- **Common-event path semantics:** an a.s. path property over uncountable time uses one common
  full-measure event for the entire trajectory.
- **Natural domains:** public theorems carry the genuine measurability, integrability,
  sigma-finiteness, positivity, and finiteness assumptions. Totalized fallback values are never
  used as mathematics.
- **Proof integrity:** project source contains no `sorry`, `admit`, project-defined axiom,
  conclusion-shaped premise, or vacuous surrogate model. Milestone declarations undergo axiom
  inspection.
- **Source corrections:** reviewed errata and semantic corrections override OCR or printed
  shorthand.
- **Minimal imports:** production modules use the narrow stable dependency closure practical for
  maintenance and possible upstreaming.
- **Milestone gate:** a document is complete only when every `BUILD` item is proved, every
  `AUDIT-FIRST`/`BUILD-CANDIDATE` item is resolved, every external item is audited or explicitly
  deferred, semantic regression tests pass, and the coverage map is complete.

## Current implementation status

Status last updated: **2026-08-30**. The **Klenke Chapters 01-08**, **Process Core and Information
Flow**, and **Discrete Martingale Calculus and Exchangeability** milestones are complete. The
active milestone is **Measure Convergence and Projective Construction**.

### Implemented and verified

- Safe-domain probability generating functions, analytic uniqueness, arbitrary-order derivative
  series, extended-value factorial-moment boundary limits, atomwise/setwise/PGF convergence,
  triangular-array Poisson approximation, and law/random-variable random-sum bridges.
- Galton-Watson PGF recursion, finite extinction laws, and the least-fixed-point extinction theorem.
- Generic multinomial laws, Poissonized multinomial splitting, Paley-Zygmund, Wald's identity,
  Blackwell-Girshick's variance identity, Kolmogorov's maximal inequality, and the Klenke strong-law
  rate consequence.
- Empirical CDF APIs and the full Glivenko-Cantelli theorem for arbitrary real laws, including
  discontinuous distributions.
- Common-a.s. monotone and right-continuous path predicates, stationary increments, the corrected
  Poisson-process definition, exact P1-P5 interval axioms, and both directions of Klenke 5.34.
- Klenke 5.35 at joint-law level through generic multinomial/Poissonization, and Klenke 5.36 for
  every finite ordered partition through simplex volume, cumulative-coordinate, exponential-gap,
  arrival/count inversion, boundary-nullity, and finite-increment-law theorems.
- Sigma-finite local convergence in measure, finite-restriction compatibility, exhaustion
  pseudometric on raw functions, genuine metric on a.e. classes, fast-convergence and
  Borel-Cantelli criteria, subsequence principles, and completeness for complete targets.
- Literal sigma-finite envelope/tail uniform integrability, closure and compatibility theorems,
  both directions of de la Vallee-Poussin on finite spaces, exact sigma-finite Vitali, and the
  Klenke 7.3 local-convergence characterization of `Lp` convergence.
- Complete reuse/defer disposition for Chapters 1, 2, 4, 7, and 8, plus regression tests for PGF
  domain, local-vs-global convergence, null modification, jump CDFs, path semantics, four Poisson
  increments, and conditional-law version semantics.
- Process modification and indistinguishability, their countable/right-continuous collapse
  theorems, full process-law stationarity, and formal counterexamples separating marginal laws,
  coordinate-product laws, and pathwise equality.
- Common-event continuous, left/right-continuous, and cadlag trajectory predicates; natural
  filtration minimality; precise usual conditions; and a mathematically correct usual
  augmentation on Mathlib's completed ambient measurable space.
- Product measurability and ceiling/floor-grid proofs that strongly adapted right- or
  left-continuous processes are progressive, including explicit progressive modifications for
  almost-sure regular paths under the usual conditions.
- The right-continuous information-flow chain through Mathlib stopping times and stopped values,
  plus regressions for predictable processes, incomplete right-continuous filtrations, and an
  always-infinite `WithTop` stopping time.
- Discrete stochastic integration with exact recursion and martingale preservation; pathwise and
  predictable quadratic variation; stopped-bracket compatibility; bounded and a.s.-finite
  optional sampling; sharp Doob `L^p`; binary martingale representation; reverse-martingale
  convergence; and Klenke 11.14 via predictable bracket localization.
- Finite-dimensional exchangeability, finite symmetrization, prefix-invariant and tail
  sigma-fields, exchangeable sample means and symmetrized LLNs, empirical probability measures,
  and set-theoretic factorization of symmetric statistics through the empirical measure.
- Structural standard-Borel de Finetti representation at exact audited external commit
  `e0532e59ceff23edab44dda9ab0655debbc9cc22`, its Bernoulli specialization, equality modulo an
  exchangeable law of the invariant and tail sigma-fields, and the Hewitt-Savage zero-one law.

All project declarations build without placeholders. Audited milestone declarations depend only on
Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

### Active work: Measure Convergence and Projective Construction

- Audit and expose pinned Mathlib's canonical weak-convergence, distribution-convergence,
  tightness, Prokhorov, product-measure, kernel, and Ionescu-Tulcea APIs without introducing a
  parallel `Weak` predicate.
- Implement only the confirmed convergence bridges and projective-family interfaces absent from
  Mathlib, then provide the standard-Borel Kolmogorov extension facade over the approved pinned
  external implementation.
- Add semantic regressions, exact source/duplicate ledgers, and axiom checks for every public
  milestone declaration.

### Planned subsequent milestones

1. **Measure convergence:** canonical weak convergence and convergence-in-distribution bridges,
   mapping/Slutsky/Portmanteau coverage, tightness and Prokhorov reuse, and the exact disposition
   of vague convergence and empirical-measure consumers.
2. **Projective construction:** product and kernel consistency, Ionescu-Tulcea reuse, finite
   projective families and limits, and an arbitrary-index standard-Borel Kolmogorov extension
   facade with uniqueness and probability preservation.

The detailed, theorem-level status is maintained in [SOURCE_MAP.md](SOURCE_MAP.md), while duplicate
decisions and exact Mathlib reuse are recorded in [MATHLIB_AUDIT.md](MATHLIB_AUDIT.md). README and
ledger status are updated at every document milestone before the corresponding push attempt.

## Repository layout

```text
StochLean/
  ForMathlib/MeasureTheory/Function/   generic convergence and UI extensions
  Probability/Branching/              Galton-Watson foundations
  Probability/Convergence/            discrete and local convergence bridges
  Probability/EmpiricalProcess/       empirical CDF and Glivenko-Cantelli
  Probability/GeneratingFunction/     PGF and law-level random sums
  Probability/LimitTheorems/          Poisson approximation
  Probability/Martingale/             discrete calculus, stopping, inequalities, convergence
  Probability/Exchangeability/        symmetry, reverse limits, empirical laws, de Finetti
  MeasureTheory/Constructions/         projective constructions and extension facades
  Probability/Process/                process laws, paths, filtrations, measurability, stopping,
                                      increments, and Poisson processes
Audit/Axioms.lean                      kernel dependency checks
docs/                                  normative handoff specifications
```

## Build and trust checks

```text
lake update
lake build
lake env lean Audit/Axioms.lean
```

The repository additionally scans project sources for `sorry`, `admit`, and project-defined
`axiom` declarations and records source coverage before a milestone is considered complete.

The checked-in Lean resource defaults are `--memory=24000` and `--threads=3`, corresponding to a
24 GB memory ceiling for each Lean compiler process and three Lean worker threads. These are
operational defaults, not mathematical or API requirements: developers may lower or raise them in
`lakefile.toml` to match the available machine. The earlier 20 GB / one-thread settings remain the
documented conservative fallback defaults for memory-constrained or highly contended hosts.

## Commit and push policy

- Work is committed locally in coherent, verified increments.
- README, source map, audit ledger, and axiom audit are synchronized whenever a document reaches
  its completion gate.
- A GitHub push is attempted after each complete design document.
- If GitHub is unavailable, the push is skipped without blocking local construction. The next
  completed document is committed normally, and all pending commits are pushed together at the
  following document boundary.

## License and provenance

StochLean is released under the [Apache License 2.0](LICENSE). Klenke's book is used only as a
mathematical reference and is not distributed in this repository. The included design handoffs
contain the approved coverage and source-correction ledger, not copyrighted textbook content.
