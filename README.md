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

Status last updated: **2026-08-29**. The active milestone is **Klenke Chapters 01-08**.

### Implemented and verified

- Safe-domain probability generating functions, analytic uniqueness, atomwise/PGF convergence,
  triangular-array Poisson approximation, and law-level random sums.
- Galton-Watson PGF recursion, finite extinction laws, and the least-fixed-point extinction theorem.
- Empirical CDF APIs and the full Glivenko-Cantelli theorem for arbitrary real laws, including
  discontinuous distributions.
- Common-a.s. monotone and right-continuous path predicates, stationary increments, the corrected
  Poisson-process definition, exact P1-P5 interval axioms, and the forward characterization.
- Converse-Poisson foundations: linear interval mean, Markov multiple-jump bound, conversion of P5
  from `limsup` to a right-hand limit, dyadic multiple-jump error, and independent identically
  distributed Bernoulli occupation indicators.
- Deterministic cores for uniform-point and exponential-arrival Poisson constructions, including
  arrival/count inversion and right continuity.
- Sigma-finite local convergence in measure, finite-restriction compatibility, exhaustion
  pseudometric on raw functions, genuine metric on a.e. classes, fast-convergence and
  Borel-Cantelli criteria, subsequence principles, and completeness for complete targets.
- Initial local Vitali and de la Vallee-Poussin sufficient-direction bridges.

All current project declarations build without placeholders. Audited milestone declarations depend
only on Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

### Remaining in the Chapters 01-08 milestone

- Finish Klenke 5.34 by connecting finite Bernoulli occupation sums to the existing
  Poisson-binomial limit and identifying every interval count as Poisson.
- Complete the probability laws for the Klenke 5.35 uniform-point construction and the arbitrary
  finite-partition proof for the Klenke 5.36 exponential-arrival construction.
- Resolve the load-bearing multinomial dependency and all remaining Chapter 1-5 audit-first or
  build-candidate rows, including random-sum moment identities and maximal-inequality/rate items
  where genuine gaps survive.
- Complete Klenke's sigma-finite envelope uniform-integrability API, equivalent formulations,
  algebra/domination closure, the converse de la Vallee-Poussin construction, the exact
  sigma-finite Vitali theorem, and the local `Lp` characterization.
- Resolve Chapter 7-8 audit rows and add only conditional-event/conditional-expectation/kernel
  bridges that survive the duplicate audit.
- Compile the required semantic regression tests and close the final coverage, dependency,
  minimal-import, and source-correction audit.

### Planned subsequent milestones

1. **Process Core and Information Flow:** audit and implement only surviving gaps in process
   modification/indistinguishability, full-law stationarity, common-a.s. cadlag predicates, usual
   filtration conditions, joint/progressive measurability bridges, and random-time evaluation.
2. **Discrete Martingale Calculus - Part I:** audit and implement the discrete stochastic integral,
   pathwise quadratic variation and predictable bracket, optional-sampling gaps, inequalities,
   and bracket convergence only where Mathlib lacks canonical versions.
3. **Exchangeability and de Finetti - Part II:** build f.d.d.-correct exchangeability,
   symmetrization, exchangeability sigma-fields, a thin reverse-martingale adapter, empirical
   probability measures, conditional-iid vocabulary, Hewitt-Savage, and structural/directing
   measure de Finetti theorems using the completed Part I engine.

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
  Probability/Process/                process paths, increments, and Poisson processes
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
