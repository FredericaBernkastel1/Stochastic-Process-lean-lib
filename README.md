# StochLean

StochLean is a Lean 4 library for probability theory and stochastic processes. Its goal is to give
people and software agents working with stochastic processes a directly reusable Lean library,
reducing the time required to formalize and verify related mathematics. It provides a
kernel-checked layer between Mathlib's measure/probability foundations and larger developments in
martingales, Markov processes, Brownian motion, Levy processes, stochastic integration, and
probabilistic applications.

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
5. [Markov Processes](docs/StochLean_MarkovProcesses_Design_v0.1.pdf) - future information,
   transition systems, Markov semantics, countable-chain recurrence, coupling, generators, and
   Feller interfaces.
6. [Markov Processes, Kernels, Semigroups, and Convergence](docs/StochLean_MarkovProcesses_Kernels_Semigroups_Design_v0.1.pdf) -
   the consolidated kernel/semigroup specification, source corrections, acceptance suite, and
   dependency ledger for the Markov layer.

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

Status last updated: **2026-08-31**. All six reviewed handoff milestones are implemented and
audited: **Klenke Chapters 01-08**, **Process Core and Information Flow**, **Discrete Martingale
Calculus and Exchangeability**, **Measure Convergence and Projective Construction**, and the two
consolidated **Markov Processes** specifications. The two externally sourced Feller results remain
explicitly deferred because their cited proof texts were not locally available; this is the
disposition required by the specifications rather than an unchecked local substitute.

### Formalized mathematical definitions

- Probability generating functions, factorial moments, random sums, multinomial laws,
  Poissonization, and Galton-Watson extinction probabilities.
- Empirical distribution functions and empirical probability measures.
- Global and sigma-finite local convergence in measure, fast local convergence, exhaustion
  pseudometrics and a.e.-class metrics, and sigma-finite uniform integrability.
- Process modification and indistinguishability; finite-dimensional, coordinate-product, and
  path-space laws; stationarity and stationary increments.
- Common-event continuous, left-continuous, right-continuous, cadlag, and monotone path properties.
- Natural filtrations, usual conditions and usual augmentation, adaptedness, progressive
  measurability, random times, and stopped processes.
- Poisson processes, arrival times, finite increment laws, and uniform-point representations.
- Discrete stochastic integrals, pathwise and predictable quadratic variation, stopped brackets,
  reverse martingales, and binary predictable representations.
- Finite-dimensional exchangeability, symmetrization, invariant and tail sigma-fields,
  conditional i.i.d. representations, and empirical-measure factorization.
- Weak and vague convergence of measures, tightness interfaces, convergence in distribution, and
  almost-sure weak convergence of empirical measures.
- Product-coordinate and cylinder sigma-fields, Ionescu-Tulcea trajectory measures, and
  arbitrary-index standard-Borel projective constructions.
- Future sigma-fields; forward-time transition systems; homogeneous Markov semigroups; kernel-free
  event-form Markov properties; transition representations; and canonical discrete chain path
  kernels and laws.
- Strictly positive hitting and return times, reachability and communication, recurrence and
  transience, Green kernels, excursion occupation measures, invariant probabilities, periods,
  aperiodicity, and positive/null recurrence.
- Probability couplings, event and full total-variation distances, path couplings, successful
  couplings, semantic independent-coalescent kernels, and convergence-to-equilibrium predicates.
- Q-matrices, exit rates, explicit uniformization rates, safe zero-rate kernels, Poisson-mixture
  semigroups, generator recovery, canonical bounded-Q semigroups, and rate-independent
  uniformization.
- Feller semigroups on Mathlib's `ZeroAtInftyContinuousMap`, their contraction operators, operator
  semigroup laws, vague/weak transition-law continuity, and stochastic continuity at zero.

### Formalized named theorems

- Paley-Zygmund inequality.
- Wald's identity and the Blackwell-Girshick variance identity.
- Kolmogorov maximal inequality.
- Glivenko-Cantelli theorem.
- Borel-Cantelli fast-convergence criterion.
- de la Vallee-Poussin criterion and Vitali convergence theorem.
- Doob maximal inequality.
- de Finetti representation theorem and the Hewitt-Savage zero-one law.
- Prokhorov and Slutsky theorems through canonical Mathlib reuse and StochLean bridges.
- Ionescu-Tulcea and Kolmogorov extension theorems through audited canonical dependencies and
  StochLean facades.
- Chapman-Kolmogorov equations and Kac's formula for irreducible positive recurrent chains.

The structural de Finetti implementation is pinned to audited commit
`e0532e59ceff23edab44dda9ab0655debbc9cc22`. The Kolmogorov extension facade is pinned to audited
Apache-2.0 commit `7d76e184c3d2138a2741baf923b57e9a01b9cf25`; neither dependency leaks a
non-canonical public representation into StochLean.

All project declarations build without placeholders. Audited milestone declarations depend only on
Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

### Project plan

The planned scope of this repository includes stochastic-process foundations, Markov processes and
semigroups, Brownian and Levy processes, path-space and Skorokhod weak convergence,
continuous-time martingales, semimartingales, and stochastic integration. Stochastic differential
calculus and stochastic differential equations (SDEs) will be developed in a separate package so
that this library can remain a focused and reusable stochastic-process foundation. Every new area
will retain the same audit-first milestone gate.

The detailed, theorem-level status is maintained in [SOURCE_MAP.md](SOURCE_MAP.md), while duplicate
decisions and exact Mathlib reuse are recorded in [MATHLIB_AUDIT.md](MATHLIB_AUDIT.md). README and
ledger status are updated at every document milestone before the corresponding push attempt.

## Repository layout

```text
StochLean/
  ForMathlib/MeasureTheory/Function/   generic convergence and UI extensions
  ForMathlib/MeasureTheory/Measure/    locally finite and vague-convergence extensions
  Probability/Branching/              Galton-Watson foundations
  Probability/Convergence/            discrete and local convergence bridges
  Probability/EmpiricalProcess/       empirical CDF and Glivenko-Cantelli
  Probability/GeneratingFunction/     PGF and law-level random sums
  Probability/LimitTheorems/          Poisson approximation
  Probability/Martingale/             discrete calculus, stopping, inequalities, convergence
  Probability/Exchangeability/        symmetry, reverse limits, empirical laws, de Finetti
  Probability/MeasureConvergence/      weak-convergence bridges and empirical weak limits
  Probability/Coupling/                generic couplings and total-variation bounds
  Probability/Markov/                  transition systems, chains, recurrence, coupling,
                                      generators, convergence, and Feller semigroups
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

The checked-in operational defaults are `--memory=24000` and `--threads=3`: the project budget is
24 GB of total build memory and three Lean worker threads. These limits are configurable defaults,
not mathematical or API requirements; developers may lower or raise them in `lakefile.toml`. Lean's
`--memory` flag is enforced per compiler process, so a host requiring a hard process-group-wide
24 GB ceiling should also serialize Lake compilation jobs or apply an operating-system memory cap.
The earlier 20 GB / one-thread settings remain the documented optional conservative configuration
for memory-constrained or highly contended hosts.

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

## Project notice

The project has undergone an initial review, but omissions and errors may still remain. If you find
an issue, please notify the author so that the library and its documentation can be corrected and
completed.
