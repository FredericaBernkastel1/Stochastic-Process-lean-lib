# Source map

This ledger maps the current StochLean modules to the normative design handoff and to Achim
Klenke, *Probability Theory: A Comprehensive Course*, third edition. The book is a mathematical
reference and is not distributed in this repository.

The status column is deliberately strict: “implemented” means the declarations compile without
project axioms or placeholders; “upstream” means the pinned Mathlib theorem is re-exported;
“partial” identifies a remaining proof obligation rather than silently weakening the result.

| Reference | Design deliverable | StochLean / Mathlib implementation | Status |
| --- | --- | --- | --- |
| Klenke 3.2–3.3 | PGF definition, basic bounds, continuity, analytic interior, uniqueness | `Probability/GeneratingFunction/Basic.lean`; `Analytic.lean` | Implemented |
| Klenke 3.7 | Discrete coefficient convergence and PGF convergence | `Probability/Convergence/Discrete.lean` | Both directions and the equivalence theorem implemented |
| Klenke 3.8 | Poisson approximation | `Probability/LimitTheorems/PoissonApproximation.lean`; Mathlib `PoissonLimitThm` | Binomial theorem upstream; non-identically distributed Bernoulli triangular-array theorem implemented in both square-smallness and maximum-smallness forms |
| Klenke 3.9 | Random sums and PGF composition | `Probability/GeneratingFunction/RandomSum.lean` | Implemented at law level |
| Klenke 3.10–3.11 | Galton–Watson recursion and extinction | `Probability/Branching/Basic.lean`; `Extinction.lean` | Generation PGF iteration, finite extinction laws, and least-fixed-point theorem implemented |
| Klenke 5.22–5.23 | Empirical CDF and Glivenko–Cantelli | `Probability/EmpiricalProcess/CDF.lean`; `StrongLaw.lean`; `GlivenkoCantelli.lean` | Finite-sample strict/non-strict APIs, common-event pointwise strong laws, and the full uniform a.s. theorem for arbitrary real laws (including atoms) implemented |
| Klenke 5.34 | Poisson-process interval-axiom characterization | `Probability/Process/Poisson/Basic.lean`; `IntervalAxioms.lean`; `IntervalAxiomsConverse.lean`; `IntervalAxiomsConverseLaw.lean` | Implemented in both directions. The converse identifies dyadic occupation sums as Poisson-binomial, controls their mismatch with interval counts, passes point masses to the Poisson limit, and reconstructs the full process predicate |
| Klenke 5.35–5.36 | Uniform-point and exponential-arrival constructions | `Probability/Process/Poisson/Constructions.lean` | Partial: deterministic uniform-point counts, nonexplosive arrival/count inversion, monotonicity, and right continuity are implemented. The multinomial/Poisson-mixing law and arbitrary finite ordered-partition arrival law remain |
| Klenke 6.2 | Local convergence in measure | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean` | Implemented |
| Klenke 6.7 | Exhaustion pseudometric for local convergence in measure | `ForMathlib/MeasureTheory/Function/LocalConvergenceMetric.lean` | Finite-measure truncated-integral characterization, canonical spanning-set reduction, raw-map pseudometric, quotient metric, and equivalence with local convergence implemented |
| Klenke 6.12 | Fast convergence and Borel--Cantelli criteria | `ForMathlib/MeasureTheory/Function/FastConvergenceLocal.lean` | Local summable-bad-set criterion and complete-target fast-Cauchy criterion implemented |
| Klenke 6.16–6.18 | Sigma-finite envelope uniform integrability and closure | `ForMathlib/MeasureTheory/Function/DeLaValleePoussin.lean` plus Mathlib `UniformIntegrable`/`UnifTight` | Canonical decomposition, finite-measure compatibility, finite-family/add/sub/neg/domination closure implemented; literal envelope/tail presentation remains |
| Klenke 6.25 | Exact sigma-finite Vitali convergence | `Probability/Convergence/LocalVitali.lean` plus Mathlib `UniformIntegrable`/`UnifTight` | Implemented in both directions for local convergence in measure and the separately named envelope-uniform-integrability package |
| Klenke Ch. 6 | Local pseudometric, subsequence and completeness package | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean`; `LocalConvergenceMetric.lean`; `FastConvergenceLocal.lean`; `CauchyInMeasureLocal.lean` | Exhaustion pseudometric and a.e.-quotient metric, fast-convergence/Borel--Cantelli criteria, sigma-finite a.e. subsequences, every-subsequence characterization, and full Cauchy completeness for complete metric targets implemented |
| Klenke 6.19 / 7.3 | de la Vallée-Poussin criterion and local `Lᵖ` bridge | `ForMathlib/MeasureTheory/Function/DeLaValleePoussin.lean`; `Probability/Convergence/LocalVitali.lean` | Superlinear-envelope tail bound, sufficient criteria, and the canonical local-`Lᵖ` Vitali characterization are implemented; the converse superlinear-envelope construction and explicit `‖f‖^p` presentation remain |
| Design path semantics | Common full-measure event; right-continuity; indistinguishability | `Probability/Process/Path/Monotone.lean`; `RightContinuous.lean` | Implemented |
| Design increment semantics | Stationary increments without assuming `X 0 = 0` | `Probability/Process/StationaryIncrements.lean` | Implemented |

## Semantic choices

- A process remains a function `T → Ω → E`; no competing process structure is introduced.
- Almost-sure path properties quantify one common full-measure event over the entire path.
- The PGF is exposed on `unitInterval`; the analytic real series is used only on its proved
  convergence region.
- Natural subtraction in the Poisson increment law is only used under an ordered-time hypothesis,
  together with an almost-sure monotone-path requirement.
- The exponential-arrival count requires an explicit divergence proof, so explosive sequences do
  not receive a totalized fallback count.
