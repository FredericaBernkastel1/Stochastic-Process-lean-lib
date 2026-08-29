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
| Klenke 3.7 | Discrete coefficient convergence and PGF convergence | `Probability/Convergence/Discrete.lean` | Coefficientwise-to-PGF direction implemented |
| Klenke 3.8 | Poisson approximation | `Probability/LimitTheorems/PoissonApproximation.lean`; Mathlib `PoissonLimitThm` | Binomial point-probability theorem upstream; triangular-array theorem remains |
| Klenke 3.9 | Random sums and PGF composition | `Probability/GeneratingFunction/RandomSum.lean` | Implemented at law level |
| Klenke 3.10–3.11 | Galton–Watson recursion and extinction | `Probability/Branching/Basic.lean`; `Extinction.lean` | Generation PGF iteration, finite extinction laws, and least-fixed-point theorem implemented |
| Klenke 5.34 | Empirical CDF and Glivenko–Cantelli | `Probability/EmpiricalProcess/CDF.lean`; `StrongLaw.lean` | Finite-sample API and pointwise a.s. convergence on one common event for all rational thresholds implemented; uniform a.s. theorem remains |
| Klenke 5.35–5.36 | Poisson-process characterizations and constructions | `Probability/Process/Poisson/Basic.lean`; `Constructions.lean` | P1–P5 API, marginal/stationary laws, and deterministic construction cores (including arrival/count inversion and right continuity) implemented; construction probability laws remain |
| Klenke 6.2 | Local convergence in measure | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean` | Implemented |
| Klenke 6.25 | Vitali convergence on finite restrictions | `Probability/Convergence/LocalVitali.lean` plus Mathlib `UniformIntegrable` | Implemented local bridge |
| Klenke Ch. 6 | Local pseudometric, subsequence and completeness package | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean` | Finite-restriction/global sigma-finite a.e. subsequences and the every-subsequence characterization implemented; pseudometric and completeness remain |
| Klenke 7.3 | de la Vallée-Poussin criterion and envelope UI bridge | Mathlib `UniformIntegrable` audit in `MATHLIB_AUDIT.md` | Remaining bridge/API work |
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
