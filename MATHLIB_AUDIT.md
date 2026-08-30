# Pinned Mathlib audit

Baseline: Lean/Mathlib `v4.33.0`, resolved Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Searches covered the pinned checkout, the complete
local tree, and the approved-external ledger before each public gap was added.

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
