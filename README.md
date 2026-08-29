# StochLean

StochLean is a Lean 4 library for probability foundations and stochastic processes. Its roadmap
follows Chapters 1-8 of Achim Klenke's *Probability Theory: A Comprehensive Course* (3rd edition)
while reusing Mathlib whenever a canonical implementation already exists.

The implementation baseline is Lean 4 and Mathlib `v4.33.0`. The library is organized by
mathematical function, not textbook chapter. Processes are ordinary functions
`X : T → Ω → E`; the project does not introduce a parallel stochastic-process structure.

## Trust and semantics

- Project source contains no `sorry`, `admit`, or project-defined axioms.
- Public declarations undergo a duplicate audit against the pinned Mathlib revision.
- Pointwise, almost-everywhere, finite-dimensional-distribution, and path-law statements are
  kept distinct.
- An almost-sure path property uses one common full-measure event for the whole trajectory.
- Conditional-expectation APIs expose their natural hypotheses instead of relying on
  totalized fallback values.

The normative handoff specification is preserved in
[`docs/StochLean_Klenke_Ch01-08_Design_v0.1.pdf`](docs/StochLean_Klenke_Ch01-08_Design_v0.1.pdf).
The source mapping and duplicate decisions are recorded in [`SOURCE_MAP.md`](SOURCE_MAP.md)
and [`MATHLIB_AUDIT.md`](MATHLIB_AUDIT.md).

## Build

```text
lake update
lake build
lake env lean Audit/Axioms.lean
```

The current implementation status, including intentionally visible remaining proof obligations,
is tracked in [`SOURCE_MAP.md`](SOURCE_MAP.md).

The repository is licensed under Apache-2.0. Klenke's book is a mathematical reference only
and is not distributed with this repository.
