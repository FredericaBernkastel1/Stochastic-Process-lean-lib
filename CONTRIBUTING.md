# Contributing

All contributions must build with the pinned toolchain and pass the following gates:

1. Search the pinned Mathlib checkout, all StochLean modules, and the approved-external ledger
   before adding a public declaration.
2. Record the search terms, inspected imports, and resolution in `MATHLIB_AUDIT.md`.
3. State the natural mathematical domain and all almost-everywhere/version qualifications.
4. Run `lake build` and the audit scripts.
5. Do not submit `sorry`, `admit`, project-defined axioms, or proofs that use a conclusion-shaped
   hypothesis.

Generic results belong in `StochLean/ForMathlib`; model-specific results belong under the
relevant `StochLean/Probability` namespace.
