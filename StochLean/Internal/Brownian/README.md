# Internal Kolmogorov--Chentsov implementation

This directory contains the StochLean-owned implementation used by
`StochLean.Probability.Process.Regularity.KolmogorovChentsov`.

The proof architecture and an initial code version were audited against
[`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion)
at commit `314f04a34ff75e18fd383917ae7fe7d77beb1b6f`, licensed under Apache-2.0.
The code was internalized under `StochLean.Internal.Brownian.*`, its imports were
rewired to StochLean/Mathlib owners, and declarations already supplied by the pinned
Mathlib revision were removed. The repository does not import or link the external package.

These modules are implementation details. Public users should import the StochLean
regularity facade instead of importing files from this directory.
