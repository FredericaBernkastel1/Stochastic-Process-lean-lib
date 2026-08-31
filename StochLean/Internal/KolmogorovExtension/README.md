# Internal Kolmogorov extension implementation

This directory contains the project-maintained arbitrary-index Kolmogorov extension proof used by
the public `StochLean.MeasureTheory.Constructions.KolmogorovExtension` facade. It is compiled as
part of StochLean and does not require or expose an external Lean package.

The proof implementation is an attribution-preserving adaptation of Rémy Degenne and Peter
Pfaffelhuber's Apache-2.0 `kolmogorov_extension4` project at audited revision
`7d76e184c3d2138a2741baf923b57e9a01b9cf25`. The audited source contains no `sorry`, `admit`,
project-defined axioms, or unsafe declarations in this proof closure. The source modules
`CompactSystem.lean`, `RegularContent.lean`, and `KolmogorovExtension.lean` were moved under
`StochLean.Internal.KolmogorovExtension`, their imports were rewired to internal owners, and the
stable public interface remains the smaller Standard-Borel StochLean facade.

Copyright and authorship headers from the source are retained in every adapted Lean file. Public
modules should import the StochLean facade, not these implementation modules directly.
