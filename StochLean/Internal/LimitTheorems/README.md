# Audited Lindeberg--Feller implementation lineage

The files in this directory are an attribution-preserving internal adaptation of the
Lindeberg--Feller proof from `statopia/statlean4` at exact commit
`dd2c4bbc72b7c643e62985d77c84755b31aec9f5`.

The relevant upstream files were distributed with Apache-2.0 source headers. Before adaptation,
the proof closure was checked for `sorry`, `admit`, project-defined axioms, and unsafe
declarations. The implementation was then reorganized under StochLean's internal namespace and
connected to StochLean's public triangular-array predicates. It is compiled directly against the
pinned Mathlib version and is not imported from, linked to, or resolved through the upstream
package.

The public StochLean theorem is
`ProbabilityTheory.SatisfiesLindeberg.tendsto_map_triangularRowSum_standardGaussian`. The converse
direction is deliberately absent because it is outside the audited proof closure required by the
design.
