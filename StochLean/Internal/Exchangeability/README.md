# Internal exchangeability proof implementation

This directory contains the project-maintained proof implementation used by StochLean's public
reverse-martingale and de Finetti APIs. It is compiled as part of the ordinary `StochLean` library
against the repository's pinned Lean/Mathlib version; it is not a Lake dependency and does not use
precompiled artifacts from an external exchangeability package.

The proof architecture and substantial source lineage were ported from Cameron Freer's
Apache-2.0 `exchangeability` project at audited revision
`e0532e59ceff23edab44dda9ab0655debbc9cc22`. Original copyright, license headers, and authorship are
retained in the Lean files. StochLean owns compatibility maintenance, namespace isolation, build
integration, public facade design, and regression/axiom checks for this internal copy.

Public users should import modules under `StochLean.Probability.*`; declarations under
`StochLean.Internal.Exchangeability` are implementation details and may change without a public
API migration promise.
