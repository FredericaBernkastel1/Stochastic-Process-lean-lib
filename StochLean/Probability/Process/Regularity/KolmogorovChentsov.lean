/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Internal.Brownian.Continuity.KolmogorovChentsov

/-!
# Kolmogorov--Chentsov regularization

This is the public StochLean owner for the generic process-regularity theorem used by
Brownian motion.  The implementation is kept under `StochLean.Internal.Brownian`; the public
mathematical API remains in the canonical process and `ProbabilityTheory` namespaces.

The main declaration is `ProbabilityTheory.exists_modification_holder_iSup`.  It returns one
measurable modification whose paths satisfy every local Hoelder exponent below the supremum
allowed by the supplied moment bounds and covering dimension.
-/

@[expose] public section
