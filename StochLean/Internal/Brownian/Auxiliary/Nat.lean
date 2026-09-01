/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This implementation was adapted into StochLean from RemyDegenne/brownian-motion
at commit 314f04a34ff75e18fd383917ae7fe7d77beb1b6f (Apache-2.0).
The module path and dependency ownership were changed to StochLean.
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a




