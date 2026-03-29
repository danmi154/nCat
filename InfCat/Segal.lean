/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.WeakEquiv
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Segal Spaces

A **Segal space** is a simplicial object `X : SimplicialObject SSet` (i.e., a bisimplicial
set / simplicial space) satisfying:

1. **Levelwise Kan condition**: each `X _⦋n⦌` is a Kan complex.
2. **Segal condition**: for each `n ≥ 2`, the Segal map from `X _⦋n⦌` to the
   iterated pullback `X _⦋1⦌ ×_{X _⦋0⦌} ⋯ ×_{X _⦋0⦌} X _⦋1⦌` is a weak
   homotopy equivalence.

The Segal condition for general `n` follows from the `n = 2` case by induction,
since pullbacks compose. We therefore define the Segal condition using only `n = 2`.

## Main definitions

* `SSet.SegalSpace.segalMap₂` : The Segal map `X _⦋2⦌ ⟶ X _⦋1⦌ ×_{X _⦋0⦌} X _⦋1⦌`.
* `SSet.IsSegalSpace` : The class of Segal spaces.

## References

* [C. Rezk, *A model for the homotopy theory of homotopy theory*, §4]
* [Kerodon, §2.1](https://kerodon.net/) — Segal conditions
-/

universe u

open CategoryTheory CategoryTheory.Limits Simplicial SimplexCategory Opposite

namespace SSet

variable (X : SimplicialObject SSet.{u})

/-- The **Segal map** for a simplicial space `X` at level 2.

This sends a 2-simplex `σ` to the pair of edges `(d₂(σ), d₀(σ))`, which lands
in the pullback `X _⦋1⦌ ×_{X _⦋0⦌} X _⦋1⦌` because the simplicial identity
`d₂ ≫ d₀ = d₀ ≫ d₁` ensures that the target of the first edge equals
the source of the second edge.

The Segal condition asks that this map is a weak homotopy equivalence. -/
noncomputable def segalMap₂ :
    X _⦋2⦌ ⟶ pullback (X.δ (0 : Fin 2) : X _⦋1⦌ ⟶ X _⦋0⦌) (X.δ 1) :=
  pullback.lift (X.δ 2) (X.δ 0)
    (X.δ_comp_δ (show (0 : Fin 2) ≤ 1 from Fin.zero_le _))

/-- A simplicial space `X : SimplicialObject SSet` is a **Segal space** if:
1. Each level `X _⦋n⦌` is a Kan complex (levelwise fibrancy).
2. The Segal map at level 2 is a weak homotopy equivalence.

The Segal condition ensures that composition of morphisms is well-defined
up to contractible choice: a 2-simplex is determined (up to homotopy) by
its boundary edges when they are composable. -/
class IsSegalSpace : Prop where
  /-- Each level of the simplicial space is a Kan complex. -/
  levelwise_kan : ∀ (n : ℕ), KanComplex (X _⦋n⦌)
  /-- The Segal map is a weak homotopy equivalence. -/
  segal : IsWeakHomotopyEquiv (segalMap₂ X)

attribute [instance] IsSegalSpace.levelwise_kan

end SSet
