/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.Segal

/-!
# Complete Segal Spaces

A **complete Segal space** (CSS) is a Segal space `X` satisfying a completeness condition
that identifies the space of objects `X _⦋0⦌` with the space of equivalences in `X`.

Completeness prevents the "too many objects" problem: without it, a Segal space could
have distinct objects that are equivalent but not equal, violating the principle that
equivalent objects in an ∞-category should be indistinguishable.

## The completeness condition

For a Segal space `X`, the degeneracy map `s₀ : X _⦋0⦌ ⟶ X _⦋1⦌` sends each object
to its identity morphism. The **space of equivalences** `X₁ᵉᑫ` is the sub-simplicial-set
of `X _⦋1⦌` consisting of 1-simplices that are invertible in the homotopy category of `X`.

`X` is **complete** if `s₀ : X _⦋0⦌ ⟶ X₁ᵉᑫ` is a weak homotopy equivalence.

## Main definitions

* `SSet.isEquivMorphism` : Predicate for a 0-simplex of X₁ being an equivalence morphism.
* `SSet.equivSpace` : The space of equivalences (sub-simplicial-set of X₁).
* `SSet.completenessMap` : The map from X₀ to the space of equivalences.
* `SSet.IsCSS` : The class of complete Segal spaces.

## References

* [C. Rezk, *A model for the homotopy theory of homotopy theory*, §6]
-/

universe u

open CategoryTheory Simplicial SimplexCategory Opposite

namespace SSet

variable (X : SimplicialObject SSet.{u})

/-- A 0-simplex `f` of `X _⦋1⦌` (a morphism in the Segal space) is an **equivalence
morphism** if it admits both a left and a right homotopy inverse.

**Left inverse**: There exists a 2-simplex `σ` with `d₂(σ) = f` (first edge), and the
composite `d₁(σ)` (which represents `g ∘ f` for `g = d₀(σ)`) is connected to the
identity `s₀(source(f))` in `π₀(X _⦋1⦌)`.

**Right inverse**: There exists a 2-simplex `τ` with `d₀(τ) = f` (second edge), and the
composite `d₁(τ)` (which represents `f ∘ g'` for `g' = d₂(τ)`) is connected to the
identity `s₀(target(f))` in `π₀(X _⦋1⦌)`. -/
def isEquivMorphism (f : (X _⦋1⦌).obj (op ⦋0⦌)) : Prop :=
  (∃ (σ : (X _⦋2⦌).obj (op ⦋0⦌)),
    (X.δ (2 : Fin 3)).app (op ⦋0⦌) σ = f ∧
    π₀.mk ((X.δ (1 : Fin 3)).app (op ⦋0⦌) σ) =
      π₀.mk ((X.σ (0 : Fin 1)).app (op ⦋0⦌)
        ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))) ∧
  (∃ (τ : (X _⦋2⦌).obj (op ⦋0⦌)),
    (X.δ (0 : Fin 3)).app (op ⦋0⦌) τ = f ∧
    π₀.mk ((X.δ (1 : Fin 3)).app (op ⦋0⦌) τ) =
      π₀.mk ((X.σ (0 : Fin 1)).app (op ⦋0⦌)
        ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)))

/-- The **space of equivalences** of a simplicial space `X`.

This is the sub-simplicial-set of `X _⦋1⦌` consisting of simplices all of whose vertices
(obtained via the vertex maps `const [0] [n] v`) are equivalence morphisms.

An `n`-simplex `σ` of `X _⦋1⦌` belongs to `equivSpace X` iff for every vertex
`v : Fin (n+1)`, the 0-simplex obtained by pulling back along the constant map at `v`
satisfies `isEquivMorphism`. -/
noncomputable def equivSpace : SSet.{u} :=
  (Subfunctor.mk
    (F := X _⦋1⦌)
    (fun (U : SimplexCategoryᵒᵖ) =>
      { σ : (X _⦋1⦌).obj U |
        ∀ (v : Fin (U.unop.len + 1)),
          isEquivMorphism X
            ((X _⦋1⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op σ) })
    (fun {_U _V} _f => sorry)).toFunctor

/-- The **completeness map** sends an object (a simplex of `X _⦋0⦌`) to its identity
morphism (a degenerate simplex of `X _⦋1⦌`), viewed as an element of the space of
equivalences.

This is the degeneracy `s₀ : X _⦋0⦌ ⟶ X _⦋1⦌` lifted through the inclusion
`equivSpace X ↪ X _⦋1⦌`, using the fact that identity morphisms are equivalences. -/
noncomputable def completenessMap : X _⦋0⦌ ⟶ equivSpace X where
  app := fun U a => ⟨(X.σ (0 : Fin 1)).app U a, sorry⟩
  naturality := sorry

/-- A **complete Segal space** (CSS) is a Segal space satisfying the completeness condition:
the map from the space of objects to the space of equivalences is a weak homotopy
equivalence.

Complete Segal spaces model (∞,1)-categories in the Rezk model. They are equivalent
(via Quillen equivalences) to quasicategories, Segal categories, and simplicial categories
with Kan-enriched hom-spaces.

The key point is that CSS provide an inductive framework: an (∞,n+1)-category is
a complete Segal object in (∞,n)-categories. -/
class IsCSS : Prop extends IsSegalSpace X where
  /-- The completeness map is a weak homotopy equivalence. -/
  complete : IsWeakHomotopyEquiv (completenessMap X)

end SSet
