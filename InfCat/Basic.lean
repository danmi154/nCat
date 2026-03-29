/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.General
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Infinity n-Categories via Iterated Complete Segal Spaces

We define (∞,n)-categories as **n-fold complete Segal spaces**, following the
framework of Barwick-Schommer-Pries and building on Rezk's complete Segal spaces.

The definition is inductive:
* **(∞,0)-Cat** = Kan complexes (∞-groupoids / spaces)
* **(∞,1)-Cat** = complete Segal spaces
* **(∞,n+1)-Cat** = complete Segal objects in (∞,n)-Cat

At each level, the ambient category is that of **iterated simplicial objects**:
* Level 0: `SSet` = `SimplexCategoryᵒᵖ ⥤ Type u`
* Level 1: `SimplicialObject SSet` (bisimplicial sets)
* Level 2: `SimplicialObject (SimplicialObject SSet)` (trisimplicial sets)

## Main definitions

* `SSet.IsInfCat₀` : (∞,0)-categories = Kan complexes
* `SSet.IsInfCat₁` : (∞,1)-categories = complete Segal spaces
* `SSet.IsInfCat₂` : (∞,2)-categories = complete Segal objects in CSS

## Equivalence with quasicategories

For n = 1, complete Segal spaces are equivalent to quasicategories via a chain
of Quillen equivalences (Joyal-Tierney, Bergner). Thus `IsCSS X` and
`Quasicategory S` describe the same mathematical objects up to equivalence,
but CSS generalize inductively to all n.

## References

* [C. Barwick, C. Schommer-Pries, *On the unicity of the theory of higher categories*]
* [C. Rezk, *A model for the homotopy theory of homotopy theory*]
* [Kerodon, *An online resource for homotopy-coherent mathematics*](https://kerodon.net/)
-/

universe u

open CategoryTheory Simplicial

namespace SSet

/-! ### (∞,0)-categories = Kan complexes -/

/-- An **(∞,0)-category** is a Kan complex: a simplicial set in which every horn
can be filled. These model ∞-groupoids, or spaces up to homotopy.

Every higher morphism (at every level) is invertible. -/
abbrev IsInfCat₀ (X : SSet.{u}) : Prop := KanComplex X

/-! ### (∞,1)-categories = Complete Segal spaces -/

/-- An **(∞,1)-category** is a complete Segal space: a simplicial object in `SSet`
satisfying the Segal condition (composition is well-defined up to contractible choice)
and completeness (equivalent objects are equal up to homotopy).

These are equivalent to quasicategories (Joyal-Tierney). Morphisms at level ≥ 2
are invertible, but 1-morphisms need not be. -/
abbrev IsInfCat₁ (X : SimplicialObject SSet.{u}) : Prop := IsCSS X

/-! ### (∞,2)-categories = 2-fold Complete Segal spaces -/

/-- An **(∞,2)-category** is a complete Segal object in (∞,1)-categories.
Concretely, it is an object `X : NSimplicial 2` (a trisimplicial set) such that:

1. Each level `X _⦋n⦌` is a complete Segal space (i.e., an (∞,1)-category).
2. The Segal condition holds: the Segal map at the outer simplicial level
   is a levelwise weak equivalence of bisimplicial sets.
3. The completeness condition holds at the outer level.

2-morphisms need not be invertible, but morphisms at level ≥ 3 are. -/
class IsInfCat₂ (X : NSimplicial.{u} 2) : Prop where
  /-- Each simplicial level is an (∞,1)-category. -/
  levelwise : ∀ (k : ℕ), IsCSS (nLevel X k)
  /-- The outer-level Segal map is a 1-weak equivalence. -/
  segal : IsNWeakEquiv 1 (nSegalMap X)
  /-- The outer-level completeness map is a 1-weak equivalence. -/
  complete : IsNWeakEquiv 1 (nCompletenessMap X)

/-! ### The general pattern

The inductive definition for all `n` is given by `IsInfNCat` in `General.lean`.
The definitions above for n ≤ 2 are the concrete instances that use the
vocabulary specific to each level (Kan complexes, CSS, etc.). -/

end SSet
