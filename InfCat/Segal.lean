/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.WeakEquiv
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Segal Spaces — Segal maps, ambient fibrancy proxies, and fiberwise mapping spaces

A **Segal space** is a simplicial object `X : SimplicialObject SSet` (i.e., a bisimplicial
set / simplicial space) satisfying:

1. **Levelwise Kan condition**: each `X _⦋n⦌` is a Kan complex.
2. **Segal condition**: for each `n ≥ 2`, the Segal map from `X _⦋n⦌` to the
   iterated pullback `X _⦋1⦌ ×_{X _⦋0⦌} ⋯ ×_{X _⦋0⦌} X _⦋1⦌` is a weak
   homotopy equivalence.

The Segal condition for general `n` follows from the `n = 2` case by induction,
since pullbacks compose. We therefore define the Segal condition using only `n = 2`.

## Main definitions

- `SSet.IsOuterReedyFibrant`: the explicit outer-face fibrancy proxy used for simplicial
  spaces in this repository.
- `SSet.homSpace`: the fiberwise mapping space between two objects of a simplicial space.
- `SSet.homSpaceMap`: functoriality of fiberwise mapping spaces under maps of simplicial
  spaces.
- `SSet.segalMap₂`: the Segal map `X _⦋2⦌ ⟶ X _⦋1⦌ ×_{X _⦋0⦌} X _⦋1⦌`.
- `SSet.IsSegalSpace`: the class of Segal spaces.

## Main statements

- `SSet.homSpaceMap_identityEdgeInHomSpace`: `homSpaceMap` preserves identity edges.

## References

* [C. Rezk, *A model for the homotopy theory of homotopy theory*, §4]
* [Kerodon, §2.1](https://kerodon.net/) — Segal conditions
-/

universe u

open CategoryTheory CategoryTheory.Limits Simplicial SimplexCategory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet

variable (X : SimplicialObject SSet.{u})

/-- Explicit outer-face fibrancy proxy for simplicial objects in simplicial sets.

The repository does not currently implement the full Reedy model structure, so we record
the currently available non-vacuous proxy: the two outer face maps in every simplicial
degree are fibrations of simplicial sets. This keeps the extra hypothesis explicit without
pretending that the full Reedy matching-map condition has already been formalized. -/
class IsOuterReedyFibrant (X : SimplicialObject SSet.{u}) : Prop where
  /-- The `d₀` face map is a fibration in every simplicial degree. -/
  left_face_fibration : ∀ n : ℕ, Fibration (X.δ (0 : Fin (n + 2)))
  /-- The `d_last` face map is a fibration in every simplicial degree. -/
  right_face_fibration : ∀ n : ℕ, Fibration (X.δ (Fin.last (n + 1)))

/-- The mapping space from `x` to `y`, encoded as the simplicial subset of `X _⦋1⦌`
whose source and target vertices are constantly `x` and `y`. -/
noncomputable def homSpace (x y : (X _⦋0⦌).obj (op ⦋0⦌)) : SSet.{u} :=
  (Subfunctor.mk
    (F := X _⦋1⦌)
    (fun (U : SimplexCategoryᵒᵖ) =>
      { σ : (X _⦋1⦌).obj U |
        ∀ (v : Fin (U.unop.len + 1)),
          ((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
              ((X.δ (1 : Fin 2)).app U σ) = x ∧
            ((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
              ((X.δ (0 : Fin 2)).app U σ) = y })
    (fun {U V} f σ hσ v => by
      constructor
      · have hδ₁ :
            ((X _⦋0⦌).map f) ((X.δ (1 : Fin 2)).app U σ) =
              (X.δ (1 : Fin 2)).app V (((X _⦋1⦌).map f) σ) := by
          simpa using (congr_fun ((X.δ (1 : Fin 2)).naturality f) σ).symm
        rw [← hδ₁]
        rw [← CategoryTheory.FunctorToTypes.map_comp_apply]
        have hcomp :
            f ≫ (SimplexCategory.const ⦋0⦌ V.unop v).op =
              (SimplexCategory.const ⦋0⦌ U.unop (f.unop.toOrderHom v)).op := by
          exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ f.unop v)
        rw [hcomp]
        exact (hσ (f.unop.toOrderHom v)).1
      · have hδ₀ :
            ((X _⦋0⦌).map f) ((X.δ (0 : Fin 2)).app U σ) =
              (X.δ (0 : Fin 2)).app V (((X _⦋1⦌).map f) σ) := by
          simpa using (congr_fun ((X.δ (0 : Fin 2)).naturality f) σ).symm
        rw [← hδ₀]
        rw [← CategoryTheory.FunctorToTypes.map_comp_apply]
        have hcomp :
            f ≫ (SimplexCategory.const ⦋0⦌ V.unop v).op =
              (SimplexCategory.const ⦋0⦌ U.unop (f.unop.toOrderHom v)).op := by
          exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ f.unop v)
        rw [hcomp]
        exact (hσ (f.unop.toOrderHom v)).2)).toFunctor

/-- The identity edge of `x`, viewed in the fiberwise endomorphism space of `x`. -/
noncomputable def identityEdgeInHomSpace
    (x : (X _⦋0⦌).obj (op ⦋0⦌)) : (homSpace X x x).obj (op ⦋0⦌) := by
  refine ⟨(X.σ (0 : Fin 1)).app (op ⦋0⦌) x, ?_⟩
  intro v
  fin_cases v
  constructor
  · simpa using congr_fun
      (congrArg (fun α => α.app (op ⦋0⦌)) (X.δ_comp_σ_succ (i := (0 : Fin 1)))) x
  · simpa using congr_fun
      (congrArg (fun α => α.app (op ⦋0⦌)) (X.δ_comp_σ_self (i := (0 : Fin 1)))) x

/-- A morphism of simplicial spaces restricts to the fiberwise mapping spaces. -/
noncomputable def homSpaceMap {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    (x y : (X _⦋0⦌).obj (op ⦋0⦌)) :
    homSpace X x y ⟶
      homSpace Y ((g.app (op ⦋0⦌)).app (op ⦋0⦌) x) ((g.app (op ⦋0⦌)).app (op ⦋0⦌) y) where
  app := by
    intro U σ
    refine ⟨(g.app (op ⦋1⦌)).app U σ.1, ?_⟩
    intro v
    constructor
    · have hδ₁ :
          (g.app (op ⦋0⦌)).app U ((X.δ (1 : Fin 2)).app U σ.1) =
            (Y.δ (1 : Fin 2)).app U ((g.app (op ⦋1⦌)).app U σ.1) := by
        exact congr_fun
          (congrArg (fun α => α.app U) (SimplicialObject.δ_naturality g (1 : Fin 2))) σ.1
      calc
        ((Y _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
            ((Y.δ (1 : Fin 2)).app U ((g.app (op ⦋1⦌)).app U σ.1))
            =
              ((Y _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
                ((g.app (op ⦋0⦌)).app U ((X.δ (1 : Fin 2)).app U σ.1)) := by rw [← hδ₁]
        _ =
            (g.app (op ⦋0⦌)).app (op ⦋0⦌)
              (((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
                ((X.δ (1 : Fin 2)).app U σ.1)) := by
              simpa using (congr_fun
                ((g.app (op ⦋0⦌)).naturality ((SimplexCategory.const ⦋0⦌ U.unop v).op))
                ((X.δ (1 : Fin 2)).app U σ.1)).symm
        _ = (g.app (op ⦋0⦌)).app (op ⦋0⦌) x := by rw [(σ.2 v).1]
    · have hδ₀ :
          (g.app (op ⦋0⦌)).app U ((X.δ (0 : Fin 2)).app U σ.1) =
            (Y.δ (0 : Fin 2)).app U ((g.app (op ⦋1⦌)).app U σ.1) := by
        exact congr_fun
          (congrArg (fun α => α.app U) (SimplicialObject.δ_naturality g (0 : Fin 2))) σ.1
      calc
        ((Y _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
            ((Y.δ (0 : Fin 2)).app U ((g.app (op ⦋1⦌)).app U σ.1))
            =
              ((Y _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
                ((g.app (op ⦋0⦌)).app U ((X.δ (0 : Fin 2)).app U σ.1)) := by rw [← hδ₀]
        _ =
            (g.app (op ⦋0⦌)).app (op ⦋0⦌)
              (((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
                ((X.δ (0 : Fin 2)).app U σ.1)) := by
              simpa using (congr_fun
                ((g.app (op ⦋0⦌)).naturality ((SimplexCategory.const ⦋0⦌ U.unop v).op))
                ((X.δ (0 : Fin 2)).app U σ.1)).symm
        _ = (g.app (op ⦋0⦌)).app (op ⦋0⦌) y := by rw [(σ.2 v).2]
  naturality := by
    intro U V f
    ext σ
    apply Subtype.ext
    simpa using congr_fun ((g.app (op ⦋1⦌)).naturality f) σ.1

@[simp]
lemma homSpaceMap_identityEdgeInHomSpace {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    (x : (X _⦋0⦌).obj (op ⦋0⦌)) :
    (homSpaceMap X g x x).app (op ⦋0⦌) (identityEdgeInHomSpace X x) =
      identityEdgeInHomSpace Y ((g.app (op ⦋0⦌)).app (op ⦋0⦌) x) := by
  apply Subtype.ext
  change
    (g.app (op ⦋1⦌)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x) =
      (Y.σ (0 : Fin 1)).app (op ⦋0⦌) ((g.app (op ⦋0⦌)).app (op ⦋0⦌) x)
  exact congr_fun
    (congrArg (fun α => α.app (op ⦋0⦌))
      (SimplicialObject.σ_naturality (X := X) (X' := Y) g (0 : Fin 1))) x

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
