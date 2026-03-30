/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.Segal

/-!
# Complete Segal Spaces — equivalence morphisms, auxiliary equivalence spaces, completeness

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

- `SSet.isEquivMorphism`: predicate for a 0-simplex of `X _⦋1⦌` to be an equivalence.
- `SSet.equivSpace`: the auxiliary simplicial subset of `X _⦋1⦌` cut out by
  vertexwise equivalence data.
- `SSet.equivSpaceMap`: functoriality of `equivSpace` under maps of simplicial spaces.
- `SSet.completenessMap`: the map from objects to this auxiliary equivalence space.
- `SSet.IsCSS`: the complete-Segal-space predicate.
- `SSet.IsPresentedCSS`: the repository's current presented CSS notion, pairing
  `IsCSS` with the explicit outer fibrancy proxy.

## Main statements

- `SSet.isEquivMorphism_degenerate_edge`: identity morphisms are equivalences.
- `SSet.equivSpaceMap_comp`: `equivSpaceMap` is functorial under composition.
- `SSet.completenessMap_natural`: the completeness map is natural in the simplicial space.

## References

- [C. Rezk, *A model for the homotopy theory of homotopy theory*, §6]
-/

universe u

open CategoryTheory Simplicial SimplexCategory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet

variable (X : SimplicialObject SSet.{u})

/-- Fiberwise left inverse data for a 1-simplex `f`. -/
def LeftFiberwiseInverseData (f : (X _⦋1⦌).obj (op ⦋0⦌)) : Prop :=
  ∃ (σ : (X _⦋2⦌).obj (op ⦋0⦌)) (γ :
      (homSpace X ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)
        ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)).obj (op ⦋0⦌)),
    (X.δ (2 : Fin 3)).app (op ⦋0⦌) σ = f ∧
      γ.1 = (X.δ (1 : Fin 3)).app (op ⦋0⦌) σ ∧
      π₀.mk γ =
        π₀.mk
          (identityEdgeInHomSpace X ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))

/-- Fiberwise right inverse data for a 1-simplex `f`. -/
def RightFiberwiseInverseData (f : (X _⦋1⦌).obj (op ⦋0⦌)) : Prop :=
  ∃ (τ : (X _⦋2⦌).obj (op ⦋0⦌)) (γ :
      (homSpace X ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)
        ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)).obj (op ⦋0⦌)),
    (X.δ (0 : Fin 3)).app (op ⦋0⦌) τ = f ∧
      γ.1 = (X.δ (1 : Fin 3)).app (op ⦋0⦌) τ ∧
      π₀.mk γ =
        π₀.mk
          (identityEdgeInHomSpace X ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))

/-- A 0-simplex `f` of `X _⦋1⦌` (a morphism in the Segal space) is an **equivalence
morphism** if it admits both a left and a right homotopy inverse inside the appropriate
fiberwise mapping spaces.

**Left inverse**: There exists a 2-simplex `σ` with `d₂(σ) = f` (first edge), and the
composite `d₁(σ)` (which represents `g ∘ f` for `g = d₀(σ)`) determines a point of the
endomorphism mapping space of `source(f)` that is connected to the identity there.

**Right inverse**: There exists a 2-simplex `τ` with `d₀(τ) = f` (second edge), and the
composite `d₁(τ)` (which represents `f ∘ g'` for `g' = d₂(τ)`) determines a point of the
endomorphism mapping space of `target(f)` that is connected to the identity there. -/
def isEquivMorphism (f : (X _⦋1⦌).obj (op ⦋0⦌)) : Prop :=
  LeftFiberwiseInverseData X f ∧ RightFiberwiseInverseData X f

/-- The auxiliary vertexwise equivalence subspace of a simplicial space `X`.

This is the sub-simplicial-set of `X _⦋1⦌` consisting of simplices all of whose vertices
(obtained via the vertex maps `const [0] [n] v`) are equivalence morphisms.

An `n`-simplex `σ` of `X _⦋1⦌` belongs to `equivSpace X` iff for every vertex
`v : Fin (n+1)`, the 0-simplex obtained by pulling back along the constant map at `v`
satisfies `isEquivMorphism`.

For genuine Segal-space-style fibrant objects, this is intended to model the usual
equivalence space; without those extra hypotheses, it should be read as the auxiliary
subobject singled out by the vertexwise predicate above. -/
noncomputable def equivSpace : SSet.{u} :=
  (Subfunctor.mk
    (F := X _⦋1⦌)
    (fun (U : SimplexCategoryᵒᵖ) =>
      { σ : (X _⦋1⦌).obj U |
        ∀ (v : Fin (U.unop.len + 1)),
          isEquivMorphism X
            ((X _⦋1⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op σ) })
    (fun {U V} f σ hσ v => by
      rw [← CategoryTheory.FunctorToTypes.map_comp_apply]
      have hcomp :
          f ≫ (SimplexCategory.const ⦋0⦌ V.unop v).op =
            (SimplexCategory.const ⦋0⦌ U.unop (f.unop.toOrderHom v)).op := by
        exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ f.unop v)
      rw [hcomp]
      exact hσ (f.unop.toOrderHom v))).toFunctor

/-- The degenerate edge `s₀(x)` admits a left homotopy inverse. -/
lemma degenerate_edge_has_left_homotopy_inverse
    (x : (X _⦋0⦌).obj (op ⦋0⦌)) :
    LeftFiberwiseInverseData X ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x) := by
  refine ⟨(X.σ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x),
    identityEdgeInHomSpace X ((X.δ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)),
    ?_, ?_, rfl⟩
  · calc
      (X.δ (2 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) := by
            exact congrArg
              (fun t => t.app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
              (X.δ_comp_σ_of_gt' (i := (2 : Fin 3)) (j := (0 : Fin 2)) (by decide))
      _ = (X.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
        exact congrArg
          (fun t => (X.σ (0 : Fin 1)).app (op ⦋0⦌) t)
          (congrArg (fun α => α.app (op ⦋0⦌) x) (X.δ_comp_σ_succ (i := (0 : Fin 1))))
  · change
      (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.δ (1 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
    calc
      (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
          exact congrArg
            (fun t => (X.σ (0 : Fin 1)).app (op ⦋0⦌) t)
            (congrArg (fun α => α.app (op ⦋0⦌) x)
              (CategoryTheory.SimplicialObject.δ_comp_σ_succ (X := X) (i := (0 : Fin 1))))
      _ =
        (X.δ (1 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) := by
            exact
              (congrArg
                (fun α => α.app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
                (CategoryTheory.SimplicialObject.δ_comp_σ_succ (X := X) (i := (0 : Fin 2)))).symm

/-- The degenerate edge `s₀(x)` admits a right homotopy inverse. -/
lemma degenerate_edge_has_right_homotopy_inverse
    (x : (X _⦋0⦌).obj (op ⦋0⦌)) :
    RightFiberwiseInverseData X ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x) := by
  refine ⟨(X.σ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x),
    identityEdgeInHomSpace X ((X.δ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)),
    ?_, ?_, rfl⟩
  · calc
      (X.δ (0 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) := by
            exact congrArg
              (fun t => t.app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
              (X.δ_comp_σ_of_le (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide))
      _ = (X.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
        exact congrArg
          (fun t => (X.σ (0 : Fin 1)).app (op ⦋0⦌) t)
          (congrArg (fun α => α.app (op ⦋0⦌) x) (X.δ_comp_σ_self (i := (0 : Fin 1))))
  · change
      (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.δ (1 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
    calc
      (X.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((X.δ (0 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) =
        (X.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
          exact congrArg
            (fun t => (X.σ (0 : Fin 1)).app (op ⦋0⦌) t)
            (congrArg (fun α => α.app (op ⦋0⦌) x)
              (CategoryTheory.SimplicialObject.δ_comp_σ_self (X := X) (i := (0 : Fin 1))))
      _ =
        (X.δ (1 : Fin 3)).app (op ⦋0⦌)
          ((X.σ (1 : Fin 2)).app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x)) := by
            exact
              (congrArg
                (fun α => α.app (op ⦋0⦌) ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x))
                (CategoryTheory.SimplicialObject.δ_comp_σ_self (X := X) (i := (1 : Fin 2)))).symm

/-- Every degenerate edge `s₀(x)` is an equivalence morphism. -/
lemma isEquivMorphism_degenerate_edge
    (x : (X _⦋0⦌).obj (op ⦋0⦌)) :
    isEquivMorphism X ((X.σ (0 : Fin 1)).app (op ⦋0⦌) x) := by
  exact ⟨degenerate_edge_has_left_homotopy_inverse X x,
    degenerate_edge_has_right_homotopy_inverse X x⟩

/-- A morphism of simplicial spaces preserves the source vertex of an edge. -/
lemma map_edge_source {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    (f : (X _⦋1⦌).obj (op ⦋0⦌)) :
    (g.app (op ⦋0⦌)).app (op ⦋0⦌) ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f) =
      (Y.δ (1 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f) := by
  exact congrArg (fun α => α.app (op ⦋0⦌) f) (SimplicialObject.δ_naturality g (1 : Fin 2))

/-- A morphism of simplicial spaces preserves the target vertex of an edge. -/
lemma map_edge_target {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    (f : (X _⦋1⦌).obj (op ⦋0⦌)) :
    (g.app (op ⦋0⦌)).app (op ⦋0⦌) ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f) =
      (Y.δ (0 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f) := by
  exact congrArg (fun α => α.app (op ⦋0⦌) f) (SimplicialObject.δ_naturality g (0 : Fin 2))

/-- A morphism of simplicial spaces carries fiberwise left inverse data to the target. -/
lemma map_left_homotopy_inverse {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    {f : (X _⦋1⦌).obj (op ⦋0⦌)}
    (hf : LeftFiberwiseInverseData X f) :
    LeftFiberwiseInverseData Y ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f) := by
  rcases hf with ⟨σ, γ, hσ, hγ, hπ⟩
  have hδ₁f := map_edge_source (X := X) g f
  change ∃ (σ' : (Y _⦋2⦌).obj (op ⦋0⦌))
      (γ' : (homSpace Y ((Y.δ (1 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f))
        ((Y.δ (1 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f))).obj (op ⦋0⦌)),
      (Y.δ (2 : Fin 3)).app (op ⦋0⦌) σ' = (g.app (op ⦋1⦌)).app (op ⦋0⦌) f ∧
        γ'.1 = (Y.δ (1 : Fin 3)).app (op ⦋0⦌) σ' ∧
          π₀.mk γ' =
            π₀.mk
              (identityEdgeInHomSpace Y
                ((Y.δ (1 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f)))
  rw [← hδ₁f]
  refine ⟨(g.app (op ⦋2⦌)).app (op ⦋0⦌) σ,
    (homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)).app
      (op ⦋0⦌) γ,
    ?_, ?_, ?_⟩
  · calc
      (Y.δ (2 : Fin 3)).app (op ⦋0⦌) ((g.app (op ⦋2⦌)).app (op ⦋0⦌) σ) =
        (g.app (op ⦋1⦌)).app (op ⦋0⦌) ((X.δ (2 : Fin 3)).app (op ⦋0⦌) σ) := by
          exact
            (congrArg (fun α => α.app (op ⦋0⦌) σ)
              (SimplicialObject.δ_naturality g (2 : Fin 3))).symm
      _ = (g.app (op ⦋1⦌)).app (op ⦋0⦌) f := by rw [hσ]
  · calc
      ((homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)
          ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌) γ).1 =
        (g.app (op ⦋1⦌)).app (op ⦋0⦌) γ.1 := by
          rfl
      _ = (g.app (op ⦋1⦌)).app (op ⦋0⦌) ((X.δ (1 : Fin 3)).app (op ⦋0⦌) σ) := by rw [hγ]
      _ = (Y.δ (1 : Fin 3)).app (op ⦋0⦌) ((g.app (op ⦋2⦌)).app (op ⦋0⦌) σ) := by
          exact
            congr_fun
              (congrArg (fun α => α.app (op ⦋0⦌))
                (SimplicialObject.δ_naturality g (1 : Fin 3))) σ
  · calc
      π₀.mk
          ((homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)
              ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌) γ) =
        SSet.π₀Map
          (homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))
          (π₀.mk γ) := by
            rfl
      _ =
        SSet.π₀Map
          (homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))
          (π₀.mk (identityEdgeInHomSpace X ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))) := by
            exact congrArg
              (SSet.π₀Map
                (homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (1 : Fin 2)).app
                  (op ⦋0⦌) f))) hπ
      _ = π₀.mk
          ((homSpaceMap X g ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)
              ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌)
            (identityEdgeInHomSpace X ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))) := by
              rfl
      _ = π₀.mk
          (identityEdgeInHomSpace Y
            ((g.app (op ⦋0⦌)).app (op ⦋0⦌) ((X.δ (1 : Fin 2)).app (op ⦋0⦌) f))) := by
          rw [SSet.homSpaceMap_identityEdgeInHomSpace]

/-- A morphism of simplicial spaces carries fiberwise right inverse data to the target. -/
lemma map_right_homotopy_inverse {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    {f : (X _⦋1⦌).obj (op ⦋0⦌)}
    (hf : RightFiberwiseInverseData X f) :
    RightFiberwiseInverseData Y ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f) := by
  rcases hf with ⟨τ, γ, hτ, hγ, hπ⟩
  have hδ₀f := map_edge_target (X := X) g f
  change ∃ (τ' : (Y _⦋2⦌).obj (op ⦋0⦌))
      (γ' : (homSpace Y ((Y.δ (0 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f))
        ((Y.δ (0 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f))).obj (op ⦋0⦌)),
      (Y.δ (0 : Fin 3)).app (op ⦋0⦌) τ' = (g.app (op ⦋1⦌)).app (op ⦋0⦌) f ∧
        γ'.1 = (Y.δ (1 : Fin 3)).app (op ⦋0⦌) τ' ∧
          π₀.mk γ' =
            π₀.mk
              (identityEdgeInHomSpace Y
                ((Y.δ (0 : Fin 2)).app (op ⦋0⦌) ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f)))
  rw [← hδ₀f]
  refine ⟨(g.app (op ⦋2⦌)).app (op ⦋0⦌) τ,
    (homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)).app
      (op ⦋0⦌) γ,
    ?_, ?_, ?_⟩
  · calc
      (Y.δ (0 : Fin 3)).app (op ⦋0⦌) ((g.app (op ⦋2⦌)).app (op ⦋0⦌) τ) =
        (g.app (op ⦋1⦌)).app (op ⦋0⦌) ((X.δ (0 : Fin 3)).app (op ⦋0⦌) τ) := by
          exact
            (congrArg (fun α => α.app (op ⦋0⦌) τ)
              (SimplicialObject.δ_naturality g (0 : Fin 3))).symm
      _ = (g.app (op ⦋1⦌)).app (op ⦋0⦌) f := by rw [hτ]
  · calc
      ((homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)
          ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌) γ).1 =
        (g.app (op ⦋1⦌)).app (op ⦋0⦌) γ.1 := by
          rfl
      _ = (g.app (op ⦋1⦌)).app (op ⦋0⦌) ((X.δ (1 : Fin 3)).app (op ⦋0⦌) τ) := by rw [hγ]
      _ = (Y.δ (1 : Fin 3)).app (op ⦋0⦌) ((g.app (op ⦋2⦌)).app (op ⦋0⦌) τ) := by
          exact
            congr_fun
              (congrArg (fun α => α.app (op ⦋0⦌))
                (SimplicialObject.δ_naturality g (1 : Fin 3))) τ
  · calc
      π₀.mk
          ((homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)
              ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌) γ) =
        SSet.π₀Map
          (homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))
          (π₀.mk γ) := by
            rfl
      _ =
        SSet.π₀Map
          (homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))
          (π₀.mk (identityEdgeInHomSpace X ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))) := by
            exact congrArg
              (SSet.π₀Map
                (homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f) ((X.δ (0 : Fin 2)).app
                  (op ⦋0⦌) f))) hπ
      _ = π₀.mk
          ((homSpaceMap X g ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)
              ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f)).app (op ⦋0⦌)
            (identityEdgeInHomSpace X ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))) := by
              rfl
      _ = π₀.mk
          (identityEdgeInHomSpace Y
            ((g.app (op ⦋0⦌)).app (op ⦋0⦌) ((X.δ (0 : Fin 2)).app (op ⦋0⦌) f))) := by
          rw [SSet.homSpaceMap_identityEdgeInHomSpace]

/-- A morphism of simplicial spaces preserves equivalence morphisms. -/
lemma isEquivMorphism_map {Y : SimplicialObject SSet.{u}} (g : X ⟶ Y)
    {f : (X _⦋1⦌).obj (op ⦋0⦌)} (hf : isEquivMorphism X f) :
    isEquivMorphism Y ((g.app (op ⦋1⦌)).app (op ⦋0⦌) f) := by
  exact ⟨map_left_homotopy_inverse (X := X) g hf.1,
    map_right_homotopy_inverse (X := X) g hf.2⟩

/-- Evaluating the degree-1 component of a simplicial morphism at a vertex
commutes with the induced map on 0-simplices. -/
lemma equivSpaceMap_vertex_naturality {Y₁ Y₂ : SimplicialObject SSet.{u}}
    (g : Y₁ ⟶ Y₂) (U : SimplexCategoryᵒᵖ) (σ : (Y₁ _⦋1⦌).obj U)
    (v : Fin (U.unop.len + 1)) :
    ((Y₂ _⦋1⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
        ((g.app (op ⦋1⦌)).app U σ) =
      (g.app (op ⦋1⦌)).app (op ⦋0⦌)
        (((Y₁ _⦋1⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op) σ) := by
  simpa using (congr_fun
    ((g.app (op ⦋1⦌)).naturality ((SimplexCategory.const ⦋0⦌ U.unop v).op)) σ).symm

/-- The functorial action of `equivSpace` on morphisms of simplicial spaces.
A morphism `g : Y₁ ⟶ Y₂` preserves equivalence morphisms, so the induced map
on `Y₁ _⦋1⦌` restricts to a map on equivalence spaces. -/
noncomputable abbrev equivSpaceMap {Y₁ Y₂ : SimplicialObject SSet.{u}}
    (g : Y₁ ⟶ Y₂) : equivSpace Y₁ ⟶ equivSpace Y₂ where
  app := by
    intro U σ
    refine ⟨(g.app (op ⦋1⦌)).app U σ.1, ?_⟩
    intro v
    rw [equivSpaceMap_vertex_naturality g U σ.1 v]
    exact SSet.isEquivMorphism_map (X := Y₁) g (σ.2 v)
  naturality := by
    intro U V f
    ext σ
    apply Subtype.ext
    simpa using congr_fun ((g.app (op ⦋1⦌)).naturality f) σ.1

@[simp]
lemma equivSpaceMap_id (Y : SimplicialObject SSet.{u}) :
    equivSpaceMap (𝟙 Y) = 𝟙 (equivSpace Y) := by
  ext U σ
  rfl

@[simp]
lemma equivSpaceMap_comp {Y₁ Y₂ Y₃ : SimplicialObject SSet.{u}}
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    equivSpaceMap (g₁ ≫ g₂) = equivSpaceMap g₁ ≫ equivSpaceMap g₂ := by
  ext U σ
  rfl

/-- Restricting a degenerate edge to a vertex gives the degenerate edge of the
corresponding restricted object. -/
lemma degenerate_edge_vertex {U : SimplexCategoryᵒᵖ}
    (a : (X _⦋0⦌).obj U) (v : Fin (U.unop.len + 1)) :
    ((X _⦋1⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op)
        ((X.σ (0 : Fin 1)).app U a) =
      (X.σ (0 : Fin 1)).app (op ⦋0⦌)
        (((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op) a) := by
  simpa using (congr_fun
    ((X.σ (0 : Fin 1)).naturality ((SimplexCategory.const ⦋0⦌ U.unop v).op)) a).symm

/-- The **completeness map** sends an object (a simplex of `X _⦋0⦌`) to its identity
morphism (a degenerate simplex of `X _⦋1⦌`), viewed as an element of the auxiliary
vertexwise equivalence subspace.

This is the degeneracy `s₀ : X _⦋0⦌ ⟶ X _⦋1⦌` lifted through the inclusion
`equivSpace X ↪ X _⦋1⦌`, using the fact that identity morphisms satisfy the fiberwise
equivalence predicate. -/
noncomputable abbrev completenessMap : X _⦋0⦌ ⟶ equivSpace X where
  app := by
    intro U a
    refine ⟨(X.σ (0 : Fin 1)).app U a, ?_⟩
    intro v
    rw [degenerate_edge_vertex X a v]
    exact isEquivMorphism_degenerate_edge X
      (((X _⦋0⦌).map (SimplexCategory.const ⦋0⦌ U.unop v).op) a)
  naturality := by
    intro U V f
    ext a
    apply Subtype.ext
    simpa using congr_fun ((X.σ (0 : Fin 1)).naturality f) a

lemma completenessMap_natural {Y₁ Y₂ : SimplicialObject SSet.{u}} (g : Y₁ ⟶ Y₂) :
    g.app (op ⦋0⦌) ≫ completenessMap Y₂ = completenessMap Y₁ ≫ equivSpaceMap g := by
  ext U a
  apply Subtype.ext
  exact (congr_fun
    (congrArg (fun α => α.app U) (SimplicialObject.σ_naturality g (0 : Fin 1))) a).symm

/-- The complete-Segal-space predicate.

It consists of:
* a Segal-space structure,
* completeness of the auxiliary map `completenessMap`.

The repository's current outer-face fibrancy proxy remains available separately as
`IsOuterReedyFibrant`; it is not baked into the headline notion `IsCSS`. -/
class IsCSS : Prop extends IsSegalSpace X where
  /-- The completeness map is a weak homotopy equivalence. -/
  complete : IsWeakHomotopyEquiv (completenessMap X)

/-- The repository's current complete-Segal-space package: `IsCSS` together with the
explicit outer-face fibrancy proxy used as ambient infrastructure in this development. -/
def IsPresentedCSS : Prop :=
  IsOuterReedyFibrant X ∧ IsCSS X

end SSet
