/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Weak Homotopy Equivalences of Simplicial Sets

We define the connected components functor π₀ on simplicial sets and
weak homotopy equivalences.

A morphism `f : X ⟶ Y` of simplicial sets is a **weak homotopy equivalence** if
for every Kan complex `K`, the induced map `π₀(Map(Y, K)) → π₀(Map(X, K))` is a
bijection, where `Map(X, K) = (ihom X).obj K` is the internal hom (mapping space)
in the cartesian closed category `SSet`.

## Main definitions

* `SSet.EdgeRel` : The edge relation between 0-simplices.
* `SSet.π₀` : Connected components of a simplicial set.
* `SSet.π₀Map` : The map on π₀ induced by a morphism.
* `SSet.IsWeakHomotopyEquiv` : Weak homotopy equivalence predicate.

## Main results

* `SSet.π₀Map_comp_eq_id` : If `f ≫ g = 𝟙`, the induced `π₀` maps compose to `id`.
* `SSet.isWeakHomotopyEquiv_of_iso` : Isomorphisms are weak homotopy equivalences.

## References

* [Kerodon, tag 00PY](https://kerodon.net/tag/00PY) — Connected components
* [Goerss-Jardine, *Simplicial Homotopy Theory*, Chapter I]
-/

universe u

open CategoryTheory Simplicial SimplexCategory MonoidalCategory Opposite

namespace SSet

section Pi0

variable (X : SSet.{u})

/-- Two 0-simplices `x` and `y` of a simplicial set `X` are connected by an **edge**
if there exists a 1-simplex `σ` with `d₁(σ) = x` (source) and `d₀(σ) = y` (target). -/
def EdgeRel (x y : X _⦋0⦌) : Prop :=
  ∃ σ : X _⦋1⦌, X.δ 1 σ = x ∧ X.δ 0 σ = y

/-- The set of connected components `π₀(X)` of a simplicial set `X`,
defined as the quotient of 0-simplices by the equivalence relation generated
by edges. For Kan complexes, the edge relation is already an equivalence
relation, so `EqvGen` is unnecessary. -/
def π₀ : Type u := Quot X.EdgeRel

end Pi0

/-- A morphism of simplicial sets preserves the edge relation. -/
lemma EdgeRel.map {X Y : SSet.{u}} (f : X ⟶ Y) {x y : X _⦋0⦌} (h : X.EdgeRel x y) :
    Y.EdgeRel (f.app _ x) (f.app _ y) := by
  obtain ⟨σ, hx, hy⟩ := h
  exact ⟨f.app _ σ,
    by rw [← hx]; exact (FunctorToTypes.naturality X Y f (SimplexCategory.δ 1).op σ).symm,
    by rw [← hy]; exact (FunctorToTypes.naturality X Y f (SimplexCategory.δ 0).op σ).symm⟩

/-- The canonical projection from 0-simplices to π₀. -/
def π₀.mk {X : SSet.{u}} (x : X _⦋0⦌) : π₀ X :=
  Quot.mk _ x

/-- A morphism of simplicial sets induces a map on connected components. -/
def π₀Map {X Y : SSet.{u}} (f : X ⟶ Y) : π₀ X → π₀ Y :=
  Quot.map (f.app _) fun _ _ h => h.map f

@[simp]
lemma π₀Map_id (X : SSet.{u}) : π₀Map (𝟙 X) = id := by
  ext ⟨x⟩; rfl

lemma π₀Map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    π₀Map (f ≫ g) = π₀Map g ∘ π₀Map f := by
  ext ⟨x⟩; rfl

/-- A morphism `f : X ⟶ Y` of simplicial sets is a **weak homotopy equivalence** if
for every Kan complex `K`, precomposition with `f` induces a bijection on connected
components of the mapping space:
  `π₀(Map(Y, K)) ≃ π₀(Map(X, K))`

where `Map(X, K) = (ihom X).obj K` is the internal hom in `SSet`. -/
def IsWeakHomotopyEquiv {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (K : SSet.{u}) [KanComplex K],
    Function.Bijective (π₀Map ((MonoidalClosed.pre f).app K))

/-- Pre-composition with `g` then `f` on mapping spaces is the identity when `f ≫ g = 𝟙`. -/
lemma pre_app_comp_eq_id {X Y K : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : f ≫ g = 𝟙 _) :
    (MonoidalClosed.pre g).app K ≫ (MonoidalClosed.pre f).app K = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, h, MonoidalClosed.pre_id]; simp

/-- If a composition of morphisms is the identity, the induced `π₀` maps compose to `id`. -/
lemma π₀Map_comp_eq_id {X Y : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : f ≫ g = 𝟙 _) :
    π₀Map g ∘ π₀Map f = id := by
  rw [← π₀Map_comp, h, π₀Map_id]

/-- Isomorphisms are weak homotopy equivalences. -/
lemma isWeakHomotopyEquiv_of_iso {X Y : SSet.{u}} (e : X ≅ Y) :
    IsWeakHomotopyEquiv e.hom := by
  intro K _
  rw [Function.bijective_iff_has_inverse]
  refine ⟨π₀Map ((MonoidalClosed.pre e.inv).app K), ?_, ?_⟩
  · exact fun x => congr_fun (π₀Map_comp_eq_id (pre_app_comp_eq_id e.inv_hom_id)) x
  · exact fun x => congr_fun (π₀Map_comp_eq_id (pre_app_comp_eq_id e.hom_inv_id)) x

/-- Weak homotopy equivalences satisfy 2-out-of-3. -/
lemma IsWeakHomotopyEquiv.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsWeakHomotopyEquiv f) (hg : IsWeakHomotopyEquiv g) :
    IsWeakHomotopyEquiv (f ≫ g) := by
  intro K _
  simpa [MonoidalClosed.pre_map, π₀Map_comp] using
    Function.Bijective.comp (hf K) (hg K)

end SSet
