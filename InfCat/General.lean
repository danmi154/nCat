/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.CSS

/-!
# General (∞,n)-Categories via Iterated Complete-Segal-Space Data

We define (∞,n)-categories for all `n` using n-fold complete Segal spaces.
The definition is inductive:
* **(∞,0)-Cat** = Kan complexes (spaces / ∞-groupoids)
* **(∞,n+1)-Cat** = complete Segal objects whose levels are (∞,n)-categories

## Main definitions

* `SSet.NSimplicial n` : The type of n-fold simplicial objects in `SSet`.
* `SSet.IsNWeakEquiv` : Levelwise weak equivalences of n-fold simplicial sets.
* `SSet.nSegalMap` : The generalized Segal map at each level.
* `SSet.nEquivSpace` : The recursive auxiliary equivalence-space object at each level.
* `SSet.nEquivSpaceMap` : Functorial action of `nEquivSpace` on morphisms.
* `SSet.nCompletenessMap` : The generalized completeness map at each level.
* `SSet.IsInfNCat` : the iterative `(∞,n)` predicate.
* `SSet.IsPresentedInfNCat` : the repository's current presented `(∞,n)` notion,
  pairing `IsInfNCat` with the explicit outer fibrancy proxy.

## Implementation notes

Since `SimplicialObject C` requires `[Category C]`, the type family `NSimplicial n`
and its category instance must be defined simultaneously. We bundle them into
`nSimplicialBundle` and project out.

The auxiliary equivalence-space construction is organized by the recursive functor
`nEquivSpaceFunctor : NSimplicial (n+1) ⥤ NSimplicial n`.
We then recover `nEquivSpace` and `nEquivSpaceMap` as its object and morphism maps.
This packages the recursion cleanly without requiring mutual definitions.

* At level 0, `nEquivSpace` is the auxiliary `equivSpace` from `CSS.lean`.
* At level `n+1`, it is defined pointwise via `innerEval`.

## References

* [C. Barwick, C. Schommer-Pries, *On the unicity of the theory of higher categories*]
* [C. Rezk, *A model for the homotopy theory of homotopy theory*]
-/

universe u

open CategoryTheory CategoryTheory.Limits Simplicial SimplexCategory Opposite

namespace SSet

/-! ### The type of n-fold simplicial sets -/

/-- Auxiliary bundle: the type of n-fold simplicial objects together with its
category structure, defined by recursion on `n`. -/
noncomputable def nSimplicialBundle : ℕ → Σ (C : Type (u + 1)), Category.{u} C
  | 0 => ⟨SSet.{u}, inferInstance⟩
  | n + 1 =>
    haveI : Category.{u} (nSimplicialBundle n).1 := (nSimplicialBundle n).2
    ⟨SimplicialObject (nSimplicialBundle n).1,
     inferInstanceAs (Category (SimplicialObject (nSimplicialBundle n).1))⟩

/-- The type of **n-fold simplicial objects** in `SSet`.
* `NSimplicial 0 = SSet` (simplicial sets)
* `NSimplicial (n+1) = SimplicialObject (NSimplicial n)` -/
@[reducible] def NSimplicial (n : ℕ) : Type (u + 1) := (nSimplicialBundle.{u} n).1

/-- Each `NSimplicial n` carries a category structure. -/
noncomputable instance instCategoryNSimplicial (n : ℕ) :
    Category.{u} (NSimplicial.{u} n) :=
  (nSimplicialBundle.{u} n).2

/-- n-fold simplicial sets have pullbacks, inherited from `SSet` via functor categories
and constructed recursively through simplicial-object categories. -/
noncomputable instance instHasPullbacksNSimplicial (n : ℕ) :
    HasPullbacks (NSimplicial.{u} n) := by
  induction n with
  | zero =>
      change HasLimitsOfShape WalkingCospan SSet.{u}
      infer_instance
  | succ n ih =>
      letI : Category.{u} (NSimplicial.{u} n) := instCategoryNSimplicial n
      letI : HasLimitsOfShape WalkingCospan (NSimplicial.{u} n) := ih
      change HasLimitsOfShape WalkingCospan (SimplexCategoryᵒᵖ ⥤ NSimplicial.{u} n)
      infer_instance

/-! ### Helpers for accessing simplicial structure -/

/-- Evaluate an (n+1)-fold simplicial set at simplicial degree `k`. -/
noncomputable def nLevel {n : ℕ} (X : NSimplicial.{u} (n + 1)) (k : ℕ) :
    NSimplicial.{u} n :=
  X.obj (op (mk k))

/-- Recursive outer-fibrancy proxy for iterated simplicial objects.

At the base level this is `IsOuterReedyFibrant` from `CSS.lean`. In higher dimensions,
we ask each outer simplicial level to carry the same proxy recursively. This is still not
the full Reedy model-structure datum, but it is a genuine non-vacuous hypothesis and makes
the intended extra fibrancy assumptions explicit in the interface. -/
def HasOuterReedyFibrancy : {n : ℕ} → NSimplicial.{u} (n + 1) → Prop
  | 0, X => SSet.IsOuterReedyFibrant X
  | _ + 1, X => ∀ k : ℕ, HasOuterReedyFibrancy (nLevel X k)

/-- The component of a morphism of (n+1)-fold simplicial sets at degree `k`. -/
noncomputable def nLevelMap {n : ℕ} {X Y : NSimplicial.{u} (n + 1)}
    (f : X ⟶ Y) (k : ℕ) : nLevel X k ⟶ nLevel Y k :=
  f.app (op (mk k))

/-- Evaluate an (n+2)-fold simplicial set at degree `k` in the **second** (inner)
simplicial direction, yielding an (n+1)-fold simplicial set.

For `X : NSimplicial (n+2)`, `innerEval k X` is the simplicial object in
`NSimplicial n` that at outer degree `j` gives `(X _⦋j⦌) _⦋k⦌` (the `(j,k)`-component
of `X`). -/
noncomputable def innerEval {n : ℕ} (k : ℕ) (X : NSimplicial.{u} (n + 2)) :
    NSimplicial.{u} (n + 1) where
  obj j := (X.obj j).obj (op (mk k))
  map f := (X.map f).app (op (mk k))
  map_id j := by simp only [X.map_id]; rfl
  map_comp f g := by simp only [X.map_comp]; rfl

/-- A morphism `j₁ ⟶ j₂` in `SimplexCategoryᵒᵖ` (i.e., a simplicial operator in the
inner direction) induces a morphism `innerEval j₁ X ⟶ innerEval j₂ X` by applying
each level's functorial action. -/
noncomputable def innerEvalMorph {n : ℕ} {j₁ j₂ : SimplexCategoryᵒᵖ}
    (f : j₁ ⟶ j₂) (X : NSimplicial.{u} (n + 2)) :
    innerEval j₁.unop.len X ⟶ innerEval j₂.unop.len X where
  app := fun p => (X.obj p).map f
  naturality _ _ h := ((X.map h).naturality f).symm

/-- A morphism `g : Y₁ ⟶ Y₂` of (n+2)-fold simplicial sets induces a morphism
between inner evaluations at any fixed degree `k`. -/
noncomputable def innerEvalMap {n : ℕ} (k : ℕ)
    {Y₁ Y₂ : NSimplicial.{u} (n + 2)} (g : Y₁ ⟶ Y₂) :
    innerEval k Y₁ ⟶ innerEval k Y₂ where
  app := fun p => (g.app p).app (op (mk k))
  naturality _ _ h := by
    simp only [innerEval]
    exact congrArg (NatTrans.app · (op (mk k))) (g.naturality h)

@[simp]
lemma innerEvalMorph_id {n : ℕ} {j : SimplexCategoryᵒᵖ}
    (X : NSimplicial.{u} (n + 2)) :
    innerEvalMorph (𝟙 j) X = 𝟙 (innerEval j.unop.len X) := by
  apply CategoryTheory.SimplicialObject.hom_ext
  intro p
  change (X.obj p).map (𝟙 j) = 𝟙 ((X.obj p).obj j)
  exact (X.obj p).map_id j

@[simp]
lemma innerEvalMorph_comp {n : ℕ} {j₁ j₂ j₃ : SimplexCategoryᵒᵖ}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (X : NSimplicial.{u} (n + 2)) :
    innerEvalMorph (f ≫ g) X = innerEvalMorph f X ≫ innerEvalMorph g X := by
  apply CategoryTheory.SimplicialObject.hom_ext
  intro p
  change (X.obj p).map (f ≫ g) = (X.obj p).map f ≫ (X.obj p).map g
  exact (X.obj p).map_comp f g

@[simp]
lemma innerEvalMap_id {n : ℕ} (k : ℕ) (Y : NSimplicial.{u} (n + 2)) :
    innerEvalMap k (𝟙 Y) = 𝟙 (innerEval k Y) := by
  apply CategoryTheory.SimplicialObject.hom_ext
  intro p
  rfl

@[simp]
lemma innerEvalMap_comp {n : ℕ} (k : ℕ)
    {Y₁ Y₂ Y₃ : NSimplicial.{u} (n + 2)} (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    innerEvalMap k (g₁ ≫ g₂) = innerEvalMap k g₁ ≫ innerEvalMap k g₂ := by
  apply CategoryTheory.SimplicialObject.hom_ext
  intro p
  rfl

lemma innerEvalMorph_comp_innerEvalMap {n : ℕ} {j₁ j₂ : SimplexCategoryᵒᵖ}
    (f : j₁ ⟶ j₂) {Y₁ Y₂ : NSimplicial.{u} (n + 2)} (g : Y₁ ⟶ Y₂) :
    innerEvalMorph f Y₁ ≫ innerEvalMap j₂.unop.len g =
      innerEvalMap j₁.unop.len g ≫ innerEvalMorph f Y₂ := by
  apply CategoryTheory.SimplicialObject.hom_ext
  intro p
  exact (g.app p).naturality f

/-! ### Levelwise weak equivalences -/

/-- A morphism of n-fold simplicial sets is a **levelwise weak equivalence** if:
* At level 0: it is a weak homotopy equivalence of simplicial sets.
* At level n+1: each component (at every simplicial degree) is a levelwise
  weak equivalence at level n. -/
def IsNWeakEquiv : (n : ℕ) → {X Y : NSimplicial.{u} n} → (X ⟶ Y) → Prop
  | 0 => fun f => IsWeakHomotopyEquiv f
  | n + 1 => fun f => ∀ (k : ℕ), IsNWeakEquiv n (nLevelMap f k)

/-! ### Generalized Segal and completeness conditions -/

/-- The **generalized Segal map** for a simplicial object `X` in `NSimplicial n`.
Sends a 2-simplex to its pair of composable edges in the pullback
`nLevel X 1 ×_{nLevel X 0} nLevel X 1`.

This generalizes `segalMap₂` from `SimplicialObject SSet` to all levels. -/
noncomputable def nSegalMap {n : ℕ} (X : NSimplicial.{u} (n + 1)) :
    nLevel X 2 ⟶ pullback
      (X.δ (0 : Fin 2) : nLevel X 1 ⟶ nLevel X 0) (X.δ 1) :=
  pullback.lift (X.δ 2) (X.δ 0)
    (X.δ_comp_δ (show (0 : Fin 2) ≤ 1 from Fin.zero_le _))

/-- The recursive functor sending an (n+1)-fold simplicial set to its auxiliary
equivalence-space object. -/
noncomputable abbrev nEquivSpaceFunctor : (n : ℕ) → NSimplicial.{u} (n + 1) ⥤ NSimplicial.{u} n
  | 0 =>
      { obj := equivSpace
        map := fun g => equivSpaceMap g
        map_id := equivSpaceMap_id
        map_comp := fun _ _ => equivSpaceMap_comp _ _ }
  | n + 1 =>
      { obj := fun X =>
          { obj := fun j =>
              (nEquivSpaceFunctor n).obj (innerEval j.unop.len X)
            map := fun f =>
              (nEquivSpaceFunctor n).map (innerEvalMorph f X)
            map_id := by
              intro j
              rw [innerEvalMorph_id]
              exact (nEquivSpaceFunctor n).map_id (innerEval j.unop.len X)
            map_comp := by
              intro j₁ j₂ j₃ f g
              rw [innerEvalMorph_comp]
              exact
                (nEquivSpaceFunctor n).map_comp (innerEvalMorph f X) (innerEvalMorph g X) }
        map := fun g =>
          { app := fun j =>
              (nEquivSpaceFunctor n).map (innerEvalMap j.unop.len g)
            naturality := by
              intro j₁ j₂ f
              simpa using congrArg ((nEquivSpaceFunctor n).map ·)
                (innerEvalMorph_comp_innerEvalMap f g) }
        map_id := by
          intro X
          apply CategoryTheory.SimplicialObject.hom_ext
          intro j
          change
            (nEquivSpaceFunctor n).map (innerEvalMap j.unop.len (𝟙 X)) =
              𝟙 ((nEquivSpaceFunctor n).obj (innerEval j.unop.len X))
          rw [innerEvalMap_id]
          exact (nEquivSpaceFunctor n).map_id (innerEval j.unop.len X)
        map_comp := by
          intro X Y Z g h
          apply CategoryTheory.SimplicialObject.hom_ext
          intro j
          change
            (nEquivSpaceFunctor n).map (innerEvalMap j.unop.len (g ≫ h)) =
              (nEquivSpaceFunctor n).map (innerEvalMap j.unop.len g) ≫
                (nEquivSpaceFunctor n).map (innerEvalMap j.unop.len h)
          rw [innerEvalMap_comp]
          exact
            (nEquivSpaceFunctor n).map_comp (innerEvalMap j.unop.len g)
              (innerEvalMap j.unop.len h) }

/-- The recursive auxiliary equivalence-space object of a simplicial object `X` in
`NSimplicial n`, defined by recursion on `n`:

* At level 0, this is `equivSpace X` — the vertexwise equivalence sub-simplicial-set
  of `X _⦋1⦌` from `CSS.lean`.
* At level `n+1`, this is defined pointwise: at each inner simplicial degree `k`,
  we evaluate `X` at `k` in the second simplicial direction and recursively
  take the same auxiliary construction.

In the absence of a full Reedy/Segal-space comparison theorem in the repository, this
should be read as the recursively defined proxy used by the completeness map, not as a
claim that every `NSimplicial (n+1)` already carries Rezk's canonical equivalence space. -/
@[reducible] noncomputable def nEquivSpace {n : ℕ}
    (X : NSimplicial.{u} (n + 1)) : NSimplicial.{u} n :=
  (nEquivSpaceFunctor.{u} n).obj X

/-- The functorial action of `nEquivSpace` on morphisms: a morphism `g : Y₁ ⟶ Y₂`
of (n+1)-fold simplicial sets induces `nEquivSpace Y₁ ⟶ nEquivSpace Y₂`.

At level 0, this is `equivSpaceMap`. At level `n+1`, it is the morphism part of
`nEquivSpaceFunctor`, applied pointwise to the maps between inner evaluations. -/
noncomputable def nEquivSpaceMap {n : ℕ}
    {Y₁ Y₂ : NSimplicial.{u} (n + 1)} (g : Y₁ ⟶ Y₂) :
    nEquivSpace Y₁ ⟶ nEquivSpace Y₂ :=
  (nEquivSpaceFunctor.{u} n).map g

/-- Evaluation at a fixed simplicial degree as a functor. -/
noncomputable def nLevelFunctor (n k : ℕ) : NSimplicial.{u} (n + 1) ⥤ NSimplicial.{u} n where
  obj X := nLevel X k
  map g := nLevelMap g k
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The recursive natural transformation implementing completeness for the auxiliary
equivalence-space construction at all levels. -/
noncomputable abbrev nCompletenessNatTrans :
    (n : ℕ) → nLevelFunctor n 0 ⟶ nEquivSpaceFunctor.{u} n
  | 0 =>
      { app := completenessMap
        naturality := by
          intro X Y g
          simpa [nLevelFunctor] using completenessMap_natural g }
  | n + 1 =>
      { app := fun X =>
          { app := fun j =>
              (nCompletenessNatTrans n).app (innerEval j.unop.len X)
            naturality := by
              intro j₁ j₂ f
              simpa [nLevelFunctor, nLevel, nLevelMap, nEquivSpaceFunctor] using
                (nCompletenessNatTrans n).naturality (innerEvalMorph f X) }
        naturality := by
          intro X Y g
          apply CategoryTheory.SimplicialObject.hom_ext
          intro j
          simpa [nLevelFunctor, nLevel, nLevelMap, nEquivSpaceFunctor] using
            (nCompletenessNatTrans n).naturality (innerEvalMap j.unop.len g) }

/-- The generalized completeness map sends an object (0-simplex of `nLevel X 0`)
to its identity morphism, viewed as an element of the recursive auxiliary
equivalence-space object.

* At level 0, this is `completenessMap X` from `CSS.lean`.
* At level `n+1`, this is defined pointwise: at each inner degree `k`,
  the component is `nCompletenessMap` applied to the inner evaluation. -/
noncomputable def nCompletenessMap : {n : ℕ} →
    (X : NSimplicial.{u} (n + 1)) → (nLevel X 0 ⟶ nEquivSpace X)
  | n, X => (nCompletenessNatTrans.{u} n).app X

/-! ### The (∞,n)-category predicate -/

/-- An **(∞,n)-category** is defined iteratively:
* **(∞,0)**: A Kan complex (every horn can be filled).
* **(∞,n+1)**: A simplicial object `X` in `NSimplicial n` such that:
  1. **Levelwise**: Each `X_k` is an (∞,n)-category.
  2. **Segal condition**: The Segal map is an n-weak equivalence.
  3. **Completeness**: The completeness map is an n-weak equivalence.

The repository's current ambient fibrancy proxy remains available separately as
`HasOuterReedyFibrancy`; it is not baked into the headline notion `IsInfNCat`. -/
def IsInfNCat : (n : ℕ) → NSimplicial.{u} n → Prop
  | 0, X => KanComplex X
  | n + 1, X =>
    (∀ (k : ℕ), IsInfNCat n (nLevel X k)) ∧
      IsNWeakEquiv n (nSegalMap X) ∧
      IsNWeakEquiv n (nCompletenessMap X)

/-- The repository's current presented `(∞,n)` notion: `IsInfNCat` together with the
recursive outer-fibrancy proxy used as ambient infrastructure in this development. -/
def IsPresentedInfNCat : (n : ℕ) → NSimplicial.{u} n → Prop
  | 0, X => IsInfNCat 0 X
  | n + 1, X => HasOuterReedyFibrancy X ∧ IsInfNCat (n + 1) X

/-! ### Recovering the concrete definitions -/

/-- At level 0, an (∞,0)-category is exactly a Kan complex. -/
theorem isInfNCat_zero_iff (X : NSimplicial.{u} 0) :
    IsInfNCat 0 X ↔ KanComplex X :=
  Iff.rfl

/-- At level 2, each simplicial level of an (∞,2)-category is an (∞,1)-category. -/
theorem isInfNCat_two_levelwise (X : NSimplicial.{u} 2)
    (h : IsInfNCat 2 X) (k : ℕ) :
    IsInfNCat 1 (nLevel X k) :=
  h.1 k

/-- At level 2, every entry of the trisimplicial set is a Kan complex.
This shows the iterative structure: (∞,2) requires (∞,1) at each level,
which in turn requires Kan at each sub-level. -/
theorem isInfNCat_two_kan (X : NSimplicial.{u} 2)
    (h : IsInfNCat 2 X) (k j : ℕ) :
    KanComplex (nLevel (nLevel X k) j) :=
  (h.1 k).1 j

end SSet
