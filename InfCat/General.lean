/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import InfCat.CSS

/-!
# General (∞,n)-Categories via Iterated Complete Segal Spaces

We define (∞,n)-categories for all `n` using n-fold complete Segal spaces.
The definition is inductive:
* **(∞,0)-Cat** = Kan complexes (spaces / ∞-groupoids)
* **(∞,n+1)-Cat** = complete Segal objects whose levels are (∞,n)-categories

## Main definitions

* `SSet.NSimplicial n` : The type of n-fold simplicial objects in `SSet`.
* `SSet.IsNWeakEquiv` : Levelwise weak equivalences of n-fold simplicial sets.
* `SSet.nSegalMap` : The generalized Segal map at each level.
* `SSet.nEquivSpace` : The generalized space of equivalences at each level.
* `SSet.nEquivSpaceMap` : Functorial action of `nEquivSpace` on morphisms.
* `SSet.nCompletenessMap` : The generalized completeness map at each level.
* `SSet.IsInfNCat` : The (∞,n)-category predicate for all `n`.

## Implementation notes

Since `SimplicialObject C` requires `[Category C]`, the type family `NSimplicial n`
and its category instance must be defined simultaneously. We bundle them into
`nSimplicialBundle` and project out.

The space of equivalences `nEquivSpace` and its functorial action `nEquivSpaceMap`
are defined simultaneously via `nEquivSpaceBundle`, a single recursive function
returning both the object map and the morphism map. This avoids mutual recursion,
which Lean 4 does not support when one definition appears in another's type signature.

* At level 0, `nEquivSpace` is `equivSpace` from `CSS.lean`.
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

/-- n-fold simplicial sets have pullbacks, inherited from `SSet` via functor categories.

TODO: Prove by induction using `Limits.hasLimitsOfShape_functor_category`. -/
noncomputable instance instHasPullbacksNSimplicial (n : ℕ) :
    HasPullbacks (NSimplicial.{u} n) := sorry

/-! ### Helpers for accessing simplicial structure -/

/-- Evaluate an (n+1)-fold simplicial set at simplicial degree `k`. -/
noncomputable def nLevel {n : ℕ} (X : NSimplicial.{u} (n + 1)) (k : ℕ) :
    NSimplicial.{u} n :=
  X.obj (op (mk k))

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

/-- The functorial action of `equivSpace` on morphisms of simplicial spaces.
A morphism `g : Y₁ ⟶ Y₂` preserves equivalence morphisms, so the induced map
on `X _⦋1⦌` restricts to a map on equivalence spaces. -/
noncomputable def equivSpaceMap {Y₁ Y₂ : SimplicialObject SSet.{u}}
    (g : Y₁ ⟶ Y₂) : equivSpace Y₁ ⟶ equivSpace Y₂ where
  app := fun U ⟨σ, _⟩ => ⟨(g.app (op ⦋1⦌)).app U σ, sorry⟩
  naturality := sorry

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

/-- Auxiliary bundle packaging `nEquivSpace` (the object map) and `nEquivSpaceMap`
(the functorial action on morphisms) into a single recursive definition.
This avoids mutual recursion, which Lean 4 does not support when one definition
appears in another's type signature.

The first component maps an (n+1)-fold simplicial set to its space of equivalences.
The second component lifts morphisms through the equivalence space construction. -/
noncomputable def nEquivSpaceBundle : (n : ℕ) →
    Σ (F : NSimplicial.{u} (n + 1) → NSimplicial.{u} n),
      ({Y₁ Y₂ : NSimplicial.{u} (n + 1)} → (Y₁ ⟶ Y₂) → (F Y₁ ⟶ F Y₂))
  | 0 => ⟨equivSpace, fun g => equivSpaceMap g⟩
  | n + 1 =>
    ⟨fun X =>
      { obj := fun j =>
          (nEquivSpaceBundle n).1 (innerEval j.unop.len X)
        map := fun f =>
          (nEquivSpaceBundle n).2 (innerEvalMorph f X)
        map_id := sorry
        map_comp := sorry },
     fun g =>
      { app := fun j =>
          (nEquivSpaceBundle n).2 (innerEvalMap j.unop.len g)
        naturality := sorry }⟩

/-- The **generalized space of equivalences** of a simplicial object `X` in
`NSimplicial n`, defined by recursion on `n`:

* At level 0, this is `equivSpace X` — the sub-simplicial-set of `X _⦋1⦌`
  consisting of equivalence morphisms (see `CSS.lean`).
* At level `n+1`, this is defined pointwise: at each inner simplicial degree `k`,
  we evaluate `X` at `k` in the second simplicial direction and recursively
  take the space of equivalences. -/
@[reducible] noncomputable def nEquivSpace {n : ℕ}
    (X : NSimplicial.{u} (n + 1)) : NSimplicial.{u} n :=
  (nEquivSpaceBundle.{u} n).1 X

/-- The functorial action of `nEquivSpace` on morphisms: a morphism `g : Y₁ ⟶ Y₂`
of (n+1)-fold simplicial sets induces `nEquivSpace Y₁ ⟶ nEquivSpace Y₂`.

At level 0, this is `equivSpaceMap`. At level `n+1`, it is defined pointwise
by applying `nEquivSpaceMap` to the inner evaluations. -/
noncomputable def nEquivSpaceMap {n : ℕ}
    {Y₁ Y₂ : NSimplicial.{u} (n + 1)} (g : Y₁ ⟶ Y₂) :
    nEquivSpace Y₁ ⟶ nEquivSpace Y₂ :=
  (nEquivSpaceBundle.{u} n).2 g

/-- The **generalized completeness map** sends an object (0-simplex of `nLevel X 0`)
to its identity morphism, viewed as an element of the space of equivalences.

* At level 0, this is `completenessMap X` from `CSS.lean`.
* At level `n+1`, this is defined pointwise: at each inner degree `k`,
  the component is `nCompletenessMap` applied to the inner evaluation. -/
noncomputable def nCompletenessMap : {n : ℕ} →
    (X : NSimplicial.{u} (n + 1)) → (nLevel X 0 ⟶ nEquivSpace X)
  | 0, X => completenessMap X
  | n + 1, X =>
    { app := fun j => nCompletenessMap (innerEval j.unop.len X)
      naturality := sorry }

/-! ### The (∞,n)-category predicate -/

/-- An **(∞,n)-category** is defined iteratively:
* **(∞,0)**: A Kan complex (every horn can be filled).
* **(∞,n+1)**: A simplicial object `X` in `NSimplicial n` such that:
  1. **Levelwise**: Each `X_k` is an (∞,n)-category.
  2. **Segal condition**: The Segal map is an n-weak equivalence.
  3. **Completeness**: The completeness map is an n-weak equivalence. -/
def IsInfNCat : (n : ℕ) → NSimplicial.{u} n → Prop
  | 0, X => KanComplex X
  | n + 1, X =>
    (∀ (k : ℕ), IsInfNCat n (nLevel X k)) ∧
    IsNWeakEquiv n (nSegalMap X) ∧
    IsNWeakEquiv n (nCompletenessMap X)

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
