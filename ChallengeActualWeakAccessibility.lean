import ChallengeActualGlobalModel
import DaggerModels.DaggerRigidification
import DaggerModels.FreeBoundary
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-! Accessibility for the literal WG and its rigidification inverse image WD. -/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OrdinaryRigidification.DaggerRigidification
universe u

namespace DaggerActualWeakAccessibilityChallenge

abbrev G := DaggerSimplicialCat.{u, u}
abbrev D := DaggerSSet.{u}
abbrev weakG : MorphismProperty G.{u} := DaggerActualGlobalModelChallenge.weak.{u}
abbrev weakD : MorphismProperty D.{u} :=
  fun {_X _Y} f ↦ weakG (daggerRigidification.map f)
abbrev generators : MorphismProperty D.{u} := freeBoundaryGenerators freeDagger.{u}
abbrev weakGArrows : ObjectProperty (Arrow G.{u}) := fun f ↦ weakG f.hom
abbrev weakDArrows : ObjectProperty (Arrow D.{u}) := fun f ↦ weakD f.hom

def gStatement : Prop :=
  ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular)
    (Q : ObjectProperty weakGArrows.{u}.FullSubcategory),
    ObjectProperty.Small.{u} Q ∧ Q.IsCardinalFilteredGenerator κ ∧
      IsCardinalAccessibleCategory weakGArrows.{u}.FullSubcategory κ ∧
      weakGArrows.{u}.ι.IsCardinalAccessible κ

def dStatement : Prop :=
  ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular)
    (Q : ObjectProperty weakDArrows.{u}.FullSubcategory),
    ObjectProperty.Small.{u} Q ∧ Q.IsCardinalFilteredGenerator κ ∧
      IsCardinalAccessibleCategory weakDArrows.{u}.FullSubcategory κ ∧
      weakDArrows.{u}.ι.IsCardinalAccessible κ

def solutionStatement : Prop :=
  ∃ (index : generators.{u}.toSet → Type u)
    (arrow : ∀ i, index i → Arrow D.{u}),
    (∀ i s, weakD (arrow i s).hom) ∧
      ∀ (i : generators.{u}.toSet) (f : Arrow D.{u}), weakD f.hom → ∀ (φ : i.1 ⟶ f),
        ∃ (s : index i) (α : i.1 ⟶ arrow i s) (β : arrow i s ⟶ f), α ≫ β = φ

end DaggerActualWeakAccessibilityChallenge
