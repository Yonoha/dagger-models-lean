import FixedGraphDecomposition
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Exact hom-wise properties under the fixed-object graph decomposition

The original dagger square is an isomorphism in the arrow category. Thus a
property respecting isomorphisms holds on all original hom maps exactly when
it holds on every off-diagonal factor and every underlying diagonal action map.
This does not assert existence of a model structure on graphs or actions.
-/

open CategoryTheory DaggerModels
open FixedDaggerSimplicialGraph

universe u

namespace DaggerFixedGraph

variable {O : Type u}
  {G H : FixedDaggerSimplicialGraph O}

/-- The original reversed hom maps are isomorphic arrows using the actual daggers. -/
def homArrowIso (f : G ⟶ H) (x y : O) : Arrow.mk (f.map x y) ≅ Arrow.mk (f.map y x) :=
  Arrow.isoMk (daggerIso G x y) (daggerIso H x y) (f.map_dagger x y).symm

/-- Any isomorphism-stable property has the same value on reversed original hom maps. -/
theorem hom_property_swap (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    (f : G ⟶ H) (x y : O) : P (f.map x y) ↔ P (f.map y x) :=
  P.arrow_mk_iso_iff (homArrowIso f x y)

variable [LinearOrder O]

/-- The actual decomposition detects the property on all ordered pairs, including diagonals. -/
theorem homwise_iff_factors (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    (f : G ⟶ H) :
    (∀ x y : O, P (f.map x y)) ↔
      (∀ p : Upper O, P (((decomposition (O := O)).functor.map f).1 p)) ∧
        (∀ x : O, P ((((decomposition (O := O)).functor.map f).2 x).app PUnit.unit)) := by
  change (∀ x y : O, P (f.map x y)) ↔
    (∀ p : Upper O, P (f.map p.1.1 p.1.2)) ∧ (∀ x : O, P (f.map x x))
  constructor
  · intro h
    exact ⟨fun p ↦ h p.1.1 p.1.2, fun x ↦ h x x⟩
  · rintro ⟨hu, hd⟩ x y
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · exact hu ⟨(x, y), hxy⟩
    · exact hd x
    · exact (hom_property_swap P f x y).2 (hu ⟨(y, x), hyx⟩)

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

/-- Actual horn-defined Kan fibrations, without a graph model-structure premise. -/
theorem kan_fibration_iff_factors (f : G ⟶ H) :
    (∀ x y : O, Fibration (f.map x y)) ↔
      (∀ p : Upper O, Fibration (((decomposition (O := O)).functor.map f).1 p)) ∧
        (∀ x : O, Fibration ((((decomposition (O := O)).functor.map f).2 x).app PUnit.unit)) := by
  have hP : (fibrations SSet.{u}).RespectsIso := by
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    infer_instance
  simpa only [HomotopicalAlgebra.fibration_iff] using homwise_iff_factors (fibrations SSet.{u}) f

end DaggerFixedGraph

namespace DaggerFixedGraph

abbrev ChosenUpper (O : Type u) := @Upper.{u} O (chosenLinearOrder O)

/-- The same statement for arbitrary original object types, using the already chosen order. -/
theorem fixedObject_homwise_iff_factors {O : Type u}
    {G H : FixedDaggerSimplicialGraph O} (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    (f : G ⟶ H) :
    (∀ x y : O, P (f.map x y)) ↔
      (∀ p : ChosenUpper O, P (((fixedObjectDecomposition O).functor.map f).1 p)) ∧
        (∀ x : O, P ((((fixedObjectDecomposition O).functor.map f).2 x).app PUnit.unit)) :=
  @homwise_iff_factors.{u} O G H (chosenLinearOrder O) P _ f

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

/-- Actual Kan fibrations detected by the decomposition for arbitrary object types. -/
theorem fixedObject_kan_fibration_iff_factors {O : Type u}
    {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (∀ x y : O, Fibration (f.map x y)) ↔
      (∀ p : ChosenUpper O, Fibration (((fixedObjectDecomposition O).functor.map f).1 p)) ∧
        (∀ x : O,
          Fibration ((((fixedObjectDecomposition O).functor.map f).2 x).app PUnit.unit)) :=
  @kan_fibration_iff_factors.{u} O G H (chosenLinearOrder O) f

end DaggerFixedGraph
