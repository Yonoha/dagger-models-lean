import OriginalSimplicialPiZeroCategory
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# The whole original component-category functor and local weak equivalences

Bundle the proved full component functors into the native category of categories.
The actual vertex functor is natural for every original enriched functor. Every
original Homwise native weak equivalence induces a fully faithful functor on
component categories, without a Kan assumption on the original Homs.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialPiZeroFunctor
noncomputable section

/-- The actual full pi0-category functor retains the original object and component maps. -/
def piZeroFunctor : SimplicialCat.{u, u} ⥤ Cat.{u, u} where
  obj C := Cat.of (componentObjects C)
  map F := (componentFunctor F).toCatHom
  map_id C := by
    rw [componentFunctor_id]
    rfl
  map_comp F G := by
    rw [componentFunctor_comp]
    rfl

/-- The vertex-to-component functor is natural for every whole original enriched functor. -/
theorem vertexFunctor_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    degreeFunctor F (op ⦋0⦌) ⋙ vertexFunctor D = vertexFunctor C ⋙ componentFunctor F := by
  refine Functor.hext (F := degreeFunctor F (op ⦋0⦌) ⋙ vertexFunctor D)
    (G := vertexFunctor C ⋙ componentFunctor F) (fun _ ↦ rfl) ?_
  intro x y a
  rfl

/-- The exact native map on every original component Hom is bijective under local weakness. -/
theorem componentMap_bijective {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x y : componentObjects C) :
    Function.Bijective ((componentFunctor F).map (X := x) (Y := y)) := by
  have := hF x y
  exact bijective_mapPiZero (F.map x y)

/-- Local native weak equivalences give native fully faithful component functors on all Homs. -/
def componentFunctorFullyFaithful {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) : (componentFunctor F).FullyFaithful := by
  have : (componentFunctor F).Full := ⟨fun {x y} ↦ (componentMap_bijective F hF x y).2⟩
  have : (componentFunctor F).Faithful := ⟨fun {x y} ↦ (componentMap_bijective F hF x y).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful (componentFunctor F)

end
end DaggerOriginalSimplicialPiZeroFunctor
