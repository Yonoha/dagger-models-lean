import NativeWalkingInternalHomCylinder

/-!
# Retractions with a whole original J-cylinder satisfy the mapping-category test

The conclusion concerns precisely the actual native internal Hom precomposition
functor under SSet.hoFunctor. It holds for every simplicial target, and therefore
also for each quasicategory in the ordinary Joyal mapping-category criterion.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeWalkingHomotopyNaturalIso
open DaggerNativeWalkingInternalHomCylinder
universe u
namespace DaggerNativeWalkingRetractionMappingEquivalence
noncomputable section

def preHoFunctor {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom B).obj Z) ⥤ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z)).toFunctor

theorem preHoFunctor_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (Z : SSet.{u}) :
    preHoFunctor g Z ⋙ preHoFunctor f Z = preHoFunctor (f ≫ g) Z := by
  unfold preHoFunctor
  rw [← Cat.Hom.comp_toFunctor, ← SSet.hoFunctor.map_comp,
    MonoidalClosed.pre_map, NatTrans.comp_app]

theorem preHoFunctor_id (A Z : SSet.{u}) :
    preHoFunctor (𝟙 A) Z = 𝟭 (SSet.hoFunctor.obj ((ihom A).obj Z)) := by
  rw [preHoFunctor, MonoidalClosed.pre_id, NatTrans.id_app,
    SSet.hoFunctor.map_id, Cat.Hom.id_toFunctor]

/-- Retain the entire original J-cylinder while transposing both exact endpoints. -/
def preRetractionIso {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (H : B ⊗ J ⟶ B)
    (h₀ : intervalEndpoint B false ≫ H = r ≫ g)
    (h₁ : intervalEndpoint B true ≫ H = 𝟙 B) (Z : SSet.{u}) :
    preHoFunctor (r ≫ g) Z ≅ preHoFunctor (𝟙 B) Z :=
  homotopyHoIso (preCylinder H Z) _ _
    (preCylinder_endpoint H Z false (r ≫ g) h₀)
    (preCylinder_endpoint H Z true (𝟙 B) h₁)

/-- The forward functor is exactly native precomposition with g. -/
def mappingEquivalence {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (hgr : g ≫ r = 𝟙 A) (H : B ⊗ J ⟶ B)
    (h₀ : intervalEndpoint B false ≫ H = r ≫ g)
    (h₁ : intervalEndpoint B true ≫ H = 𝟙 B) (Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom B).obj Z) ≌ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  CategoryTheory.Equivalence.mk (preHoFunctor g Z) (preHoFunctor r Z)
    ((eqToIso (preHoFunctor_id B Z)).symm ≪≫
      (preRetractionIso g r H h₀ h₁ Z).symm ≪≫
      (eqToIso (preHoFunctor_comp r g Z)).symm)
    (eqToIso (by rw [preHoFunctor_comp, hgr, preHoFunctor_id]))

/-- No fibrancy or pre-assumed categorical weak equivalence is required. -/
theorem preHoFunctor_isEquivalence {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (hgr : g ≫ r = 𝟙 A) (H : B ⊗ J ⟶ B)
    (h₀ : intervalEndpoint B false ≫ H = r ≫ g)
    (h₁ : intervalEndpoint B true ≫ H = 𝟙 B) (Z : SSet.{u}) :
    (preHoFunctor g Z).IsEquivalence :=
  show (mappingEquivalence g r hgr H h₀ h₁ Z).functor.IsEquivalence by infer_instance

end
end DaggerNativeWalkingRetractionMappingEquivalence
