import NativeBoundaryJoyalMappingWeak

/-!
# The actual ho functor sends full monomorphism-right maps to equivalences

The existing exact section and whole walking-isomorphism cylinder yield an actual
inverse on native homotopy categories. No quasi-category or Joyal-model premise is used.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeBoundaryJoyalMappingWeak DaggerNativeBoundaryCategoricalCylinder
open DaggerNativeWalkingHomotopyNaturalIso
universe u
namespace DaggerNativeBoundaryHoEquivalence
noncomputable section

def hoMap {X Y : SSet.{u}} (f : X ⟶ Y) : SSet.hoFunctor.obj X ⥤ SSet.hoFunctor.obj Y :=
  (SSet.hoFunctor.map f).toFunctor

theorem hoMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hoMap f ⋙ hoMap g = hoMap (f ≫ g) := by
  unfold hoMap
  rw [← Cat.Hom.comp_toFunctor, ← SSet.hoFunctor.map_comp]

theorem hoMap_id (X : SSet.{u}) : hoMap (𝟙 X) = 𝟭 (SSet.hoFunctor.obj X) := by
  rw [hoMap, SSet.hoFunctor.map_id, Cat.Hom.id_toFunctor]

/-- The forward functor is exactly the native ho of the original full mono-right map. -/
def monoRightHoEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    SSet.hoFunctor.obj X ≌ SSet.hoFunctor.obj Y := by
  let hSec := exists_section f hf
  let s := hSec.choose
  have hs := hSec.choose_spec
  have hr : (f ≫ s) ≫ f = f := by rw [Category.assoc, hs, Category.comp_id]
  let hCyl := exists_cylinder f hf (f ≫ s) hr
  let H := hCyl.choose
  have h0 := hCyl.choose_spec.1
  have h1 := hCyl.choose_spec.2.1
  let ε : hoMap (f ≫ s) ≅ hoMap (𝟙 X) := homotopyHoIso H _ _ h0 h1
  exact CategoryTheory.Equivalence.mk (hoMap f) (hoMap s)
    ((eqToIso (hoMap_id X)).symm ≪≫ ε.symm ≪≫ (eqToIso (hoMap_comp f s)).symm)
    (eqToIso (by rw [hoMap_comp, hs, hoMap_id]))

/-- Full mono-right maps induce equivalences of the actual native homotopy categories. -/
theorem monoRight_ho_isEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    (SSet.hoFunctor.map f).toFunctor.IsEquivalence :=
  show (monoRightHoEquivalence f hf).functor.IsEquivalence by infer_instance

end
end DaggerNativeBoundaryHoEquivalence
