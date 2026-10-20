import NativeWalkingRetractionMappingEquivalence
import NativeJoyalMappingWeakProperties

/-!
# Exact native internal-Hom homotopy-category objects and ordinary maps

Reuse the existing closed curryHomEquiv', unitHomEquiv, and the native ho object
equivalence. Actual precomposition and actual postcomposition retain ordinary
map composition under this full equivalence. No quasi-category or model is needed.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory MonoidalClosed
open DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerNativeIhomHoObjects
noncomputable section

def homObjectEquiv (A B : SSet.{u}) :
    (A ⟶ B) ≃ SSet.hoFunctor.obj ((ihom A).obj B) :=
  (MonoidalClosed.curryHomEquiv').trans
    ((SSet.unitHomEquiv _).trans (SSet.hoFunctor.obj.equiv _).symm)

def homObject {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.hoFunctor.obj ((ihom A).obj B) := homObjectEquiv A B f

theorem ho_map_obj {X Y : SSet.{u}} (f : X ⟶ Y) (x : SSet.hoFunctor.obj X) :
    SSet.hoFunctor.obj.equiv Y ((SSet.hoFunctor.map f).toFunctor.obj x) =
      f.app (Opposite.op ⦋0⦌) (SSet.hoFunctor.obj.equiv X x) := rfl

theorem curry'_pre {A B Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ Z) :
    MonoidalClosed.curry' g ≫ (MonoidalClosed.pre f).app Z =
      MonoidalClosed.curry' (f ≫ g) := by
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_pre_app, MonoidalClosed.curry',
    MonoidalClosed.uncurry_curry]
  rw [MonoidalCategory.rightUnitor_naturality_assoc]

theorem pre_obj {A B Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ Z) :
    (preHoFunctor f Z).obj (homObject g) = homObject (f ≫ g) := by
  apply (SSet.hoFunctor.obj.equiv _).injective
  rw [preHoFunctor, ho_map_obj]
  change (MonoidalClosed.curry' g ≫ (MonoidalClosed.pre f).app Z).app
      (Opposite.op ⦋0⦌) PUnit.unit =
    (MonoidalClosed.curry' (f ≫ g)).app (Opposite.op ⦋0⦌) PUnit.unit
  rw [curry'_pre]

def postHoFunctor (A : SSet.{u}) {B Z : SSet.{u}} (g : B ⟶ Z) :
    SSet.hoFunctor.obj ((ihom A).obj B) ⥤ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  (SSet.hoFunctor.map ((ihom A).map g)).toFunctor

theorem post_obj {A B Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ Z) :
    (postHoFunctor A g).obj (homObject f) = homObject (f ≫ g) := by
  apply (SSet.hoFunctor.obj.equiv _).injective
  rw [postHoFunctor, ho_map_obj]
  change (MonoidalClosed.curry' f ≫ (ihom A).map g).app
      (Opposite.op ⦋0⦌) PUnit.unit =
    (MonoidalClosed.curry' (f ≫ g)).app (Opposite.op ⦋0⦌) PUnit.unit
  rw [MonoidalClosed.curry'_ihom_map]

end
end DaggerNativeIhomHoObjects
