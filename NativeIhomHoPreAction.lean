import NativeIhomHoObjects

/-!
# Whole internal-Hom ho isomorphisms act on the original mapping categories

Use the existing closed composition and the actual monoidal ho functor. Currying
the resulting ordinary bifunctor sends an isomorphism between original map
objects to a natural isomorphism of the exact original precomposition functors.
No J-representation of arbitrary ho isomorphisms is assumed.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerNativeIhomHoObjects DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerNativeIhomHoPreAction
noncomputable section

def compositionFunctor (A B Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom A).obj B) × SSet.hoFunctor.obj ((ihom B).obj Z) ⥤
      SSet.hoFunctor.obj ((ihom A).obj Z) :=
  (Functor.LaxMonoidal.μ SSet.hoFunctor ((ihom A).obj B) ((ihom B).obj Z) ≫
    SSet.hoFunctor.map (MonoidalClosed.comp A B Z)).toFunctor

def preAction (A B Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom A).obj B) ⥤
      SSet.hoFunctor.obj ((ihom B).obj Z) ⥤ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  Functor.curry.obj (compositionFunctor A B Z)

theorem mapped_section {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    (λ_ (SSet.hoFunctor.obj ((ihom B).obj Z))).inv ≫
      (Functor.LaxMonoidal.ε SSet.hoFunctor ≫
        SSet.hoFunctor.map (MonoidalClosed.curry' f)) ▷
          SSet.hoFunctor.obj ((ihom B).obj Z) ≫
      Functor.LaxMonoidal.μ SSet.hoFunctor ((ihom A).obj B) ((ihom B).obj Z) ≫
      SSet.hoFunctor.map (MonoidalClosed.comp A B Z) =
        SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z) := by
  rw [comp_whiskerRight_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.left_unitality_inv_assoc,
    ← SSet.hoFunctor.map_comp, ← SSet.hoFunctor.map_comp]
  congr 1

theorem preAction_homObject {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) :
    (preAction A B Z).obj (homObject f) = preHoFunctor f Z := by
  have h := congrArg Cat.Hom.toFunctor (mapped_section f Z)
  change (λ_ (SSet.hoFunctor.obj ((ihom B).obj Z))).inv.toFunctor ⋙
    (((Functor.LaxMonoidal.ε SSet.hoFunctor).toFunctor ⋙
      (SSet.hoFunctor.map (MonoidalClosed.curry' f)).toFunctor).prod
        (𝟭 (SSet.hoFunctor.obj ((ihom B).obj Z)))) ⋙ compositionFunctor A B Z =
          preHoFunctor f Z at h
  rw [← SSet.hoFunctor.unitHomEquiv_eq] at h
  exact h

def preIso {A B : SSet.{u}} (f g : A ⟶ B) (e : homObject f ≅ homObject g)
    (Z : SSet.{u}) : preHoFunctor f Z ≅ preHoFunctor g Z :=
  (eqToIso (preAction_homObject f Z)).symm ≪≫ (preAction A B Z).mapIso e ≪≫
    eqToIso (preAction_homObject g Z)

end
end DaggerNativeIhomHoPreAction
