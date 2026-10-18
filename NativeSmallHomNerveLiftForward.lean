import NativeSmallHomNerveLift

/-! The literal full chain map from a small-hom source to a large-hom target. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeSmallHomNerveLiftForward
noncomputable section

/-- Apply the original functor to every object and arrow of each whole chain. -/
def mixedMap {A B : Type u} [Category.{0} A] [Category.{u} B] (F : A ⥤ B) :
    nerve A ⟶ nerve B where
  app _ := (F.mapComposableArrows _).obj

/-- This is the same original map after raising and immediately unwrapping the source homs. -/
theorem up_mixedMap {A B : Type u} [Category.{0} A] [Category.{u} B] (F : A ⥤ B) :
    DaggerNativeSmallHomNerveLift.upMap A ≫ nerveMap (ULiftHom.down.{0, u, u} ⋙ F) =
      mixedMap F := rfl

end
end DaggerNativeSmallHomNerveLiftForward
