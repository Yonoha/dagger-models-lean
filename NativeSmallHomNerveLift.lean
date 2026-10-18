import NativeCommaSecondCostructuredArrowRetractSmallOperators

/-! Preserve the literal nerve when raising only the universe of small hom types. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeSmallHomNerveLift
noncomputable section

variable (C : Type u) [Category.{0} C]

/-- The same chain, with each arrow wrapped by Mathlib's ULiftHom.up. -/
def upMap : nerve C ⟶ nerve (ULiftHom.{u} C) where
  app _ := (ULiftHom.up.{0, u, u}.mapComposableArrows _).obj

/-- Unwrap each arrow of exactly the same chain. -/
def downMap : nerve (ULiftHom.{u} C) ⟶ nerve C where
  app _ := (ULiftHom.down.{0, u, u}.mapComposableArrows _).obj

/-- Raising the hom universe gives an isomorphism of the full original simplicial sets. -/
def iso : nerve C ≅ nerve (ULiftHom.{u} C) where
  hom := upMap C
  inv := downMap C
  hom_inv_id := by
    apply NatTrans.ext
    funext q x
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  inv_hom_id := by
    apply NatTrans.ext
    funext q x
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The map on full chains of a functor from large hom types to small hom types. -/
def mixedMap {A B : Type u} [Category.{u} A] [Category.{0} B] (F : A ⥤ B) :
    nerve A ⟶ nerve B where
  app _ := (F.mapComposableArrows _).obj

/-- The literal mixed map followed by the isomorphism is the native homogeneous nerve map. -/
theorem mixedMap_up {A B : Type u} [Category.{u} A] [Category.{0} B] (F : A ⥤ B) :
    mixedMap F ≫ upMap B = nerveMap (F ⋙ ULiftHom.up.{0, u, u}) := rfl

end
end DaggerNativeSmallHomNerveLift
