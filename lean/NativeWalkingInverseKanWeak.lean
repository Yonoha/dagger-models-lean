import NativeJoyalWeakWholeWalkingInverse
import NativeWalkingEdgeKanInclusion
import NativeSSetRawHomotopyEquivalenceWeak

/-! Whole original J-inverse homotopies give native Kan weak equivalences. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeWalkingEdgeKanInclusion DaggerNativeJoyalWeakWholeWalkingInverse
open DaggerNativeSSetRawHomotopyEquivalenceWeak DaggerNativeJoyalMappingTest
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWalkingInverseKanWeak
noncomputable section

theorem raw_zero_edge (A : SSet.{u}) :
    SSet.ι₀ ≫ (A ◁ edgeInclusion.{u}) = intervalEndpoint A false := by
  apply NatTrans.ext
  funext q a
  apply Prod.ext rfl
  apply nerve.ext_of_isThin
  rfl

theorem raw_one_edge (A : SSet.{u}) :
    SSet.ι₁ ≫ (A ◁ edgeInclusion.{u}) = intervalEndpoint A true := by
  apply NatTrans.ext
  funext q a
  apply Prod.ext rfl
  apply nerve.ext_of_isThin
  rfl

def rawHomotopyEquiv {A B : SSet.{u}} (f : A ⟶ B) (d : WalkingInverseData f) :
    SSet.HomotopyEquiv A B where
  hom := f
  inv := d.inv
  homInvId := SSet.Homotopy.mk ((A ◁ edgeInclusion.{u}) ≫ d.leftCylinder)
    (by rw [← Category.assoc, raw_zero_edge, d.left_zero])
    (by rw [← Category.assoc, raw_one_edge, d.left_one])
  invHomId := SSet.Homotopy.mk ((B ◁ edgeInclusion.{u}) ≫ d.rightCylinder)
    (by rw [← Category.assoc, raw_zero_edge, d.right_zero])
    (by rw [← Category.assoc, raw_one_edge, d.right_one])

theorem walking_inverse_Kan_weak {A B : SSet.{u}} (f : A ⟶ B)
    (d : WalkingInverseData f) : WeakEquivalence f :=
  rawHomotopyEquiv_weakEquivalence (rawHomotopyEquiv f d)

theorem quasi_weak_Kan_weak {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) (hf : weakCategoricalEquivalences f) : WeakEquivalence f :=
  walking_inverse_Kan_weak f (DaggerNativeJoyalWeakWholeWalkingInverse.fromWeak f hf)

end
end DaggerNativeWalkingInverseKanWeak
