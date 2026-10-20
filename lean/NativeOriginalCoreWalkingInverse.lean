import NativeWalkingKanTensor
import NativeWalkingInverseKanWeak

/-! Entire original J-inverse homotopies restrict to the exact original ordinary cores. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeKanSourceOriginalCoreFactor
open DaggerNativeWalkingKanTensor DaggerNativeJoyalWeakWholeWalkingInverse
open DaggerNativeWalkingInverseKanWeak DaggerNativeJoyalMappingTest
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCoreWalkingInverse
noncomputable section

theorem core_map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryCoreCandidateMap (f ≫ g) =
      ordinaryCoreCandidateMap f ≫ ordinaryCoreCandidateMap g := by
  apply NatTrans.ext
  funext q x
  apply Subtype.ext
  rfl

theorem core_map_id (X : SSet.{u}) : ordinaryCoreCandidateMap (𝟙 X) = 𝟙 _ := by
  apply NatTrans.ext
  funext q x
  apply Subtype.ext
  rfl

def coreCylinder {X : SSet.{u}} [X.Quasicategory] (H : X ⊗ J.{u} ⟶ X) :
    (ordinaryCoreCandidate X : SSet.{u}) ⊗ J.{u} ⟶ (ordinaryCoreCandidate X : SSet.{u}) := by
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex := native_quasi_core_kan X
  have : J.{u}.KanComplex := walking_kan
  have : ((ordinaryCoreCandidate X : SSet.{u}) ⊗ J.{u}).KanComplex := kan_tensor _ _
  exact factor (((ordinaryCoreCandidate X).ι ▷ J.{u}) ≫ H)

theorem coreCylinder_comp {X : SSet.{u}} [X.Quasicategory] (H : X ⊗ J.{u} ⟶ X) :
    coreCylinder H ≫ (ordinaryCoreCandidate X).ι =
      ((ordinaryCoreCandidate X).ι ▷ J.{u}) ≫ H := rfl

theorem coreCylinder_endpoint {X : SSet.{u}} [X.Quasicategory]
    (H : X ⊗ J.{u} ⟶ X) (b : Bool) (g : X ⟶ X)
    (hg : intervalEndpoint X b ≫ H = g) :
    intervalEndpoint (ordinaryCoreCandidate X : SSet.{u}) b ≫ coreCylinder H =
      ordinaryCoreCandidateMap g := by
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  rw [Category.assoc, coreCylinder_comp]
  have hn : intervalEndpoint (ordinaryCoreCandidate X : SSet.{u}) b ≫
      ((ordinaryCoreCandidate X).ι ▷ J.{u}) =
        (ordinaryCoreCandidate X).ι ≫ intervalEndpoint X b := by
    apply NatTrans.ext
    rfl
  rw [← Category.assoc, hn, Category.assoc, hg, ordinaryCoreCandidateMap_comp_ι]

def restrict {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) (d : WalkingInverseData f) : WalkingInverseData (ordinaryCoreCandidateMap f) where
  inv := ordinaryCoreCandidateMap d.inv
  leftCylinder := coreCylinder d.leftCylinder
  rightCylinder := coreCylinder d.rightCylinder
  left_zero := by
    simpa only [core_map_comp] using
      coreCylinder_endpoint d.leftCylinder false (f ≫ d.inv) d.left_zero
  left_one := by
    simpa only [core_map_id] using coreCylinder_endpoint d.leftCylinder true (𝟙 A) d.left_one
  right_zero := by
    simpa only [core_map_comp] using
      coreCylinder_endpoint d.rightCylinder false (d.inv ≫ f) d.right_zero
  right_one := by
    simpa only [core_map_id] using coreCylinder_endpoint d.rightCylinder true (𝟙 B) d.right_one

theorem weak_core_map {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) (hf : weakCategoricalEquivalences f) :
    WeakEquivalence (ordinaryCoreCandidateMap f) :=
  walking_inverse_Kan_weak _
    (restrict f (DaggerNativeJoyalWeakWholeWalkingInverse.fromWeak f hf))

end
end DaggerNativeOriginalCoreWalkingInverse
