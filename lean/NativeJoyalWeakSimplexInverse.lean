import NativeHoIsoTriangles
import ActualAntiJoyalWeakInverseRecognition

/-!
# The entire mapping weak class has inverse witnesses using edges and 2-simplices

The whole inverse map remains part of the data. Four actual internal-Hom edges
and four actual cancellation triangles witness both endomorphism isomorphisms.
This is not a cardinal bound on that inverse map or an accessibility theorem.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerNativeIhomHoObjects DaggerNativeJoyalWeakQuasiInverse
open DaggerNativeHoIsoTriangles DaggerNativeJoyalWeakInverseRecognition
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeJoyalWeakSimplexInverse
noncomputable section

structure SimplexInverseData {A B : SSet.{u}} (f : A ⟶ B) where
  inv : B ⟶ A
  left : IsoTriangles ((ihom A).obj A) (homObject (f ≫ inv)) (homObject (𝟙 A))
  right : IsoTriangles ((ihom B).obj B) (homObject (inv ≫ f)) (homObject (𝟙 B))

def SimplexInverseData.toInverseData {A B : SSet.{u}} {f : A ⟶ B}
    (d : SimplexInverseData f) : InverseData f := ⟨d.inv, d.left.toIso, d.right.toIso⟩

def SimplexInverseData.fromInverseData {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    {f : A ⟶ B} (d : InverseData f) : SimplexInverseData f := by
  have : ((ihom A).obj A).Quasicategory :=
    DaggerNativeIhomQuasicategories.ihom_quasicategory A A
  have : ((ihom B).obj B).Quasicategory :=
    DaggerNativeIhomQuasicategories.ihom_quasicategory B B
  exact ⟨d.inv, IsoTriangles.fromIso d.leftIso, IsoTriangles.fromIso d.rightIso⟩

theorem simplex_inverse_weak {A B : SSet.{u}} (f : A ⟶ B) (d : SimplexInverseData f) :
    weakCategoricalEquivalences f := inverse_data_weak f d.toInverseData

theorem quasi_weak_iff_simplex_inverse {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) : weakCategoricalEquivalences f ↔ Nonempty (SimplexInverseData f) := by
  rw [quasi_weak_iff_inverse_data]
  exact ⟨fun ⟨d⟩ ↦ ⟨SimplexInverseData.fromInverseData d⟩,
    fun ⟨d⟩ ↦ ⟨d.toInverseData⟩⟩

theorem weak_iff_replacement_simplex_inverse {A B : SSet.{u}} (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔
      Nonempty (SimplexInverseData (DaggerNativeInnerHornFactorization.replacement.map f)) := by
  exact (DaggerNativeInnerQuasicategoryWeakReplacement.replacement_map_weak_iff f).symm.trans
    (quasi_weak_iff_simplex_inverse (DaggerNativeInnerHornFactorization.replacement.map f))

theorem actual_weak_iff_replacement_underlying_simplex_inverse
    {A B : AntiInvolutiveSSet.{u}} (f : A ⟶ B) :
    DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f ↔
      Nonempty (SimplexInverseData
        (DaggerActualAntiInnerHornFactorization.replacement.map f).hom) := by
  exact (DaggerActualAntiInnerWeakReplacement.replacement_map_weak_iff f).symm.trans
    (quasi_weak_iff_simplex_inverse
      (DaggerActualAntiInnerHornFactorization.replacement.map f).hom)

end
end DaggerNativeJoyalWeakSimplexInverse
