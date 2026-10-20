import NativeBisimplicialBoxUnion
import NativeReedyBoxExtension

/-! Reedy fibrations lift against the actual union inclusion when its vertical side is anodyne. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxUnion DaggerNativeReedyBoxExtension
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyBoxUnionLifting
noncomputable section

theorem union_lifting {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)
    [WeakEquivalence A.ι] {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f) :
    HasLiftingProperty (unionInclusion H A) f := by
  have : Cofibration A.ι := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  constructor
  intro a b sq
  have hab : boxMap H.ι (𝟙 (A : SSet.{u})) ≫ (verticalInclusion H A ≫ a) =
      boxMap (𝟙 (H : SSet.{u})) A.ι ≫ (horizontalInclusion H A ≫ a) := by
    rw [← Category.assoc, intersection_square, Category.assoc]
  have hac : (verticalInclusion H A ≫ a) ≫ f = boxMap (𝟙 K) A.ι ≫ b := by
    have he := congrArg (fun t ↦ verticalInclusion H A ≫ t) sq.w
    simpa only [← Category.assoc, verticalInclusion_comp] using he
  have hbc : (horizontalInclusion H A ≫ a) ≫ f = boxMap H.ι (𝟙 B) ≫ b := by
    have he := congrArg (fun t ↦ horizontalInclusion H A ≫ t) sq.w
    simpa only [← Category.assoc, horizontalInclusion_comp] using he
  obtain ⟨d, hdA, hdH, hdf⟩ := compatible_box_extension H.ι A.ι f hf
    (verticalInclusion H A ≫ a) (horizontalInclusion H A ≫ a) b hab hac hbc
  refine ⟨d, ?_, hdf⟩
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  rcases p.property with hp | hp
  · exact congrFun (NatTrans.congr_app (NatTrans.congr_app hdH h) v)
      (⟨p.val.1, hp⟩, p.val.2)
  · exact congrFun (NatTrans.congr_app (NatTrans.congr_app hdA h) v)
      (p.val.1, ⟨p.val.2, hp⟩)

end
end DaggerNativeReedyBoxUnionLifting
