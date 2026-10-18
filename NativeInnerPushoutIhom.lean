import NativeInnerHornUnionProd
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions

/-!
# Whole inner pushout-products and native internal-Hom pullback maps

Use the actual original union-product inclusion and the exact two-variable adjunction.
All monomorphisms, all inner-left maps and all full internal-Hom pullback squares are
retained. No Joyal model, Cartesian-model structure or desired product closure is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerNativeInnerHornFactorization DaggerNativeInnerHornUnionProd
universe u
namespace DaggerNativeInnerPushoutIhom
noncomputable section

/-- Full internal-Hom pullback maps are inner-right for every mono and inner-right input. -/
theorem pullback_inner {A B E T : SSet.{u}} {i : A ⟶ B} [Mono i] {p : E ⟶ T}
    (hp : innerFibrations p) (sq : SSet.PullbackIhom i p) : innerFibrations sq.π := by
  rw [innerFibrations_iff]
  intro n k h0 hn
  let s₁₂ : SSet.PushoutTensor i (SSet.horn (n + 2) k).ι :=
    Functor.PushoutObjObj.ofHasPushout _ _ _
  rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom s₁₂ sq]
  suffices innerAnodyne s₁₂.ι from this p hp
  intro E' T' q hq
  rw [← HasLiftingProperty.iff_of_arrow_iso_left s₁₂.flipArrowIso]
  let s₁₃ : SSet.PullbackIhom (SSet.horn (n + 2) k).ι q :=
    Functor.PullbackObjObj.ofHasPullback _ _ _
  rw [SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom s₁₂.flip s₁₃]
  have hm : (MorphismProperty.monomorphisms SSet.{u}).rlp s₁₃.π := by
    apply DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_monomorphisms
    intro m
    rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom
      (SSet.PushoutTensor.unionProd (SSet.horn (n + 2) k) (SSet.boundary m)) s₁₃,
      SSet.PushoutTensor.ι_unionProd]
    exact horn_union_boundary_innerAnodyne n k h0 hn m q hq
  exact hm i (show Mono i from inferInstance)

/-- The complete pushout-product of a mono and an inner-left map is inner-left. -/
theorem pushout_inner {A₁ B₁ A₂ B₂ : SSet.{u}} {i : A₁ ⟶ B₁} [Mono i] {j : A₂ ⟶ B₂}
    (hj : innerAnodyne j) (sq : SSet.PushoutTensor i j) : innerAnodyne sq.ι := by
  intro E T p hp
  let s₁₃ : SSet.PullbackIhom i p := Functor.PullbackObjObj.ofHasPullback _ _ _
  rw [SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq s₁₃]
  exact hj s₁₃.π (pullback_inner hp s₁₃)

/-- The same complete pushout-product with the two original inputs reversed. -/
theorem pushout_inner_left {A₁ B₁ A₂ B₂ : SSet.{u}} {i : A₁ ⟶ B₁} {j : A₂ ⟶ B₂}
    [Mono j] (hi : innerAnodyne i) (sq : SSet.PushoutTensor i j) : innerAnodyne sq.ι := by
  haveI : innerAnodyne.{u}.RespectsIso := by
    unfold innerAnodyne
    infer_instance
  have h := pushout_inner hi sq.flip
  exact (innerAnodyne.arrow_mk_iso_iff sq.flipArrowIso).1 h

end
end DaggerNativeInnerPushoutIhom
