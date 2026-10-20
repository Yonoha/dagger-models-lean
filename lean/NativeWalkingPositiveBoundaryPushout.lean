import NativeWalkingFullBlockRegularity
import NativeWalkingMonoPushout

/-! Every choice of the actual positive-boundary/zero-endpoint pushout has an inner-left map. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingMonoPushout
open DaggerNativeInnerHornFactorization DaggerNativeWalkingFullBlockRegularity
universe u
namespace DaggerNativeWalkingPositiveBoundaryPushout
noncomputable section

theorem canonical_inner (n : ℕ) :
    innerAnodyne.{u} (relativePushout (SSet.boundary.{u} (n + 1)).ι).ι := by
  have hr := SSet.Subcomplex.range_ι (SSet.boundary.{u} (n + 1))
  change SSet.Subcomplex.range (SSet.boundary.{u} (n + 1)).ι = SSet.boundary (n + 1) at hr
  rw [relativePushout_ι]
  change innerAnodyne.{u}
    ((SSet.Subcomplex.range (SSet.boundary.{u} (n + 1)).ι).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).ι
  have hs : ∀ S : SSet.Subcomplex (Δ[n + 1] : SSet.{u}),
      S = SSet.boundary (n + 1) → innerAnodyne
        (S.unionProd DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).ι := by
    intro S hS
    subst S
    exact boundary_zero_innerAnodyne.{u} n
  exact hs _ hr

theorem pushout_inner (n : ℕ)
    (sq : SSet.PushoutTensor (SSet.boundary.{u} (n + 1)).ι zeroInclusion.{u}) :
    innerAnodyne sq.ι := by
  intro E T p hp
  have hh := canonical_inner.{u} n p hp
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (comparisonArrowIso (SSet.boundary (n + 1)).ι sq) p).mp hh

end
end DaggerNativeWalkingPositiveBoundaryPushout
