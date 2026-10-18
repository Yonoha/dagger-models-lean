import NativeWalkingEndpointSection
import NativeWalkingPositiveBoundaryPushout

/-! Endpoint evaluation into every native quasi-category is a full Kan trivial fibration. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingMonoPushout
open DaggerNativeWalkingEndpointSection DaggerNativeWalkingPositiveBoundaryPushout
open DaggerNativeInnerHornFactorization DaggerNativeInnerJoyalMappingWeak
open DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWalkingEndpointTrivialRestriction
noncomputable section

theorem positive_boundary_lifting (n : ℕ) (Z : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty (SSet.boundary.{u} (n + 1)).ι
      ((MonoidalClosed.pre zeroInclusion.{u}).app Z) := by
  let sq := relativePushout (SSet.boundary.{u} (n + 1)).ι
  let pb := terminalPullback zeroInclusion.{u} Z
  have hp : innerFibrations (terminal.from Z) :=
    (quasicategory_iff_inner_terminal _ terminalIsTerminal).mp inferInstance
  have hh : HasLiftingProperty (SSet.boundary.{u} (n + 1)).ι pb.π := by
    rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq.flip pb,
      HasLiftingProperty.iff_of_arrow_iso_left sq.flipArrowIso]
    exact canonical_inner n (terminal.from Z) hp
  simpa only [pb, terminalPullback_π] using hh

theorem boundary_lifting (Z : SSet.{u}) [Z.Quasicategory] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι ((MonoidalClosed.pre zeroInclusion.{u}).app Z) := by
  cases n with
  | zero => exact boundary_zero_lifting Z
  | succ n => exact positive_boundary_lifting n Z

theorem endpoint_mono_rlp (Z : SSet.{u}) [Z.Quasicategory] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((MonoidalClosed.pre zeroInclusion.{u}).app Z) :=
  boundary_rlp_monomorphisms _ (boundary_lifting Z)

theorem endpoint_trivial_fibration (Z : SSet.{u}) [Z.Quasicategory] :
    trivialFibrations SSet.{u} ((MonoidalClosed.pre zeroInclusion.{u}).app Z) :=
  (boundary_rlp_iff_trivialFibration _).mp (boundary_lifting Z)

end
end DaggerNativeWalkingEndpointTrivialRestriction
