import NativeMonoRestrictionParameterizedWalkingLifting

/-! All original mono restrictions lift every relative original zero-J cylinder. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingRelativeGenerators
open DaggerNativeWalkingMonoPushout DaggerNativeMonoRestrictionWalkingLifting
open DaggerNativeInnerJoyalMappingWeak
universe u
namespace DaggerNativeMonoRestrictionRelativeWalkingLifting
noncomputable section

theorem union_zero_terminal_lifting {X : SSet.{u}} (S : X.Subcomplex)
    (Z : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty (S.unionProd zeroSubcomplex.{u}).ι (terminal.from Z) := by
  have hh := pushout_zero_lifting S.ι Z (relativePushout S.ι)
  rw [relativePushout_ι] at hh
  have hr := SSet.Subcomplex.range_ι S
  change SSet.Subcomplex.range S.ι = S at hr
  let P : X.Subcomplex → Prop := fun T ↦
    HasLiftingProperty (T.unionProd zeroSubcomplex.{u}).ι (terminal.from Z)
  exact (congrArg P hr).mp hh

theorem restriction_union_zero_lifting {X Y : SSet.{u}}
    (S : X.Subcomplex) (T : Y.Subcomplex) (Z : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty (T.unionProd zeroSubcomplex.{u}).ι
      ((MonoidalClosed.pre S.ι).app Z) := by
  let sq := SSet.PushoutTensor.unionProd S (T.unionProd zeroSubcomplex.{u})
  let pb := terminalPullback S.ι Z
  have hA := union_zero_terminal_lifting (S.unionProd T) Z
  have hB : HasLiftingProperty (S.unionProd (T.unionProd zeroSubcomplex.{u})).ι
      (terminal.from Z) :=
    (HasLiftingProperty.iff_of_arrow_iso_left
      (SSet.Subcomplex.unionProd.assocArrowIso S T zeroSubcomplex.{u}) _).mp hA
  have hC : HasLiftingProperty sq.ι (terminal.from Z) := by
    simpa only [sq, SSet.PushoutTensor.ι_unionProd] using hB
  have hh := (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq pb).mp hC
  simpa only [pb, terminalPullback_π] using hh

def rangeRestrictionArrowIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (Z : SSet.{u}) :
    Arrow.mk ((MonoidalClosed.pre (SSet.Subcomplex.range i).ι).app Z) ≅
      Arrow.mk ((MonoidalClosed.pre i).app Z) :=
  Arrow.isoMk (Iso.refl _)
    ((MonoidalClosed.internalHom.mapIso (rangeIso i).op).app Z) (by
      change (MonoidalClosed.pre i).app Z =
        (MonoidalClosed.pre (SSet.Subcomplex.range i).ι).app Z ≫
          (MonoidalClosed.pre (rangeIso i).hom).app Z
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, rangeIso_hom_ι])

theorem restriction_relative_zero_lifting {A B K L : SSet.{u}}
    (i : A ⟶ B) [Mono i] (j : K ⟶ L) [Mono j] (Z : SSet.{u}) [Z.Quasicategory]
    (sq : SSet.PushoutTensor j zeroInclusion.{u}) :
    HasLiftingProperty sq.ι ((MonoidalClosed.pre i).app Z) := by
  have hR := restriction_union_zero_lifting (SSet.Subcomplex.range i)
    (SSet.Subcomplex.range j) Z
  have hZ : HasLiftingProperty ((SSet.Subcomplex.range j).unionProd zeroSubcomplex.{u}).ι
      ((MonoidalClosed.pre i).app Z) :=
    (HasLiftingProperty.iff_of_arrow_iso_right _ (rangeRestrictionArrowIso i Z)).mp hR
  have hC : HasLiftingProperty (relativePushout j).ι ((MonoidalClosed.pre i).app Z) := by
    rw [relativePushout_ι]
    exact hZ
  exact (HasLiftingProperty.iff_of_arrow_iso_left (comparisonArrowIso j sq) _).mp hC

end
end DaggerNativeMonoRestrictionRelativeWalkingLifting
