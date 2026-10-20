import TerminalArrowConnectedColimits
import NativeInnerFactorizationAccessible
import ActualAntiInnerFactorizationAccessible

/-!
# Finite accessibility of both original whole quasi-category replacements

The original replacement functors are unchanged. Their terminal-arrow factors
are definitionally the generic connected-colimit preserving terminal-arrow
functor, and their original aleph-zero small-object middle factors are accessible.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerTerminalArrowConnectedColimits
universe u
namespace DaggerOriginalQuasiReplacementsAccessible
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance nativeReplacementAccessible :
    Functor.IsCardinalAccessible DaggerNativeInnerHornFactorization.replacement.{u}
      Cardinal.aleph0.{u} := by
  change Functor.IsCardinalAccessible
    (toTerminalArrow SSet.{u} ⋙ DaggerNativeInnerHornFactorization.factorization.Z)
    Cardinal.aleph0.{u}
  infer_instance

instance actualReplacementAccessible :
    DaggerActualAntiInnerHornFactorization.replacement.{u}.IsCardinalAccessible
      Cardinal.aleph0.{u} := by
  change (toTerminalArrow AntiInvolutiveSSet.{u} ⋙
    DaggerActualAntiInnerHornFactorization.factorization.Z).IsCardinalAccessible Cardinal.aleph0.{u}
  infer_instance

instance actualUnderlyingReplacementAccessible :
    Functor.IsCardinalAccessible
      (DaggerActualAntiInnerHornFactorization.replacement.{u} ⋙ antiForget)
      Cardinal.aleph0.{u} := by infer_instance

instance nativePreservesFiltered (J : Type u) [SmallCategory J] [IsFiltered J] :
    Limits.PreservesColimitsOfShape J DaggerNativeInnerHornFactorization.replacement.{u} := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ Cardinal.aleph0.{u} J

instance actualPreservesFiltered (J : Type u) [SmallCategory J] [IsFiltered J] :
    Limits.PreservesColimitsOfShape J DaggerActualAntiInnerHornFactorization.replacement.{u} := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ Cardinal.aleph0.{u} J

end
end DaggerOriginalQuasiReplacementsAccessible
