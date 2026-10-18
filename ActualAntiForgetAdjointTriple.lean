import OriginalTaggedReverseFreeCompletion

/-!
# Both adjoints of the original anti-involutive forgetful functor

Right Kan extension along the original simplex inclusion gives the cofree object.
Transport uses the established original presheaf equivalence and restriction iso.
The central functor is exactly the existing antiForget in both adjunctions.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalTaggedReverseSimplex TaggedReverseSimplex
open DaggerModels.OriginalTaggedReversePresheafInclusion
open DaggerModels.OriginalTaggedReverseFreeCompletion
universe v u
namespace DaggerActualAntiForgetAdjointTriple
noncomputable section

private instance (A : SSet.{u}) :
    simplexInclusion.op.HasPointwiseRightKanExtension A := fun _ ↦ inferInstance

/-- The cofree object uses the original inclusion and the original anti-involutive equivalence. -/
def cofreeAnti : SSet.{u} ⥤ AntiInvolutiveSSet.{u} :=
  simplexInclusion.op.ran ⋙ TaggedPresheaf.toAntiInvolutive

/-- The original antiForget is left adjoint to this actual right Kan extension. -/
def cofreeAntiAdjunction : antiForget.{u} ⊣ cofreeAnti.{u} :=
  (antiInvolutiveEquivalence.{u}.toAdjunction.comp
    (simplexInclusion.op.ranAdjunction (Type u))).ofNatIsoLeft extensionRestrictionIso

instance forgetIsLeftAdjoint : antiForget.{u}.IsLeftAdjoint :=
  cofreeAntiAdjunction.isLeftAdjoint

instance forgetIsRightAdjoint : antiForget.{u}.IsRightAdjoint :=
  freeAntiAdjunction.isRightAdjoint

instance forgetPreservesColimits : PreservesColimitsOfSize.{v, v} antiForget.{u} :=
  cofreeAntiAdjunction.leftAdjoint_preservesColimits

instance forgetPreservesLimits : PreservesLimitsOfSize.{v, v} antiForget.{u} :=
  freeAntiAdjunction.rightAdjoint_preservesLimits

end
end DaggerActualAntiForgetAdjointTriple
