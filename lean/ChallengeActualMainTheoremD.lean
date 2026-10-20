import ActualTaggedNonQuillenForExactDCHClasses
import NativeJoyalFirstFactorization

/-! Fixed problem: construct the exact source model and prove both original non-Quillen claims. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalTaggedReverseAdjunctions
universe u
namespace ChallengeActualMainTheoremD

def Statement : Prop := ∃ M : ModelCategory AntiInvolutiveSSet.{u},
  letI : ModelCategory AntiInvolutiveSSet.{u} := M
  letI : ModelCategory DaggerSSet.{u} := DaggerActualRigidificationQuillen.modelD.{u}
  (∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
    Cofibration f ↔ AntiInvolutiveSSet.NormalMono f) ∧
  (∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
    WeakEquivalence f ↔ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f) ∧
  (∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
    Fibration f ↔ DaggerNativeJoyalFirstFactorization.candidateFibrations f.hom) ∧
  (¬ leftAdjunction.{u}.IsQuillenAdjunction ∧ ¬ rightAdjunction.{u}.IsQuillenAdjunction) ∧
  (¬ ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y), Cofibration f ↔ Cofibration
    (DaggerModels.OriginalTaggedReversePresheafInclusion.presheafRoute.map f))

end ChallengeActualMainTheoremD
