import ActualInnerIteratedGadgetData
import ActualInnerNecklaceMappingContractible
import ActualIteratedGadgetProperties
import ActualGeneralRightConeRigidificationLeg

/-! BOTH original Hom weights and actual right mappings stay contractible in the NEW G family.
Only level ZERO is reused from the old N R Rig family; positive levels use the SAME native G.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerNativeInnerHornFactorization
open DaggerActualInnerIteratedGadgetData DaggerActualGeneralRightConeMapping
open DaggerActualRightMappingWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerIteratedGadgetProperties
noncomputable section

def endpointHom (P : BaseCode) (k : ℕ) : SSet.{u} :=
  DaggerActualGeneralRightConeRigidificationLeg.originalHom (spaceAt P k)
    (alphaAt P k) (omegaAt P k)

def homStep (P : BaseCode) (k : ℕ) : endpointHom.{u} P k ⟶ endpointHom P (k + 1) :=
  DaggerActualGeneralRightConeRigidificationLeg.homMap (spaceAt P k) (alphaAt P k)
    (omegaAt P k) (unit.app (spaceAt P k))

theorem homStep_weak (P : BaseCode) (k : ℕ) : WeakEquivalence (homStep.{u} P k) := by
  have : WeakEquivalence ((rigidification.map (unit.app (spaceAt P k))).map
      (RigidificationVertices.vertexEquiv (spaceAt P k) (alphaAt P k))
      (RigidificationVertices.vertexEquiv (spaceAt P k) (omegaAt P k))) :=
    DaggerActualInnerReplacementExtensions.unit_hom_weak _ _ _
  unfold homStep DaggerActualGeneralRightConeRigidificationLeg.homMap
    DaggerModels.OriginalOrdinaryMovingHomColimits.castMap
    OriginalOrdinaryEndpointTransport.transport
  infer_instance

theorem endpoint_hom_toUnit_weak (P : BaseCode) (k : ℕ) :
    WeakEquivalence (toUnit (endpointHom.{u} P k)) := by
  induction k with
  | zero =>
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedGadgetProperties.endpoint_hom_GW ⟨P, 0⟩)
  | succ k ih =>
    have : WeakEquivalence (homStep.{u} P k) := homStep_weak P k
    have he : homStep P k ≫ toUnit (endpointHom P (k + 1)) =
        toUnit (endpointHom P k) := isTerminalTensorUnit.hom_ext _ _
    have : WeakEquivalence (homStep P k ≫ toUnit (endpointHom P (k + 1))) := by
      rw [he]
      exact ih
    exact weakEquivalence_of_precomp (homStep P k) (toUnit (endpointHom P (k + 1)))

theorem positive_quasicategory (P : BaseCode) (k : ℕ) :
    (spaceAt.{u} P (k + 1)).Quasicategory := replacement_quasicategory (spaceAt P k)

theorem positive_mapping_kan (P : BaseCode) (k : ℕ) :
    (rightMapping (spaceAt.{u} P (k + 1)) (alphaAt P (k + 1))
      (omegaAt P (k + 1))).KanComplex := by
  have : (spaceAt.{u} P (k + 1)).Quasicategory := positive_quasicategory P k
  exact DaggerActualGeneralRightConeKan.rightMapping_kan _ _ _

theorem positive_mapping_toUnit_weak (P : BaseCode) (k : ℕ) : WeakEquivalence
    (toUnit (rightMapping (spaceAt.{u} P (k + 1)) (alphaAt P (k + 1))
      (omegaAt P (k + 1)))) := by
  induction k with
  | zero =>
    cases P with
    | inl T =>
      exact DaggerActualInnerNecklaceMappingContractible.innerNecklace_mapping_toUnit_weak T
    | inr n => exact DaggerActualInnerConeRightMappingContractible.innerCone_mapping_toUnit_weak n
  | succ k ih =>
    have : (spaceAt.{u} P (k + 1)).Quasicategory := positive_quasicategory P k
    have : (spaceAt.{u} P (k + 1 + 1)).Quasicategory := positive_quasicategory P (k + 1)
    let f : spaceAt.{u} P (k + 1) ⟶ spaceAt P (k + 1 + 1) :=
      unit.app (spaceAt P (k + 1))
    let a := alphaAt.{u} P (k + 1)
    let b := omegaAt.{u} P (k + 1)
    let Y := rightMapping (spaceAt.{u} P (k + 1 + 1)) (alphaAt P (k + 1 + 1))
      (omegaAt P (k + 1 + 1))
    have : WeakEquivalence (map f a b) :=
      map_weak_of_categorical_weak f
        (DaggerNativeInnerJoyalMappingWeak.unit_weak (spaceAt P (k + 1))) a b
    have he : map f a b ≫ toUnit Y = toUnit (rightMapping (spaceAt P (k + 1)) a b) :=
      isTerminalTensorUnit.hom_ext _ _
    have : WeakEquivalence (map f a b ≫ toUnit Y) := by
      rw [he]
      exact ih
    exact weakEquivalence_of_precomp (map f a b) (toUnit Y)

theorem endpoint_hom_GW (P : Code) : DaggerSSetGluing.GW
    (toUnit (endpointHom.{u} P.base P.level)) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mp (endpoint_hom_toUnit_weak P.base P.level)

end
end DaggerActualInnerIteratedGadgetProperties
