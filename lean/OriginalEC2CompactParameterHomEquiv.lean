import OriginalEquivariantParameterTensor

/-!
# The original EC₂ tensor and mapping-space correspondence

The domain is the literal realization of the original codiscrete C₂ nerve.
For generated locally compact parameters, equivariant maps from its ordinary
product correspond to maps into the original compact-open mapping space.
Both parameter and target naturality refer to the exact original arrows.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalCompactGeneration DaggerOriginalEquivariantCompactParameterCurry
open DaggerOriginalEquivariantParameterTensor

universe u

namespace DaggerOriginalEC2CompactParameterHomEquiv

noncomputable section

/-- The original realized EC₂ has the native compact-generated topology. -/
instance originalEC2_generated :
    IsGeneratedBy compactHausFamily.{u} realizedEC2ContinuousAction.{u}.obj.V := by
  change IsGeneratedBy compactHausFamily.{u}
    (SSet.toTop.obj DaggerOriginalEC2SimplicialAction.simplicialEC2.{u})
  infer_instance

/-- The actual EC₂ product action, with trivial parameter action. -/
abbrev originalEC2Tensor (K : TopCat.{u}) : Action TopCat.{u} C2.{u} :=
  parameterTensor realizedEC2ContinuousAction K

/-- The original EC₂ product arrow induced by the actual parameter map. -/
abbrev originalEC2TensorMap {K L : TopCat.{u}} (i : K ⟶ L) :
    originalEC2Tensor K ⟶ originalEC2Tensor L :=
  parameterTensorMap realizedEC2ContinuousAction i

/-- Equivariant maps from original EC₂ products correspond to the literal compact-open families. -/
def originalEC2HomEquiv (K : TopCat.{u})
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (X : ContAction TopCat.{u} C2.{u}) :
    (originalEC2Tensor K ⟶ X.obj) ≃ (K ⟶ mappingTop X) where
  toFun f := TopCat.ofHom
    (equivariantCurryEquiv realizedEC2ContinuousAction X K
      (equivariantProductHomEquiv realizedEC2ContinuousAction X K f))
  invFun f := (equivariantProductHomEquiv realizedEC2ContinuousAction X K).symm
    ((equivariantCurryEquiv realizedEC2ContinuousAction X K).symm f.hom)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original hom equivalence retains evaluation at the original EC₂ point. -/
theorem originalEC2HomEquiv_apply (K : TopCat.{u})
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (X : ContAction TopCat.{u} C2.{u}) (f : originalEC2Tensor K ⟶ X.obj)
    (k : K) (e : realizedEC2ContinuousAction.{u}.obj.V) :
    (originalEC2HomEquiv K X f k).val e = f.hom (e, k) := rfl

/-- Naturality is literal precomposition by the original product arrow. -/
theorem originalEC2HomEquiv_parameter_naturality {K L : TopCat.{u}}
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    [IsGeneratedBy compactHausFamily.{u} L] [LocallyCompactSpace L]
    (X : ContAction TopCat.{u} C2.{u}) (i : K ⟶ L) (f : originalEC2Tensor L ⟶ X.obj) :
    originalEC2HomEquiv K X (originalEC2TensorMap i ≫ f) =
      i ≫ originalEC2HomEquiv L X f := by
  ext k
  rfl

/-- Naturality in the action is literal postcomposition on the original compact-open subtype. -/
theorem originalEC2HomEquiv_target_naturality (K : TopCat.{u})
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    {X Y : ContAction TopCat.{u} C2.{u}} (p : X ⟶ Y) (f : originalEC2Tensor K ⟶ X.obj) :
    originalEC2HomEquiv K Y (f ≫ p.hom) = originalEC2HomEquiv K X f ≫ postcompose p := by
  ext k
  rfl

end

end DaggerOriginalEC2CompactParameterHomEquiv
