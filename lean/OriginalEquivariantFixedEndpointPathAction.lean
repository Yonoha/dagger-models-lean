import OriginalEC2EndpointCylinders
import OriginalUnitaryPathMapNaturality

/-!
# The original pointwise action on paths between fixed endpoints

The path space carries exactly pointwise postcomposition by the original continuous action.
Both original endpoints are fixed points. In particular, the time parameter is unchanged.
The action is jointly continuous by the existing discrete topology on the original group C₂.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEquivariantConstantMaps DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalContinuousEndpointCylinderFamilies DaggerOriginalLabeledPathFiberNaturality

universe u

namespace DaggerOriginalEquivariantFixedEndpointPathAction

noncomputable section

/-- The original group element acts pointwise on the original continuous path. -/
def pathActionEnd (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X) (g : C2.{u}) :
    End (continuousPathTop X.obj.V a.val b.val) :=
  End.of (labeledContinuousPathTopMap (X.obj.ρ g).asHom a.val b.val a.val b.val
    (a.property g) (b.property g))

/-- The pointwise path action of the same original group on the same original path space. -/
def pathAction (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X) :
    Action TopCat.{u} C2.{u} where
  V := continuousPathTop X.obj.V a.val b.val
  ρ :=
    { toFun := pathActionEnd X a b
      map_one' := by
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro p
        apply Path.ext
        funext t
        exact ConcreteCategory.congr_hom
          (congrArg End.asHom X.obj.ρ.map_one) (p.toContinuousMap t)
      map_mul' g h := by
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro p
        apply Path.ext
        funext t
        exact ConcreteCategory.congr_hom
          (congrArg End.asHom (X.obj.ρ.map_mul g h)) (p.toContinuousMap t) }

/-- Joint continuity uses the same original discrete C₂ and the continuous path maps. -/
theorem pathAction_isContinuous (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X) :
    (pathAction X a b).IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact ((pathAction X a b).ρ g).asHom.hom.continuous

/-- The same pointwise action regarded as a continuous action. -/
def continuousPathAction (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X) :
    ContAction TopCat.{u} C2.{u} :=
  ⟨pathAction X a b, pathAction_isContinuous X a b⟩

/-- Evaluation retains exactly the original pointwise action and original time. -/
theorem continuousPathAction_apply (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X)
    (g : C2.{u}) (p : (continuousPathAction X a b).obj.V) (t : unitInterval) :
    (((continuousPathAction X a b).obj.ρ g).asHom p).toContinuousMap t =
      (X.obj.ρ g).asHom (p.toContinuousMap t) := rfl

end

end DaggerOriginalEquivariantFixedEndpointPathAction
