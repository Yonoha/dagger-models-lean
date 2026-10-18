import ActualFreeAntiWalkingCategoricalCylinder

/-!
# A categorical interval retraction for the literal whole tagged walking generator

The original freeAnti map has an actual anti-involutive retraction. Its opposite
underlying composite contracts through the original walking-isomorphism interval
on every simplex of both copies. No Joyal or DCH model hypothesis is supplied.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualTaggedWalkingIsoImageDKObstruction
open DaggerActualTaggedWalkingIsoSourceHomotopy
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualFreeAntiWalkingCategoricalCylinder
universe u
namespace DaggerActualTaggedWalkingCategoricalRetraction
noncomputable section

/-- The inverse is the literal original freeAnti image of the old collapse. -/
def taggedCollapse : freeAnti.obj J.{u} ⟶ freeAnti.obj (Δ[0] : SSet.{u}) :=
  freeAnti.map collapse

/-- The original whole generator and inverse form an actual anti-involutive retraction. -/
theorem taggedGenerator_retraction : taggedGenerator.{u} ≫ taggedCollapse.{u} = 𝟙 _ := by
  change freeAnti.map zeroInclusion ≫ freeAnti.map collapse = _
  rw [← freeAnti.map_comp, zeroInclusion_collapse, freeAnti.map_id]

/-- The first original endpoint equation in the general cylinder notation. -/
theorem original_endpoint_zero :
    intervalEndpoint J.{u} false ≫ cylinder.{u} = collapse.{u} ≫ zeroInclusion.{u} := by
  rw [intervalEndpoint, ← endpoint_eq_lift]
  exact endpoint_zero_cylinder

/-- The second original endpoint equation in the same general notation. -/
theorem original_endpoint_one : intervalEndpoint J.{u} true ≫ cylinder.{u} = 𝟙 J.{u} := by
  rw [intervalEndpoint, ← endpoint_eq_lift]
  exact endpoint_one_cylinder

/-- The full cylinder lives on the actual freeAnti target, including its reversed copy. -/
def taggedCylinder :
    (freeAnti.obj J.{u}).toSSet ⊗ J.{u} ⟶ (freeAnti.obj J.{u}).toSSet :=
  freeCylinder cylinder

/-- At the original zero endpoint the whole cylinder is the inverse-forward composite. -/
theorem taggedCylinder_zero :
    intervalEndpoint (freeAnti.obj J.{u}).toSSet false ≫ taggedCylinder.{u} =
      taggedCollapse.{u}.hom ≫ taggedGenerator.{u}.hom := by
  rw [taggedCylinder, freeCylinder_endpoint cylinder false (collapse ≫ zeroInclusion)
    original_endpoint_zero, freeAnti.map_comp]
  rfl

/-- At the original one endpoint the whole cylinder is the exact identity. -/
theorem taggedCylinder_one :
    intervalEndpoint (freeAnti.obj J.{u}).toSSet true ≫ taggedCylinder.{u} =
      𝟙 (freeAnti.obj J.{u}).toSSet := by
  rw [taggedCylinder, freeCylinder_endpoint cylinder true (𝟙 J) original_endpoint_one,
    freeAnti.map_id]
  rfl

end
end DaggerActualTaggedWalkingCategoricalRetraction
