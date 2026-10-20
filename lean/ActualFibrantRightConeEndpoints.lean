import ActualFibrantRightConeContractibility
import OriginalCounitRightConeRetractionHomFactorizationReconciled

/-! Discharge nonemptiness at the two original right-cone endpoints after the actual gadget unit. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRetractionHomFactorization
open DaggerOriginalEnrichedHomTransport DaggerActualRigidificationDirectedIntervalObjects
open DaggerOriginalCounitRightConeRelativeHomotopy DaggerOrdinaryTranslation
open DaggerChosenRigidificationNecklace
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerActualFibrantGadgetData
universe u

namespace DaggerActualFibrantRightConeEndpoints
noncomputable section

/-- The actual last-edge rigidification retains the initial cone object. -/
theorem lastEdge_alpha_obj (n : ℕ) :
    (rigidification.map (lastEdge.{u} n)).obj (endpoint 0) = alphaObj n := by
  rw [endpoint, RigidificationVertices.vertexEquiv_naturality]
  change RigidificationVertices.vertexEquiv (cone n)
    ((lastEdge n).app (op ⦋0⦌) vertexZero) =
      RigidificationVertices.vertexEquiv (cone n) (alpha n)
  rw [lastEdge_zero]

/-- The same actual last-edge rigidification retains the terminal cone object. -/
theorem lastEdge_omega_obj (n : ℕ) :
    (rigidification.map (lastEdge.{u} n)).obj (endpoint 1) = omegaObj n := by
  rw [endpoint, RigidificationVertices.vertexEquiv_naturality]
  change RigidificationVertices.vertexEquiv (cone n)
    ((lastEdge n).app (op ⦋0⦌) vertexOne) =
      RigidificationVertices.vertexEquiv (cone n) (omega n)
  rw [lastEdge_one]

/-- The original cone's prescribed endpoint Hom contains an actual vertex. -/
def endpoint_vertex (n : ℕ) :
    (alphaObj.{u} n ⟶[SSet.{u}] omegaObj.{u} n).obj (op ⦋0⦌) :=
  ((rigidification.map (lastEdge n)).map (endpoint 0) (endpoint 1) ≫
    targetHomTransport (lastEdge_alpha_obj n) (lastEdge_omega_obj n)).app (op ⦋0⦌) edge

/-- The selected endpoint Hom of C(F(cone[n])) is weakly contractible, without premises.
Both endpoints are the literal images under C of the original gadget unit. -/
theorem endpoint_hom_toUnit_GW (n : ℕ) :
    DaggerSSetGluing.GW (toUnit
      ((rigidification.map (DaggerActualFibrantGadgetData.unit.app (cone.{u} n))).obj
          (alphaObj n) ⟶[SSet.{u}]
        (rigidification.map (DaggerActualFibrantGadgetData.unit.app (cone.{u} n))).obj
          (omegaObj n))) := by
  apply DaggerActualFibrantRightConeContractibility.cone_gadget_hom_toUnit_GW
  exact ⟨((rigidification.map (DaggerActualFibrantGadgetData.unit.app (cone n))).map
    (alphaObj n) (omegaObj n)).app (op ⦋0⦌) (endpoint_vertex n)⟩

end
end DaggerActualFibrantRightConeEndpoints
