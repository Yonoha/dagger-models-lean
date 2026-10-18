import ActualFibrantGadgetData
import DaggerModels.RigidificationVertices

/-! The actual gadget unit preserves all vertices bijectively, with the original labels. -/

set_option autoImplicit false
open CategoryTheory Opposite DaggerModels OrdinaryRigidification
open OriginalOrdinaryLocalKanReplacement DaggerActualFibrantGadgetData
open scoped Simplicial
universe u

namespace DaggerActualFibrantGadgetVertices
noncomputable section

/-- The unit retains the original unit-based rigidification vertex and replacement object map. -/
theorem unit_vertex (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv (replacement.obj (rigidification.obj X))
      ((DaggerActualFibrantGadgetData.unit.app X).app (op ⦋0⦌) x) =
    (OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X)).obj
      (RigidificationVertices.vertexEquiv X x) := rfl

/-- The full degree-zero map is the composite of the original vertex identifications. -/
theorem unit_vertex_map (X : SSet.{u}) :
    (DaggerActualFibrantGadgetData.unit.app X).app (op ⦋0⦌) =
      (NerveVertices.vertexEquiv (replacement.obj (rigidification.obj X))).symm ∘
        (OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X)).obj ∘
          RigidificationVertices.vertexEquiv X := by
  funext x
  apply (NerveVertices.vertexEquiv (replacement.obj (rigidification.obj X))).injective
  rw [unit_vertex]
  exact (Equiv.apply_symm_apply _ _).symm

/-- Every original vertex occurs exactly once in the fibrant gadget, without type identification. -/
theorem unit_vertex_bijective (X : SSet.{u}) :
    Function.Bijective ((DaggerActualFibrantGadgetData.unit.app X).app (op ⦋0⦌)) := by
  rw [unit_vertex_map]
  exact (NerveVertices.vertexEquiv (replacement.obj (rigidification.obj X))).symm.bijective.comp
    ((unit_obj_bijective (rigidification.obj X)).comp
      (RigidificationVertices.vertexEquiv X).bijective)

end
end DaggerActualFibrantGadgetVertices
