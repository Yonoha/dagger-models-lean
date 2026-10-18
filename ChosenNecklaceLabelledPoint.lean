import ChosenNecklaceCanonicalObjects
import ChosenNecklaceIntervalSingle

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

def pointComparison : LabelledComparison.{u} point := by
  rw [← code_eq_point_of_zero (single 0) rfl]
  exact singleComparison 0

theorem LabelledComparison.inverse_object {T : NecklaceCode} (S : LabelledComparison.{u} T)
    (b : (NC.{u} T).Obj) :
    S.iso.inv.obj b = RV T.toSSet (T.verticesEquiv.symm b.as) := by
  have h : S.iso.hom.obj (RV T.toSSet (T.verticesEquiv.symm b.as)) = b := by
    rw [S.objects, canonicalNCObject_vertex, Equiv.apply_symm_apply]
    rfl
  have hi := congrArg S.iso.inv.obj h
  have hh := congrArg (fun F ↦ F.obj (RV T.toSSet (T.verticesEquiv.symm b.as)))
    S.iso.hom_inv_id
  exact hi.symm.trans hh

theorem point_vertex_unique (x y : (Δ[0] : SSet.{u}).obj (op ⦋0⦌)) : x = y :=
  (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm

theorem pointAt_zero (T : NecklaceCode) (v : Vertices.{u} T) :
    (pointAt T v).app (op ⦋0⦌) (point.verticesEquiv.symm pointObj.as) =
      T.verticesEquiv.symm v := by
  rw [← pointAt_vertex T v]
  change (pointAt T v).app _ _ = (pointAt T v).app _ _
  exact congrArg ((pointAt T v).app (op ⦋0⦌)) (point_vertex_unique _ _)

/-- Whole point-leg compatibility; arbitrary target Hom data are forced by its same object. -/
theorem LabelledComparison.point_leg {T : NecklaceCode} (S : LabelledComparison.{u} T)
    (v : Vertices.{u} T) :
    C.map (pointAt T v) ≫ S.iso.hom =
      pointComparison.iso.hom ≫ pointNCFunctor (NC T) ⟨v⟩ := by
  apply (cancel_epi pointComparison.iso.inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply pointNCFunctor_ext
  change S.iso.hom.obj ((C.map (pointAt T v)).obj
    (pointComparison.iso.inv.obj pointObj)) = ⟨v⟩
  rw [LabelledComparison.inverse_object]
  change S.iso.hom.obj ((C.map (pointAt T v)).obj
    (RV (Δ[0] : SSet.{u}) (point.verticesEquiv.symm pointObj.as))) = ⟨v⟩
  rw [DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality,
    pointAt_zero, S.objects, canonicalNCObject_vertex, Equiv.apply_symm_apply]

end

end DaggerChosenRigidificationNecklace
