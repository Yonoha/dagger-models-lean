import ChosenNecklaceCutComparison

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) (j : Fin (T.len + 1))

theorem cutNCInclusion_left_vertex (y : (toSSet.{u} (cutLeft T j)).obj (op ⦋0⦌)) :
    (cutNCInclusion T j false).obj ⟨(cutLeft T j).verticesEquiv y⟩ =
      ⟨T.verticesEquiv ((cutLeftι T j).app _ y)⟩ := by
  apply congrArg NecklaceThickening.mk
  have h := intervalι_vertices T 0 j (Fin.zero_le j) ((cutLeft T j).verticesEquiv y)
  simpa only [mapVertices, Equiv.symm_apply_apply] using h.symm

theorem cutNCInclusion_right_vertex (y : (toSSet.{u} (cutRight T j)).obj (op ⦋0⦌)) :
    (cutNCInclusion T j true).obj ⟨(cutRight T j).verticesEquiv y⟩ =
      ⟨T.verticesEquiv ((cutRightι T j).app _ y)⟩ := by
  apply congrArg NecklaceThickening.mk
  have h := intervalι_vertices T j (Fin.last T.len) (Fin.le_last j)
    ((cutRight T j).verticesEquiv y)
  simpa only [mapVertices, Equiv.symm_apply_apply] using h.symm

variable (hj : j ∈ T.joints) (L : LabelledComparison.{u} (cutLeft T j))
variable (R : LabelledComparison.{u} (cutRight T j))

theorem cutChosenIso_objects (a : (C.{u}.obj T.toSSet).Obj) :
    (cutChosenIso T j hj L R).hom.obj a = canonicalNCObject T a := by
  obtain ⟨x, rfl⟩ := (RV T.toSSet).surjective a
  rw [canonicalNCObject_vertex]
  rcases cut_degree_cover T j hj x with ⟨y, hy⟩ | ⟨y, hy⟩
  · have h := congrArg (fun F ↦ F.obj (RV (toSSet (cutLeft T j)) y))
      (cutChosenIso_left T j hj L R)
    change (cutChosenIso T j hj L R).hom.obj
      ((C.map (cutLeftι T j)).obj (RV _ y)) =
      (cutNCInclusion T j false).obj (L.iso.hom.obj (RV _ y)) at h
    rw [DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality,
      hy, L.objects, canonicalNCObject_vertex, cutNCInclusion_left_vertex, hy] at h
    exact h
  · have h := congrArg (fun F ↦ F.obj (RV (toSSet (cutRight T j)) y))
      (cutChosenIso_right T j hj L R)
    change (cutChosenIso T j hj L R).hom.obj
      ((C.map (cutRightι T j)).obj (RV _ y)) =
      (cutNCInclusion T j true).obj (R.iso.hom.obj (RV _ y)) at h
    rw [DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality,
      hy, R.objects, canonicalNCObject_vertex, cutNCInclusion_right_vertex, hy] at h
    exact h

def cutComparison : LabelledComparison.{u} T where
  iso := cutChosenIso T j hj L R
  objects := cutChosenIso_objects T j hj L R

end

end DaggerChosenRigidificationNecklace
