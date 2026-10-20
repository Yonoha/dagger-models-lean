import OriginalOrdinaryGraphColimit
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Object and degreewise total-edge colimits of ordinary graph colimits

The graph cocone's object and total-edge images are colimiting.  Evaluating
its total-edge image in any simplex degree gives the literal Type colimit of
the original total edges in that degree.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.SimplicialGraph.TotalSpace.Colimit

variable {J : Type u} [SmallCategory J] (F : J ⥤ SimplicialGraph.{u})

/-- The object part of the graph cocone is the original Type colimit cocone. -/
noncomputable def objectIsColimit : IsColimit (objectCocone F (cocone F)) where
  desc s := colimit.desc (objectDiagram F) s
  fac s j := colimit.ι_desc s j
  uniq s m hm := by
    apply colimit.hom_ext
    intro j
    exact (hm j).trans (colimit.ι_desc s j).symm

/-- The total edges of the graph point are the original total-edge colimit. -/
noncomputable def totalEdgeIsColimit :
    IsColimit (TotalSpace.edgeFunctor.mapCocone (cocone F)) where
  desc s := project F ≫ colimit.desc (edgeDiagram F) s
  fac s j := by
    calc
      TotalSpace.edgeMap (leg F j) ≫
          (project F ≫ colimit.desc (edgeDiagram F) s) =
        (edgeι F j ≫ reconstruct F) ≫
          (project F ≫ colimit.desc (edgeDiagram F) s) := by
            rw [reconstruct_ι]
      _ = edgeι F j ≫
          ((reconstruct F ≫ project F) ≫ colimit.desc (edgeDiagram F) s) := by
            simp only [Category.assoc]
      _ = edgeι F j ≫ colimit.desc (edgeDiagram F) s := by
            rw [reconstruct_project, Category.id_comp]
      _ = s.ι.app j := colimit.ι_desc s j
  uniq s m hm := by
    have he : reconstruct F ≫ m = colimit.desc (edgeDiagram F) s := by
      apply colimit.hom_ext
      intro j
      change (edgeι F j ≫ reconstruct F) ≫ m =
        edgeι F j ≫ colimit.desc (edgeDiagram F) s
      rw [reconstruct_ι F j]
      exact (hm j).trans (colimit.ι_desc s j).symm
    calc
      m = (project F ≫ reconstruct F) ≫ m := by
        rw [project_reconstruct, Category.id_comp]
      _ = project F ≫ (reconstruct F ≫ m) := Category.assoc _ _ _
      _ = project F ≫ colimit.desc (edgeDiagram F) s := by rw [he]

/-- The raw Type diagram of original total edges in simplex degree `n`. -/
def degreeDiagram (n : SimplexCategoryᵒᵖ) : J ⥤ Type u :=
  edgeDiagram F ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n

/-- The graph cocone is colimiting on total edges in every simplex degree. -/
noncomputable def degreeIsColimit (n : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone
      (TotalSpace.edgeFunctor.mapCocone (cocone F))) :=
  isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
    (totalEdgeIsColimit F)

/-- The canonical comparison to the explicit degreewise Type colimit. -/
noncomputable def degreeIso (n : SimplexCategoryᵒᵖ) :
    (totalEdges F).obj n ≅ colimit (degreeDiagram F n) :=
  colimitObjIsoColimitCompEvaluation (edgeDiagram F) n

/-- The comparison remembers each original total edge exactly. -/
theorem degreeIso_ι (j : J) (n : SimplexCategoryᵒᵖ) :
    colimit.ι (degreeDiagram F n) j ≫ (degreeIso F n).inv = (edgeι F j).app n :=
  colimitObjIsoColimitCompEvaluation_ι_inv (edgeDiagram F) j n

end DaggerModels.SimplicialGraph.TotalSpace.Colimit
