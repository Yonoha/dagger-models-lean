import OriginalSimplicialCategoryBarVertexCylinder

/-!
# The original bar homotopy from precomposition to the source fibre

The zero endpoint includes the original precomposed Hom simplex and the one
endpoint includes the unchanged Hom simplex. The homotopy lies in the original
bar component and is defined on every original Hom simplex.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryBarVertexArrow
open DaggerOriginalSimplicialCategoryBarVertexCylinder
universe u
namespace DaggerOriginalSimplicialCategoryBarVertexHomotopy
noncomputable section

/-- The zero endpoint is exactly inclusion after original precomposition. -/
theorem barVertexCylinderMap_zero (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    SSet.ι₀ ≫ barVertexCylinderMap C a z =
      precomposeVertex C a z ≫ barHomInclusion C x z := by
  apply NatTrans.ext
  funext n b
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro k l f
  rfl

/-- The one endpoint is exactly the original unchanged Hom inclusion. -/
theorem barVertexCylinderMap_one (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    SSet.ι₁ ≫ barVertexCylinderMap C a z = barHomInclusion C y z := by
  apply NatTrans.ext
  funext n b
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro k l f
  rfl

/-- The full original precomposition has its actual directed homotopy in the original bar. -/
def barVertexHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    SSet.Homotopy (precomposeVertex C a z ≫ barHomInclusion C x z)
      (barHomInclusion C y z) :=
  SSet.Homotopy.mk (barVertexCylinderMap C a z) (barVertexCylinderMap_zero C a z)
    (barVertexCylinderMap_one C a z)

end
end DaggerOriginalSimplicialCategoryBarVertexHomotopy
