import OriginalCounitRightConeQLatchingReconciled

/-!
# Literal face legs of the actual Q boundary comparison

This is an unconditional step toward monicity of `boundaryQMap`. It identifies
all codimension-one face legs with the original cosimplicial Q maps. The
intersection/normal-form theorem needed for monicity is not supplied here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQLatching

universe u

namespace DaggerOriginalCounitRightConeQBoundaryMono

noncomputable section

private instance : SSet.stdSimplex.{u}.Faithful :=
  inferInstanceAs (uliftYoneda.{u} (C := SimplexCategory)).Faithful

/-- The literal codimension-one face is contained in the standard boundary. -/
theorem face_le_boundary (k : ℕ) (i : Fin (k + 2)) :
    SSet.stdSimplex.face.{u} {i}ᶜ ≤ SSet.boundary.{u} (k + 1) := by
  rw [SSet.boundary_eq_iSup]
  exact le_iSup_of_le i le_rfl

/-- The standard face map, now valued in the actual boundary subcomplex. -/
def faceInBoundary (k : ℕ) (i : Fin (k + 2)) :
    (Δ[k] : SSet.{u}) ⟶ (∂Δ[k + 1] : SSet.{u}) :=
  (SSet.stdSimplex.faceSingletonComplIso.{u} i).hom ≫
    SSet.Subcomplex.homOfLE (face_le_boundary.{u} k i)

/-- Following boundary inclusion recovers the original standard face map. -/
theorem faceInBoundary_inclusion (k : ℕ) (i : Fin (k + 2)) :
    faceInBoundary.{u} k i ≫ (∂Δ[k + 1]).ι = SSet.stdSimplex.δ i := by
  dsimp only [faceInBoundary]
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  exact SSet.stdSimplex.faceSingletonComplIso_hom_ι i

/-- The corresponding object of the actual boundary-simplex index category. -/
def faceBoundaryIndex (k : ℕ) (i : Fin (k + 2)) :
    SimplexIndex (∂Δ[k + 1] : SSet.{u}) :=
  CostructuredArrow.mk (faceInBoundary.{u} k i)

/-- Its operator is the exact ordinary face operator, in every universe. -/
theorem boundaryOperator_face (k : ℕ) (i : Fin (k + 2)) :
    boundaryOperator.{u} (k + 1) (faceBoundaryIndex.{u} k i) =
      SimplexCategory.δ i := by
  apply SSet.stdSimplex.{u}.map_injective
  rw [boundaryOperator_image]
  change faceInBoundary.{u} k i ≫ (∂Δ[k + 1]).ι =
    SSet.stdSimplex.{u}.map (SimplexCategory.δ i)
  rw [faceInBoundary_inclusion]
  rfl

/-- The literal face leg into the boundary-indexed colimit of the original Q. -/
def faceQToBoundary (k : ℕ) (i : Fin (k + 2)) :
    QFunctor.{u}.obj ⦋k⦌ ⟶ boundaryQColimit.{u} (k + 1) :=
  colimit.ι (boundaryQDiagram.{u} (k + 1)) (faceBoundaryIndex.{u} k i)

/-- Its composite with the boundary map is exactly the original Q face map. -/
theorem faceQToBoundary_comp (k : ℕ) (i : Fin (k + 2)) :
    faceQToBoundary.{u} k i ≫ boundaryQMap.{u} (k + 1) =
      QFunctor.{u}.map (SimplexCategory.δ i) := by
  rw [faceQToBoundary, boundaryQMap_leg, boundaryOperator_face]

end

end DaggerOriginalCounitRightConeQBoundaryMono
