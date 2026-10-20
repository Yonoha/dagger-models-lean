import OriginalCounitRightConeQBoundaryMonoReconciled
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-!
# Recognition of the actual Q boundary by its codimension-one faces

Every simplex of the literal boundary factors through one of its faces. This
identifies the image of the actual boundary-indexed Q comparison as the union
of the images of the original Q coface maps. It does not identify intersections
of those images or assert that the boundary comparison is a monomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQBoundaryMono

universe u

namespace DaggerOriginalCounitRightConeQBoundaryRecognition

noncomputable section

/-- A boundary simplex has a non-surjective ordinary operator. -/
theorem boundaryOperator_not_surjective (k : ℕ)
    (σ : SimplexIndex (∂Δ[k + 1] : SSet.{u})) :
    ¬ Function.Surjective (boundaryOperator.{u} (k + 1) σ).toOrderHom := by
  have hmem : ¬ Function.Surjective
      (SSet.stdSimplex.asOrderHom ((SSet.yonedaEquiv σ.hom).val)) :=
    (SSet.yonedaEquiv σ.hom).property
  have hval : ((SSet.yonedaEquiv σ.hom).val :
      (Δ[k + 1] : SSet.{u}).obj (op σ.left)) =
      SSet.stdSimplex.objEquiv.symm (boundaryOperator.{u} (k + 1) σ) := by
    change SSet.yonedaEquiv (σ.hom ≫ (∂Δ[k + 1]).ι) = _
    rw [← boundaryOperator_image]
    exact SSet.stdSimplex.yonedaEquiv_map _
  rw [hval] at hmem
  exact hmem

/-- Every ordinary operator represented by a boundary simplex factors through a face. -/
theorem boundaryOperator_factors_face (k : ℕ)
    (σ : SimplexIndex (∂Δ[k + 1] : SSet.{u})) :
    ∃ (i : Fin (k + 2)) (g : σ.left ⟶ ⦋k⦌),
      boundaryOperator.{u} (k + 1) σ = g ≫ SimplexCategory.δ i := by
  exact SimplexCategory.eq_comp_δ_of_not_surjective _
    (boundaryOperator_not_surjective.{u} k σ)

/-- Factorization in the literal boundary subcomplex, not only in its ambient simplex. -/
theorem boundary_simplex_factors_face (k : ℕ)
    (σ : SimplexIndex (∂Δ[k + 1] : SSet.{u})) :
    ∃ (i : Fin (k + 2)) (g : σ.left ⟶ ⦋k⦌),
      σ.hom = SSet.stdSimplex.{u}.map g ≫ faceInBoundary.{u} k i := by
  obtain ⟨i, g, hg⟩ := boundaryOperator_factors_face.{u} k σ
  refine ⟨i, g, ?_⟩
  apply (cancel_mono (∂Δ[k + 1]).ι).1
  rw [Category.assoc, faceInBoundary_inclusion]
  change σ.hom ≫ (∂Δ[k + 1]).ι =
    SSet.stdSimplex.{u}.map g ≫ SSet.stdSimplex.{u}.map (SimplexCategory.δ i)
  rw [← SSet.stdSimplex.map_comp, ← hg]
  exact (boundaryOperator_image.{u} (k + 1) σ).symm

/-- Every boundary-colimit leg factors through an actual Q face leg. -/
theorem boundaryQ_leg_factors_face (k : ℕ)
    (σ : SimplexIndex (∂Δ[k + 1] : SSet.{u})) :
    ∃ (i : Fin (k + 2)) (g : σ.left ⟶ ⦋k⦌),
      colimit.ι (boundaryQDiagram.{u} (k + 1)) σ =
        QFunctor.{u}.map g ≫ faceQToBoundary.{u} k i := by
  obtain ⟨i, g, hg⟩ := boundary_simplex_factors_face.{u} k σ
  let f : σ ⟶ faceBoundaryIndex.{u} k i :=
    CostructuredArrow.homMk g hg.symm
  refine ⟨i, g, ?_⟩
  have hw := colimit.w (boundaryQDiagram.{u} (k + 1)) f
  change QFunctor.{u}.map g ≫ faceQToBoundary.{u} k i =
    colimit.ι (boundaryQDiagram.{u} (k + 1)) σ at hw
  exact hw.symm

/-- The image of the actual boundary comparison is exactly the union of its
codimension-one Q-face images. This is the image calculation preceding the
still-needed intersection/normal-form argument for monicity. -/
theorem boundaryQMap_range_faces (k : ℕ) :
    SSet.Subcomplex.range (boundaryQMap.{u} (k + 1)) =
      ⨆ (i : Fin (k + 2)),
        SSet.Subcomplex.range (QFunctor.{u}.map (SimplexCategory.δ i)) := by
  rw [SSet.range_eq_iSup_of_isColimit
    (colimit.isColimit (boundaryQDiagram.{u} (k + 1)))
    (boundaryQMap.{u} (k + 1))]
  apply le_antisymm
  · refine iSup_le fun σ ↦ ?_
    obtain ⟨i, g, hg⟩ := boundaryQ_leg_factors_face.{u} k σ
    have hcomp :
        colimit.ι (boundaryQDiagram.{u} (k + 1)) σ ≫ boundaryQMap.{u} (k + 1) =
          QFunctor.{u}.map g ≫ QFunctor.{u}.map (SimplexCategory.δ i) := by
      rw [hg, Category.assoc, faceQToBoundary_comp]
    change SSet.Subcomplex.range
      (colimit.ι (boundaryQDiagram.{u} (k + 1)) σ ≫ boundaryQMap.{u} (k + 1)) ≤ _
    rw [hcomp]
    exact (Subfunctor.range_comp_le _ _).trans (le_iSup_of_le i le_rfl)
  · refine iSup_le fun i ↦ ?_
    rw [← faceQToBoundary_comp.{u} k i]
    exact le_iSup_of_le (faceBoundaryIndex.{u} k i) le_rfl

end

end DaggerOriginalCounitRightConeQBoundaryRecognition
