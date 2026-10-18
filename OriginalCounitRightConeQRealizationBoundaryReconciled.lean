import OriginalCounitRightConeQBoundaryCofibrationsReconciled
import OriginalCounitRightConeQRealizationAdjunctionReconciled

/-!
# Realization of the literal boundary inclusion by the original Q

Identify the actual left Kan extension boundary map with the already verified
original boundary-Q map, using explicit isomorphisms which commute with every
original simplex leg. This gives cofibrations for the realization of every
standard boundary inclusion in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQBoundaryCofibrations
open DaggerOriginalCounitRightConeQRealizationAdjunction

universe u

namespace DaggerOriginalCounitRightConeQRealizationBoundary

noncomputable section

instance realizationUnit_isIso : IsIso realizationUnit.{u} := by
  dsimp [realizationUnit, realization]
  infer_instance

/-- The representable identification is inverse to the actual original-Q Kan unit. -/
def representableIso (n : SimplexCategory) :
    realization.{u}.obj (uliftYoneda.{u}.obj n) ≅ QFunctor.{u}.obj n :=
  (asIso (realizationUnit.{u}.app n)).symm

/-- The boundary identification comes from the two colimit universal properties. -/
def boundaryRealizationIso (n : ℕ) :
    boundaryQColimit.{u} n ≅ realization.{u}.obj (∂Δ[n] : SSet.{u}) :=
  (colimit.isColimit (boundaryQDiagram.{u} n)).coconePointUniqueUpToIso
    (simplexCoconeIsColimit (∂Δ[n] : SSet.{u}))

/-- The colimit identification preserves the actual unit and each literal boundary leg. -/
theorem boundaryRealizationIso_hom_leg (n : ℕ)
    (σ : DaggerChosenRigidificationNecklace.SimplexIndex (∂Δ[n] : SSet.{u})) :
    colimit.ι (boundaryQDiagram.{u} n) σ ≫ (boundaryRealizationIso.{u} n).hom =
      realizationUnit.app σ.left ≫ realization.map σ.hom :=
  (colimit.isColimit (boundaryQDiagram.{u} n)).fac
    (simplexCocone (∂Δ[n] : SSet.{u})) σ

/-- Realization of the exact boundary inclusion commutes with the original Q comparison. -/
theorem boundaryRealizationIso_map (n : ℕ) :
    (boundaryRealizationIso.{u} n).hom ≫ realization.map (∂Δ[n]).ι ≫
      (representableIso.{u} ⦋n⦌).hom = boundaryQMap.{u} n := by
  apply colimit.hom_ext
  intro σ
  rw [boundaryQMap_leg]
  simp only [← Category.assoc]
  rw [boundaryRealizationIso_hom_leg,
    Category.assoc (realizationUnit.app σ.left) (realization.map σ.hom)
      (realization.map (∂Δ[n]).ι),
    ← realization.map_comp, ← boundaryOperator_image]
  have h := realizationUnit.{u}.naturality (boundaryOperator.{u} n σ)
  change QFunctor.map (boundaryOperator.{u} n σ) ≫ realizationUnit.app ⦋n⦌ =
    realizationUnit.app σ.left ≫ realization.map
      (SSet.stdSimplex.{u}.map (boundaryOperator.{u} n σ)) at h
  rw [← h, Category.assoc]
  simp only [representableIso, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id, Category.comp_id]

/-- The actual realization map is the old boundary map transported by these precise isos. -/
theorem realization_boundary_map_eq (n : ℕ) :
    realization.{u}.map (∂Δ[n]).ι =
      (boundaryRealizationIso.{u} n).inv ≫ boundaryQMap.{u} n ≫
        (representableIso.{u} ⦋n⦌).inv := by
  rw [← boundaryRealizationIso_map]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id, Category.comp_id]

/-- The original-Q realization sends each literal boundary inclusion to a cofibration. -/
theorem realization_boundary_cofibration (n : ℕ) :
    Cofibration (realization.{u}.map (∂Δ[n]).ι) := by
  rw [realization_boundary_map_eq]
  have := boundaryQMap_cofibration.{u} n
  infer_instance

end

end DaggerOriginalCounitRightConeQRealizationBoundary
