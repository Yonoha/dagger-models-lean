import OriginalCounitRightConeQCommonBaseFaceReconciled
import OriginalCounitRightConeQBoundaryMonoReconciled

/-!
# A literal boundary-index object witnessing distinct-face overlap

The common old face of two distinct cofaces is itself a simplex of the
actual standard boundary. Its two arrows to the original face indices
make the two corresponding Q colimit legs agree there.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQBoundaryMono
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQFunctor

universe u

namespace DaggerOriginalCounitRightConeQCommonBoundaryOverlap

noncomputable section

private abbrev α (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    ⦋n⦌ ⟶ ⦋n + 2⦌ := commonBaseHom n i j hij

def factorI (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.factor_δ (α n i j hij) i

def factorJ (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.factor_δ (α n i j hij) j

theorem factorI_spec (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    factorI n i j hij ≫ SimplexCategory.δ i = α n i j hij := by
  apply SimplexCategory.factor_δ_spec
  intro v
  exact ((commonBaseHom_vertex_range n i j hij
    ((α n i j hij).toOrderHom v)).1 ⟨v, rfl⟩).1

theorem factorJ_spec (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    factorJ n i j hij ≫ SimplexCategory.δ j = α n i j hij := by
  apply SimplexCategory.factor_δ_spec
  intro v
  exact ((commonBaseHom_vertex_range n i j hij
    ((α n i j hij).toOrderHom v)).1 ⟨v, rfl⟩).2

/-- The common simplex as a literal object of the target boundary
index category. -/
def commonBoundaryIndex (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    SimplexIndex (∂Δ[n + 2] : SSet.{u}) :=
  CostructuredArrow.mk
    (SSet.stdSimplex.{u}.map (factorJ n i j hij) ≫
      faceInBoundary.{u} (n + 1) j)

private theorem commonBoundaryIndex_faceI (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    (commonBoundaryIndex.{u} n i j hij).hom =
      SSet.stdSimplex.{u}.map (factorI n i j hij) ≫
        faceInBoundary.{u} (n + 1) i := by
  apply (cancel_mono (∂Δ[n + 2]).ι).1
  change (SSet.stdSimplex.{u}.map (factorJ n i j hij) ≫
      faceInBoundary.{u} (n + 1) j) ≫ (∂Δ[n + 2]).ι =
    (SSet.stdSimplex.{u}.map (factorI n i j hij) ≫
      faceInBoundary.{u} (n + 1) i) ≫ (∂Δ[n + 2]).ι
  rw [Category.assoc, Category.assoc,
    faceInBoundary_inclusion, faceInBoundary_inclusion]
  change SSet.stdSimplex.{u}.map (factorJ n i j hij) ≫
    SSet.stdSimplex.{u}.map (SimplexCategory.δ j) =
      SSet.stdSimplex.{u}.map (factorI n i j hij) ≫
        SSet.stdSimplex.{u}.map (SimplexCategory.δ i)
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp,
    factorI_spec, factorJ_spec]

def commonBoundaryToFaceI (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    commonBoundaryIndex.{u} n i j hij ⟶
      faceBoundaryIndex.{u} (n + 1) i :=
  CostructuredArrow.homMk (factorI n i j hij)
    (commonBoundaryIndex_faceI.{u} n i j hij).symm

def commonBoundaryToFaceJ (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    commonBoundaryIndex.{u} n i j hij ⟶
      faceBoundaryIndex.{u} (n + 1) j :=
  CostructuredArrow.homMk (factorJ n i j hij) rfl

/-- The two literal face colimit legs agree after their shared old-face
factor maps. This is equality inside the actual boundary-indexed Q
colimit, without replacing it by a face-cover surrogate. -/
theorem commonQFaceLegs_agree (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    QFunctor.{u}.map (factorI n i j hij) ≫
      faceQToBoundary.{u} (n + 1) i =
    QFunctor.{u}.map (factorJ n i j hij) ≫
      faceQToBoundary.{u} (n + 1) j := by
  let D := boundaryQDiagram.{u} (n + 2)
  let σ := commonBoundaryIndex.{u} n i j hij
  have hi := colimit.w D (commonBoundaryToFaceI.{u} n i j hij)
  have hj := colimit.w D (commonBoundaryToFaceJ.{u} n i j hij)
  change QFunctor.{u}.map (factorI n i j hij) ≫
      faceQToBoundary.{u} (n + 1) i = colimit.ι D σ at hi
  change QFunctor.{u}.map (factorJ n i j hij) ≫
      faceQToBoundary.{u} (n + 1) j = colimit.ι D σ at hj
  exact hi.trans hj.symm

end

end DaggerOriginalCounitRightConeQCommonBoundaryOverlap
