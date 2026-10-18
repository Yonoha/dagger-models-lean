import OriginalRigidificationDirectedProductProjectionReconciled
import DaggerModels.SimplicialEnrichment

/-!
# The two actual cross-time compositions for the right cone

The source arrows are original `Q` arrows. Horizontal arrows are placed at
time zero or one, and the vertical arrows are images of the unique directed
arrow in the original rigidification of `Δ[1]`.
-/

set_option autoImplicit false

open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalRigidificationDirectedProductProjection
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom

universe u

namespace DaggerOriginalCounitRightConeCrossTimeSections

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

/-- Place every simplex of X at a specified original endpoint time. -/
def horizontalAt (X : SSet.{u}) (i : I.{u}.obj (op ⦋0⦌)) : X ⟶ X ⊗ I.{u} :=
  lift (𝟙 X) (SSet.const i)

/-- A vertical line at one literal vertex of X. -/
def verticalAt (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) : I.{u} ⟶ X ⊗ I.{u} :=
  lift (SSet.const a) (𝟙 I.{u})

/-- Both coordinates of a horizontal endpoint remain literal. -/
theorem horizontalAt_vertex (X : SSet.{u}) (a : X.obj (op ⦋0⦌))
    (i : I.{u}.obj (op ⦋0⦌)) :
    (horizontalAt X i).app (op ⦋0⦌) a = (a, i) := by
  change (a, I.{u}.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op i) = (a, i)
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- Both coordinates of a vertical endpoint remain literal. -/
theorem verticalAt_vertex (X : SSet.{u}) (a : X.obj (op ⦋0⦌))
    (i : I.{u}.obj (op ⦋0⦌)) :
    (verticalAt X a).app (op ⦋0⦌) i = (a, i) := by
  change (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a, i) = (a, i)
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The chosen actual directed arrow, shaped by the enriched tensor unit. -/
def directedArrow : 𝟙_ SSet.{u} ⟶ intervalHom.{u} :=
  (SSet.unitHomEquiv intervalHom.{u}).symm
    ((directedHomIso.{u}.inv).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- A horizontal original Hom arrow at either endpoint time. -/
def horizontal (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (i : I.{u}.obj (op ⦋0⦌)) :
    firstHom X a b ⟶
      (RV (X ⊗ I.{u}) (a, i) ⟶[SSet.{u}] RV (X ⊗ I.{u}) (b, i)) :=
  originalChosenHomMap (horizontalAt X i) a b ≫
    targetHomTransport
      (congrArg (RV (X ⊗ I.{u})) (horizontalAt_vertex X a i))
      (congrArg (RV (X ⊗ I.{u})) (horizontalAt_vertex X b i))

/-- The directed vertical arrow at one original vertex, with both RV casts. -/
def vertical (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    𝟙_ SSet.{u} ⟶
      (RV (X ⊗ I.{u}) (a, vertexZero.{u}) ⟶[SSet.{u}]
        RV (X ⊗ I.{u}) (a, vertexOne.{u})) :=
  directedArrow.{u} ≫
    originalChosenHomMap (verticalAt X a) vertexZero.{u} vertexOne.{u} ≫
      targetHomTransport
        (congrArg (RV (X ⊗ I.{u})) (verticalAt_vertex X a vertexZero.{u}))
        (congrArg (RV (X ⊗ I.{u})) (verticalAt_vertex X a vertexOne.{u}))

/-- Horizontal at zero, followed by vertical at the target vertex. -/
def sectionZero (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    firstHom X a b ⟶ crossHom X a b :=
  (ρ_ (firstHom X a b)).inv ≫
    (horizontal X a b vertexZero.{u} ⊗ₘ vertical X b) ≫
      eComp SSet (RV (X ⊗ I.{u}) (a, vertexZero.{u}))
        (RV (X ⊗ I.{u}) (b, vertexZero.{u}))
        (RV (X ⊗ I.{u}) (b, vertexOne.{u}))

/-- Vertical at the source vertex, followed by horizontal at one. -/
def sectionOne (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    firstHom X a b ⟶ crossHom X a b :=
  (λ_ (firstHom X a b)).inv ≫
    (vertical X a ⊗ₘ horizontal X a b vertexOne.{u}) ≫
      eComp SSet (RV (X ⊗ I.{u}) (a, vertexZero.{u}))
        (RV (X ⊗ I.{u}) (a, vertexOne.{u}))
        (RV (X ⊗ I.{u}) (b, vertexOne.{u}))

/-- The first cross-time section for the original cone Q. -/
def s0 (n : ℕ) : DaggerOriginalCounitRightCone.Q.{u} n ⟶ coneCrossHom.{u} n :=
  sectionZero (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

/-- The second cross-time section for the original cone Q. -/
def s1 (n : ℕ) : DaggerOriginalCounitRightCone.Q.{u} n ⟶ coneCrossHom.{u} n :=
  sectionOne (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

end

end DaggerOriginalCounitRightConeCrossTimeSections
