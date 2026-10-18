import OriginalChosenProductComparisonReconciledRecovered
import OriginalRigidificationDirectedIntervalHomNativeIsoReconciled
import OriginalCounitRightCone
import SSetProductGeometric

/-!
# Projection from a cross-time Hom in the original rigidification

The second factor is the directed one-simplex, with the literal vertex pair
`0,1`. Its original Hom is terminal. Thus the full product comparison gives
a geometric weak equivalence on the first projection, including both chosen
object transports.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerChosenRigidificationNecklace DaggerOriginalProductGadget
open DaggerSSetGluing

universe u

namespace DaggerOriginalRigidificationDirectedProductProjection

noncomputable section

/-- The selected original directed Hom, not a codiscrete interval Hom. -/
abbrev intervalHom : SSet.{u} :=
  (RV (Δ[1] : SSet.{u}) vertexZero.{u} ⟶[SSet.{u}]
    RV (Δ[1] : SSet.{u}) vertexOne.{u})

/-- The directed Hom is terminal, by its actual isomorphism with `Δ[0]`. -/
def intervalHom_isTerminal : IsTerminal intervalHom.{u} :=
  IsTerminal.ofIso SSet.stdSimplex.isTerminalObj₀ directedHomIso.{u}.symm

/-- The canonical collapse of the original directed Hom is an isomorphism. -/
instance intervalHom_toUnit_isIso : IsIso (toUnit intervalHom.{u}) :=
  isIso_of_isTerminal intervalHom_isTerminal.{u} isTerminalTensorUnit _

/-- The same canonical collapse is a geometric weak equivalence. -/
theorem intervalHom_toUnit_GW : GW (toUnit intervalHom.{u}) := by
  haveI : WeakEquivalence (toUnit intervalHom.{u}) := inferInstance
  exact (weakEquivalence_iff_GW _).1 ‹WeakEquivalence (toUnit intervalHom.{u})›

/-- The original first-factor Hom at the chosen original vertices. -/
abbrev firstHom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : SSet.{u} :=
  RV X a ⟶[SSet.{u}] RV X b

/-- The actual cross-time Hom at `(a,0)` and `(b,1)`. -/
abbrev crossHom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : SSet.{u} :=
  RV (X ⊗ (Δ[1] : SSet.{u})) (a, vertexZero.{u}) ⟶[SSet.{u}]
    RV (X ⊗ (Δ[1] : SSet.{u})) (b, vertexOne.{u})

/-- The literal original Hom map of the first projection, with both RV casts. -/
def projection (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    crossHom X a b ⟶ firstHom X a b :=
  originalChosenHomMap (fst X (Δ[1] : SSet.{u}))
    (a, vertexZero.{u}) (b, vertexOne.{u})

/-- Full-map factorization through the product comparison and terminal interval. -/
theorem projection_factorization (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    chosenVertexProductComparison a b vertexZero.{u} vertexOne.{u} ≫
      (firstHom X a b ◁ toUnit intervalHom.{u}) ≫
        (ρ_ (firstHom X a b)).hom = projection X a b := by
  rw [whiskerLeft_toUnit_comp_rightUnitor_hom,
    chosenVertexProductComparison_fst]
  rfl

/-- The first projection is a geometric weak equivalence, for arbitrary X,a,b. -/
theorem projection_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (projection X a b) := by
  have hprod : GW (chosenVertexProductComparison a b
      vertexZero.{u} vertexOne.{u}) :=
    chosenVertexProductComparison_GW a b vertexZero.{u} vertexOne.{u}
  have hwhisker : GW (firstHom X a b ◁ toUnit intervalHom.{u}) :=
    DaggerSSetProductGeometric.whiskerLeft_geometric (toUnit intervalHom.{u}) intervalHom_toUnit_GW
      (firstHom X a b)
  letI : WeakEquivalence (chosenVertexProductComparison a b
      vertexZero.{u} vertexOne.{u}) := (weakEquivalence_iff_GW _).2 hprod
  letI : WeakEquivalence (firstHom X a b ◁ toUnit intervalHom.{u}) :=
    (weakEquivalence_iff_GW _).2 hwhisker
  apply (weakEquivalence_iff_GW _).1
  rw [← projection_factorization X a b]
  infer_instance

/-- The same cross-time Hom for the actual right-cone endpoints. -/
abbrev coneCrossHom (n : ℕ) : SSet.{u} :=
  crossHom (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

/-- The original first projection from the cross-time cone Hom to literal Q. -/
def coneProjection (n : ℕ) :
    coneCrossHom.{u} n ⟶ DaggerOriginalCounitRightCone.Q.{u} n :=
  projection (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

/-- The cross-time projection onto the existing cone Q is a geometric WE. -/
theorem coneProjection_GW (n : ℕ) : GW (coneProjection.{u} n) :=
  projection_GW (DaggerOriginalCounitRightCone.cone.{u} n)
    (DaggerOriginalCounitRightCone.alpha.{u} n)
    (DaggerOriginalCounitRightCone.omega.{u} n)

end

end DaggerOriginalRigidificationDirectedProductProjection
