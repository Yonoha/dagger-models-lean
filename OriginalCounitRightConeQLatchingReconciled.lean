import OriginalCounitRightConeQFunctorReconciled
import ChosenRigidificationSimplexColimit
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The actual boundary-indexed comparison for the right-cone Q diagram

This constructs the map from the colimit indexed by simplices of the literal
boundary of a standard simplex to the original `Q n`. An identification with
a Reedy latching object and cofibrancy of the map require further proofs.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightConeQFunctor

universe u

namespace DaggerOriginalCounitRightConeQLatching

noncomputable section

private instance : SSet.stdSimplex.{u}.Full :=
  inferInstanceAs (uliftYoneda.{u} (C := SimplexCategory)).Full

private instance : SSet.stdSimplex.{u}.Faithful :=
  inferInstanceAs (uliftYoneda.{u} (C := SimplexCategory)).Faithful

/-- The ordinary simplex operator underlying an actual boundary simplex. -/
def boundaryOperator (n : ℕ)
    (σ : SimplexIndex (∂Δ[n] : SSet.{u})) : σ.left ⟶ ⦋n⦌ :=
  SSet.stdSimplex.{u}.preimage (σ.hom ≫ (∂Δ[n]).ι)

/-- Its representable image is the boundary simplex followed by inclusion. -/
theorem boundaryOperator_image (n : ℕ)
    (σ : SimplexIndex (∂Δ[n] : SSet.{u})) :
    SSet.stdSimplex.{u}.map (boundaryOperator.{u} n σ) =
      σ.hom ≫ (∂Δ[n]).ι := by
  exact SSet.stdSimplex.{u}.map_preimage _

/-- Operators commute with every morphism in the actual boundary-simplex category. -/
theorem boundaryOperator_naturality (n : ℕ)
    {σ τ : SimplexIndex (∂Δ[n] : SSet.{u})} (h : σ ⟶ τ) :
    boundaryOperator.{u} n σ = h.left ≫ boundaryOperator.{u} n τ := by
  apply SSet.stdSimplex.{u}.map_injective
  rw [SSet.stdSimplex.map_comp, boundaryOperator_image, boundaryOperator_image]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (∂Δ[n]).ι) (CostructuredArrow.w h).symm

/-- The original `QFunctor` restricted to simplices of the literal boundary. -/
def boundaryQDiagram (n : ℕ) :
    SimplexIndex (∂Δ[n] : SSet.{u}) ⥤ SSet.{u} :=
  CostructuredArrow.proj SSet.stdSimplex.{u} (∂Δ[n] : SSet.{u}) ⋙ QFunctor.{u}

/-- The boundary legs land in the same original `Q n`, with its original endpoints. -/
def boundaryQCocone (n : ℕ) : Cocone (boundaryQDiagram.{u} n) where
  pt := QFunctor.{u}.obj ⦋n⦌
  ι := {
    app := fun σ ↦ QFunctor.{u}.map (boundaryOperator.{u} n σ)
    naturality := by
      intro σ τ h
      change QFunctor.{u}.map h.left ≫
          QFunctor.{u}.map (boundaryOperator.{u} n τ) =
        QFunctor.{u}.map (boundaryOperator.{u} n σ)
      rw [← QFunctor.map_comp, ← boundaryOperator_naturality n h] }

/-- A boundary-indexed colimit, without presupposing a Reedy comparison theorem. -/
def boundaryQColimit (n : ℕ) : SSet.{u} :=
  colimit (boundaryQDiagram.{u} n)

/-- The actual canonical map from the boundary-indexed colimit to `Q n`. -/
def boundaryQMap (n : ℕ) : boundaryQColimit.{u} n ⟶ QFunctor.{u}.obj ⦋n⦌ :=
  colimit.desc (boundaryQDiagram.{u} n) (boundaryQCocone.{u} n)

/-- Its restriction to every original boundary simplex is the original Q map. -/
theorem boundaryQMap_leg (n : ℕ)
    (σ : SimplexIndex (∂Δ[n] : SSet.{u})) :
    colimit.ι (boundaryQDiagram.{u} n) σ ≫ boundaryQMap.{u} n =
      QFunctor.{u}.map (boundaryOperator.{u} n σ) := by
  exact colimit.ι_desc (boundaryQCocone.{u} n) σ

end

end DaggerOriginalCounitRightConeQLatching
