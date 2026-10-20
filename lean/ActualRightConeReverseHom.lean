import ActualRightConeObjectClassification
import OriginalRigidificationDirectedIntervalHomNativeIsoReconciled

/-! The original rigidified right cone has no arrows from its tip back to its base. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRetractionHomFactorization
open DaggerOriginalEnrichedHomTransport
open DaggerChosenRigidificationNecklace hiding C RV
universe u

namespace DaggerActualRightConeReverseHom

noncomputable section

def reverseHom (n : ℕ) : SSet.{u} :=
  (rigidification.{u}.obj (cone.{u} n)).enriched.Hom (omegaObj.{u} n) (alphaObj.{u} n)

/-- The literal cone-to-interval projection detects an impossible reverse ordered path. -/
theorem degree_isEmpty (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    IsEmpty ((reverseHom.{u} n).obj q) := by
  constructor
  intro x
  let p := rigidification.{u}.map (projection.{u} n)
  let a := RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u})
    DirectedIntervalHom.vertexOne.{u}
  let b := RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u})
    DirectedIntervalHom.vertexZero.{u}
  have hω : p.obj (omegaObj.{u} n) = a := by
    rw [omegaObj, RigidificationVertices.vertexEquiv_naturality, projection_omega]
  have hα : p.obj (alphaObj.{u} n) = b := by
    rw [alphaObj, RigidificationVertices.vertexEquiv_naturality, projection_alpha]
  let f : reverseHom.{u} n ⟶ (a ⟶[SSet.{u}] b) :=
    p.map (omegaObj.{u} n) (alphaObj.{u} n) ≫ targetHomTransport hω hα
  let e := rigidificationSimplexIso.{u}.app ⦋1⦌
  let y := (e.hom.map a b).app q (f.app q x)
  have hle := SimplicialThickening.Path.le (y.obj 0)
  have ha : e.hom.obj a = DirectedIntervalHom.thickOne.{u} :=
    DirectedIntervalHom.simplexIso_one
  have hb : e.hom.obj b = DirectedIntervalHom.thickZero.{u} :=
    DirectedIntervalHom.simplexIso_zero
  change (e.hom.obj a).as ≤ (e.hom.obj b).as at hle
  rw [ha, hb] at hle
  change (1 : Fin 2) ≤ 0 at hle
  exact (by decide : ¬((1 : Fin 2) ≤ 0)) hle

/-- The full original enriched Hom, in every simplicial degree, is initial. -/
def isInitial (n : ℕ) : IsInitial (reverseHom.{u} n) := by
  refine IsInitial.ofUniqueHom (fun X ↦ ?_) ?_
  · exact
      { app := fun q x ↦ False.elim ((degree_isEmpty n q).false x)
        naturality := by
          intro q r f
          ext x
          exact False.elim ((degree_isEmpty n q).false x) }
  · intro X f
    ext q x
    exact False.elim ((degree_isEmpty n q).false x)

end
end DaggerActualRightConeReverseHom
