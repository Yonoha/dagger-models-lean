import OriginalCounitRightConeRelativeHomotopyTimeOne
import OriginalCounitRightConeCrossTimeSectionsReconciled
import OriginalChosenHomMapFunctorialityReconciled

/-!
# The actual relative-cone homotopy on the original chosen Hom

Both formal endpoints are fixed by the whole simplicial homotopy. Thus the
original chosen Hom map has the exact cross-time source and literal `Q` target.
No weak equivalence is inferred from the homotopy alone.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerOriginalRigidificationDirectedProductProjection

universe u

namespace DaggerOriginalCounitRightConeRelativeHomMap

noncomputable section

private def zero : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- Alpha remains the literal alpha vertex at every time-zero-simplex. -/
theorem alpha_fixed_vertex (n : ℕ)
    (t : (Δ[1] : SSet.{u}).obj (op ⦋0⦌)) :
    (relativeHomotopy.{u} n).app (op ⦋0⦌) (alpha.{u} n, t) = alpha.{u} n := by
  have h := congrArg
    (fun f : ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ⟶ cone.{u} n ↦
      f.app (op ⦋0⦌) (zero.{u}, t))
    (alpha_relativeHomotopy.{u} n)
  change (relativeHomotopy.{u} n).app (op ⦋0⦌) (alpha.{u} n, t) =
    (alphaMap.{u} n).app (op ⦋0⦌)
      ((SSet.stdSimplex.isTerminalObj₀.from
        ((Δ[0] ⊗ Δ[1]) : SSet.{u})).app (op ⦋0⦌) (zero.{u}, t)) at h
  have hz :
      (SSet.stdSimplex.isTerminalObj₀.from
        ((Δ[0] ⊗ Δ[1]) : SSet.{u})).app (op ⦋0⦌) (zero.{u}, t) =
        zero.{u} := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  rw [hz] at h
  exact h

/-- Omega remains the literal omega vertex at every time-zero-simplex. -/
theorem omega_fixed_vertex (n : ℕ)
    (t : (Δ[1] : SSet.{u}).obj (op ⦋0⦌)) :
    (relativeHomotopy.{u} n).app (op ⦋0⦌) (omega.{u} n, t) = omega.{u} n := by
  have h := congrArg
    (fun f : ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ⟶ cone.{u} n ↦
      f.app (op ⦋0⦌) (zero.{u}, t))
    (omega_relativeHomotopy.{u} n)
  change (relativeHomotopy.{u} n).app (op ⦋0⦌) (omega.{u} n, t) =
    (omegaMap.{u} n).app (op ⦋0⦌)
      ((SSet.stdSimplex.isTerminalObj₀.from
        ((Δ[0] ⊗ Δ[1]) : SSet.{u})).app (op ⦋0⦌) (zero.{u}, t)) at h
  have hz :
      (SSet.stdSimplex.isTerminalObj₀.from
        ((Δ[0] ⊗ Δ[1]) : SSet.{u})).app (op ⦋0⦌) (zero.{u}, t) =
        zero.{u} := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  rw [hz] at h
  exact h

/-- The actual original Hom map induced by the relative cone homotopy. -/
def homH (n : ℕ) : coneCrossHom.{u} n ⟶ Q.{u} n :=
  originalChosenHomMap (relativeHomotopy.{u} n)
      (alpha.{u} n, vertexZero.{u}) (omega.{u} n, vertexOne.{u}) ≫
    targetHomTransport
      (congrArg (RV (cone.{u} n)) (alpha_fixed_vertex.{u} n vertexZero.{u}))
      (congrArg (RV (cone.{u} n)) (omega_fixed_vertex.{u} n vertexOne.{u}))

end

end DaggerOriginalCounitRightConeRelativeHomMap
