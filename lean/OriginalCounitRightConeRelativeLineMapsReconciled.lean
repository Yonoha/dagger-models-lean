import OriginalCounitRightConeRelativeHomMapReconciled
import OriginalCounitRightConeCrossTimeSectionsReconciled

/-!
# Whole simplicial-map identities for the original relative cone lines

The actual horizontal and vertical maps used in the cross-time Hom sections
are compared with the original relative cone homotopy before rigidification.
These identities alone do not give a weak equivalence of Hom objects.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerOriginalCounitRightConeCrossTimeSections

universe u

namespace DaggerOriginalCounitRightConeRelativeLineMaps

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

private def zero : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- The horizontal placement at the first directed vertex is constant time zero. -/
theorem horizontalAt_zero (X : SSet.{u}) :
    horizontalAt X vertexZero.{u} = timeSlice X 0 := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro i
      rfl

/-- The horizontal placement at the last directed vertex is constant time one. -/
theorem horizontalAt_one (X : SSet.{u}) :
    horizontalAt X vertexOne.{u} = timeSlice X 1 := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro i
      rfl

/-- Time-zero horizontal placement retracts by the whole original homotopy. -/
theorem horizontal_relative_zero (n : ℕ) :
    horizontalAt (cone.{u} n) vertexZero.{u} ≫ relativeHomotopy.{u} n =
      𝟙 (cone.{u} n) := by
  rw [horizontalAt_zero]
  exact relativeHomotopy_time_zero.{u} n

/-- Time-one horizontal placement is the chosen projection and last edge. -/
theorem horizontal_relative_one (n : ℕ) :
    horizontalAt (cone.{u} n) vertexOne.{u} ≫ relativeHomotopy.{u} n =
      projection.{u} n ≫ lastEdge.{u} n := by
  rw [horizontalAt_one]
  exact relativeHomotopy_time_one.{u} n

/-- A vertical line at a represented vertex factors through its point map. -/
theorem verticalAt_point (X : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ X) :
    verticalAt X (p.app (op ⦋0⦌) zero.{u}) =
      verticalAt (Δ[0] : SSet.{u}) zero.{u} ≫ (p ▷ I.{u}) := by
  unfold verticalAt
  rw [lift_whiskerRight, SSet.const_comp]

private theorem vertical_fixed (n : ℕ)
    (p : (Δ[0] : SSet.{u}) ⟶ cone.{u} n)
    (hp : (p ▷ I.{u}) ≫ relativeHomotopy.{u} n =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ I.{u}) : SSet.{u}) ≫ p) :
    verticalAt (cone.{u} n) (p.app (op ⦋0⦌) zero.{u}) ≫
        relativeHomotopy.{u} n =
      SSet.const (X := I.{u}) (p.app (op ⦋0⦌) zero.{u}) := by
  rw [verticalAt_point, Category.assoc, hp, ← Category.assoc]
  have hterminal :
      verticalAt (Δ[0] : SSet.{u}) zero.{u} ≫
          SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ I.{u}) : SSet.{u}) =
        SSet.const (X := I.{u}) zero.{u} :=
    SSet.stdSimplex.ext₀
  rw [hterminal, SSet.const_comp]

/-- The actual alpha vertical line stays at alpha in every simplicial degree. -/
theorem vertical_relative_alpha (n : ℕ) :
    verticalAt (cone.{u} n) (alpha.{u} n) ≫ relativeHomotopy.{u} n =
      SSet.const (X := I.{u}) (alpha.{u} n) :=
  vertical_fixed.{u} n (alphaMap.{u} n) (alpha_relativeHomotopy.{u} n)

/-- The actual omega vertical line stays at omega in every simplicial degree. -/
theorem vertical_relative_omega (n : ℕ) :
    verticalAt (cone.{u} n) (omega.{u} n) ≫ relativeHomotopy.{u} n =
      SSet.const (X := I.{u}) (omega.{u} n) :=
  vertical_fixed.{u} n (omegaMap.{u} n) (omega_relativeHomotopy.{u} n)

end

end DaggerOriginalCounitRightConeRelativeLineMaps
