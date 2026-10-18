import OriginalCounitRightConeRelativeHomotopy

/-!
# Endpoint maps of the original cone prism

This source-only layer records the whole-map time slices. It does not use a
homotopy as a substitute for a Joyal weak-equivalence proof.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy

universe u

namespace DaggerOriginalCounitRightConeRelativeHomotopy

noncomputable section

/-- The actual constant-time inclusion into the Cartesian cylinder. -/
def timeSlice (X : SSet.{u}) (t : Fin 2) : X ⟶ X ⊗ Δ[1] where
  app q x := ⟨x, SSet.stdSimplex.const 1 t q⟩
  naturality := by
    intro q q' f
    funext x
    rfl

/-- Constant-time inclusions commute with an arbitrary simplicial map. -/
theorem timeSlice_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (t : Fin 2) :
    f ≫ timeSlice Y t = timeSlice X t ≫ (f ▷ (Δ[1] : SSet.{u})) := by
  rfl

/-- Time zero is the identity on the whole large simplex. -/
theorem simplexPrism_time_zero (n k : ℕ) :
    timeSlice.{u} Δ[n + k] 0 ≫ simplexPrism.{u} n k =
      𝟙 (Δ[n + k] : SSet.{u}) := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    change (simplexPrism.{u} n k).app (op ⦋d⦌)
      (x, SSet.stdSimplex.const 1 0 (op ⦋d⦌)) i = x i
    rw [simplexPrism_app]
    change prismOrder n k (x i, 0) = x i
    exact prismOrder_zero n k (x i)

/-- Time zero is the identity of the *literal* pushout cone. -/
theorem relativeHomotopy_time_zero (n : ℕ) :
    timeSlice.{u} (cone.{u} n) 0 ≫ relativeHomotopy.{u} n =
      𝟙 (cone.{u} n) := by
  apply pushout.hom_ext
  · calc
      simplexIncl.{u} n ≫ timeSlice.{u} (cone.{u} n) 0 ≫
          relativeHomotopy.{u} n =
        timeSlice.{u} Δ[n + 1] 0 ≫
          (simplexIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫
            relativeHomotopy.{u} n := by
        simp only [← Category.assoc]
        rw [timeSlice_naturality]
      _ = simplexIncl.{u} n := by
        rw [simplexIncl_relativeHomotopy, ← Category.assoc,
          simplexPrism_time_zero]
        simp
      _ = simplexIncl.{u} n ≫ 𝟙 (cone.{u} n) := by simp
  · calc
      baseIncl.{u} n ≫ timeSlice.{u} (cone.{u} n) 0 ≫
          relativeHomotopy.{u} n =
        timeSlice.{u} Δ[0] 0 ≫
          (baseIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫
            relativeHomotopy.{u} n := by
        simp only [← Category.assoc]
        rw [timeSlice_naturality]
      _ = baseIncl.{u} n := by
        rw [baseIncl_relativeHomotopy, ← Category.assoc]
        have h : timeSlice.{u} Δ[0] 0 ≫
            SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) =
              𝟙 (Δ[0] : SSet.{u}) := SSet.stdSimplex.ext₀
        rw [h, Category.id_comp]
      _ = baseIncl.{u} n ≫ 𝟙 (cone.{u} n) := by simp

end

end DaggerOriginalCounitRightConeRelativeHomotopy
