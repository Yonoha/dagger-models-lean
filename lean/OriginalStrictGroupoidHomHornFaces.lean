import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import OriginalJoinedHornPrefix

/-!
# Exact matching equations of the original horn faces

An actual map from a native horn supplies its original face values. Native monicity
of the horn inclusion and native coface identities prove their matching equations.
Reuse the previously verified original all-operator Yoneda evaluation theorem.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedHornPrefix

universe u

namespace DaggerOriginalStrictGroupoidHomHornFaces

noncomputable section

/-- A given original horn map evaluated on its actual native j-th face. -/
def hornFaceValue {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (h : (Λ[n + 1, i] : SSet.{u}) ⟶ X) (j : Fin (n + 2)) (hj : j ≠ i) : X _⦋n⦌ :=
  h.app (op ⦋n⦌) (SSet.horn.face i j hj)

/-- The original face value is exactly Yoneda of the same original horn inclusion and map. -/
theorem hornFaceValue_yoneda {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (h : (Λ[n + 1, i] : SSet.{u}) ⟶ X) (j : Fin (n + 2)) (hj : j ≠ i) :
    SSet.yonedaEquiv (SSet.horn.ι i j hj ≫ h) = hornFaceValue i h j hj := by
  rw [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι]
  rfl

/-- Actual native faces of the same original horn have the same codimension-two overlap. -/
theorem hornFace_intersection {n : ℕ} (i : Fin (n + 3)) (k l : Fin (n + 2))
    (hkl : k ≤ l) (hl : l.succ ≠ i) (hk : k.castSucc ≠ i) :
    SSet.stdSimplex.δ k ≫ SSet.horn.ι i l.succ hl =
      SSet.stdSimplex.δ l ≫ SSet.horn.ι i k.castSucc hk := by
  apply (cancel_mono (SSet.horn (n + 2) i).ι).mp
  simp only [Category.assoc, SSet.horn.ι_ι]
  exact SSet.stdSimplex.δ_comp_δ hkl

/-- All matching equations are proved for every actual original horn map. -/
theorem hornFaceValue_compatible {X : SSet.{u}} {n : ℕ} (i : Fin (n + 3))
    (h : (Λ[n + 2, i] : SSet.{u}) ⟶ X) (k l : Fin (n + 2))
    (hkl : k ≤ l) (hl : l.succ ≠ i) (hk : k.castSucc ≠ i) :
    X.δ k (hornFaceValue i h l.succ hl) = X.δ l (hornFaceValue i h k.castSucc hk) := by
  calc
    X.δ k (hornFaceValue i h l.succ hl) =
        SSet.yonedaEquiv (SSet.stdSimplex.δ k ≫ (SSet.horn.ι i l.succ hl ≫ h)) := by
      simpa only [hornFaceValue_yoneda] using
        (yonedaEquiv_precomp_operator (SSet.horn.ι i l.succ hl ≫ h)
          (SimplexCategory.δ k)).symm
    _ = SSet.yonedaEquiv (SSet.stdSimplex.δ l ≫ (SSet.horn.ι i k.castSucc hk ≫ h)) := by
      rw [← Category.assoc, ← Category.assoc, hornFace_intersection i k l hkl hl hk]
    _ = X.δ l (hornFaceValue i h k.castSucc hk) := by
      simpa only [hornFaceValue_yoneda] using
        yonedaEquiv_precomp_operator (SSet.horn.ι i k.castSucc hk ≫ h) (SimplexCategory.δ l)

end

end DaggerOriginalStrictGroupoidHomHornFaces
