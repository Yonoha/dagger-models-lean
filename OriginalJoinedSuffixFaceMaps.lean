import OriginalJoinedHornFaceCompatibility
import OriginalCofaceIntersectionAgreement

/-!
# Actual joined suffix coface maps agree on entire intersections

Use the original horn coface simplices, the native omitted-vertex face
isomorphisms, and the proved epimorphic double-coface coverage. The original
horn-map naturality then proves equality on each full pairwise intersection.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornFaceCompatibility
open DaggerOriginalCofaceIntersectionAgreement

universe u

namespace DaggerOriginalJoinedSuffixFaceMaps

noncomputable section

/-- The exact original joined simplex supplied by a coface of the original horn map. -/
def joinedHornCoface {X : SSet.{u}} (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    (Δ[k + n + 1] : SSet.{u}) ⟶ X :=
  (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
    ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n⦌))
      (SSet.horn.ι i j hj ≫ φ))

/-- The map on the actual omitted-vertex face, retaining that same original coface simplex. -/
def suffixFaceMap {X : SSet.{u}} (k n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i)
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    (SSet.stdSimplex.face {suffixIndex k (n + 1) j}ᶜ : SSet.{u}) ⟶ X :=
  (SSet.stdSimplex.faceSingletonComplIso (suffixIndex k (n + 1) j)).inv ≫
    joinedHornCoface k n i j hj φ

/-- For arbitrary original horn dimensions, distinct ordered suffix faces agree everywhere. -/
theorem suffixFaceMap_agreement {X : SSet.{u}} (k n : ℕ)
    (i j l : Fin (n + 3)) (hj : j ≠ i) (hl : l ≠ i) (hjl : j < l)
    (φ : (Λ[n + 2, i] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ X) :
    SSet.Subcomplex.homOfLE inf_le_left ≫ suffixFaceMap k (n + 1) i j hj φ =
      SSet.Subcomplex.homOfLE inf_le_right ≫ suffixFaceMap k (n + 1) i l hl φ := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin (n + 2), a.castSucc = j := by
    refine ⟨⟨j.val, by have h := l.isLt; change j.val < l.val at hjl; omega⟩, ?_⟩
    exact Fin.ext rfl
  obtain ⟨b, rfl⟩ : ∃ b : Fin (n + 2), b.succ = l := by
    refine ⟨⟨l.val - 1, by have h := l.isLt; change a.val < l.val at hjl; omega⟩, ?_⟩
    apply Fin.ext
    change l.val - 1 + 1 = l.val
    change a.val < l.val at hjl
    omega
  have hab : a ≤ b := by change a.val ≤ b.val; change a.val < b.val + 1 at hjl; omega
  have hshift : suffixIndex k (n + 1) a ≤ suffixIndex k (n + 1) b := by
    change k + 1 + a.val ≤ k + 1 + b.val
    change a.val ≤ b.val at hab
    omega
  have ha : (suffixIndex k (n + 1) a).castSucc = suffixIndex k (n + 2) a.castSucc :=
    Fin.ext rfl
  have hb : (suffixIndex k (n + 1) b).succ = suffixIndex k (n + 2) b.succ :=
    Fin.ext rfl
  have hw := joined_two_coface_compatibility k n i a b hab hl hj φ
  have h := intersection_agreement (suffixIndex k (n + 1) a) (suffixIndex k (n + 1) b)
    hshift (joinedHornCoface k (n + 1) i a.castSucc hj φ)
      (joinedHornCoface k (n + 1) i b.succ hl φ) hw
  rw [ha, hb] at h
  exact h

end

end DaggerOriginalJoinedSuffixFaceMaps
