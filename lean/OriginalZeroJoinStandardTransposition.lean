import OriginalZeroJoinStandardCofaces

/-!
# Standard face transposition with original cofaces retained

Original Yoneda and the explicit native successor cast convert a map into
J_0 X to a map from the original successor standard simplex into X. The
proved shifted-coface equation transfers every original common-face relation
to the successor common-face relation, with no filling assumption.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalZeroJoinYonedaCorrespondence DaggerOriginalZeroJoinStandardCofaces

universe u

namespace DaggerOriginalZeroJoinStandardTransposition

/-- The original inverse successor cast retains the native joined coface exactly. -/
theorem zeroJoinStandardIso_inv_comp_coface (n : ℕ) (i : Fin (n + 2)) :
    (zeroJoinStandardIso n).inv ≫ (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i) =
      SimplexCategory.δ i.succ ≫ (zeroJoinStandardIso (n + 1)).inv := by
  apply (cancel_mono (zeroJoinStandardIso (n + 1)).hom).mp
  rw [Category.assoc, zeroJoinStandardIso_coface]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Transpose to the actual original successor standard simplex through the explicit cast. -/
def zeroJoinStandardTranspose {X : SSet.{u}} (n : ℕ)
    (a : (Δ[n] : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) : (Δ[n + 1] : SSet.{u}) ⟶ X :=
  SSet.stdSimplex.map (zeroJoinStandardIso n).inv ≫ zeroJoinYonedaEquiv ⦋n⦌ X a

/-- Transposition converts every original coface to the original successor-index coface. -/
theorem zeroJoinStandardTranspose_precomp_coface {X : SSet.{u}} (n : ℕ)
    (i : Fin (n + 2)) (a : (Δ[n + 1] : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    zeroJoinStandardTranspose n (SSet.stdSimplex.δ i ≫ a) =
      SSet.stdSimplex.δ i.succ ≫ zeroJoinStandardTranspose (n + 1) a := by
  have h := congrArg SSet.stdSimplex.{u}.map (zeroJoinStandardIso_inv_comp_coface n i)
  simp only [Functor.map_comp] at h
  have hy := zeroJoinYonedaEquiv_precomp (SimplexCategory.δ i) a
  change zeroJoinYonedaEquiv ⦋n⦌ X (SSet.stdSimplex.δ i ≫ a) =
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i)) ≫
      zeroJoinYonedaEquiv ⦋n + 1⦌ X a at hy
  change SSet.stdSimplex.map (zeroJoinStandardIso n).inv ≫
      SSet.stdSimplex.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i)) =
    SSet.stdSimplex.δ i.succ ≫ SSet.stdSimplex.map (zeroJoinStandardIso (n + 1)).inv at h
  dsimp only [zeroJoinStandardTranspose]
  rw [hy, ← Category.assoc, h, Category.assoc]

/-- Every original common-face equation becomes the exact original successor common-face
relation. No agreement or filler in X is assumed separately. -/
theorem zeroJoinStandardTranspose_common_face {X : SSet.{u}} (n : ℕ)
    (a b : Fin (n + 2))
    (μa μb : (Δ[n + 1] : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X)
    (w : SSet.stdSimplex.δ a ≫ μb = SSet.stdSimplex.δ b ≫ μa) :
    SSet.stdSimplex.δ a.succ ≫ zeroJoinStandardTranspose (n + 1) μb =
      SSet.stdSimplex.δ b.succ ≫ zeroJoinStandardTranspose (n + 1) μa := by
  rw [← zeroJoinStandardTranspose_precomp_coface, w,
    zeroJoinStandardTranspose_precomp_coface]

/-- Standard transposition commutes with the same actual original target map. -/
theorem zeroJoinStandardTranspose_postcomp {X Y : SSet.{u}} (n : ℕ)
    (a : (Δ[n] : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) (p : X ⟶ Y) :
    zeroJoinStandardTranspose n (a ≫ Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op p) =
      zeroJoinStandardTranspose n a ≫ p := by
  dsimp only [zeroJoinStandardTranspose]
  rw [zeroJoinYonedaEquiv_postcomp, Category.assoc]

end DaggerOriginalZeroJoinStandardTransposition
