import OriginalRestBoundaryConeFaceRecovery

/-!
# Both inverse equations for the actual original boundary cone transpose

Native multicofork colimit uniqueness reduces equality to every whole original
face. The exact face-recovery equation and prescribed glued restrictions then
prove both inverse equations. This yields a genuine equivalence of the actual
original mapping sets, retaining every prefix and suffix dimension and universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalZeroJoinYonedaCorrespondence DaggerOriginalZeroJoinStandardCofaces
open DaggerOriginalZeroJoinStandardTransposition DaggerOriginalTransposedBoundaryFaceAgreement
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalRestBoundaryInverseFaceMaps DaggerOriginalRestBoundaryInverseGluing
open DaggerOriginalRestBoundaryConeFaceRecovery

universe u

namespace DaggerOriginalRestBoundaryConeInverseIdentities

noncomputable section

/-- The original smaller prefix boundary is the native gluing of all its original prefix faces.
-/
theorem prefixInverseDiagram (k n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram (prefixBoundary.{u} k n)
      (fun j : Fin (k + 1) ↦ SSet.stdSimplex.face {prefixIndex k n j}ᶜ)
      (fun j l ↦ SSet.stdSimplex.face {prefixIndex k n j}ᶜ ⊓
        SSet.stdSimplex.face {prefixIndex k n l}ᶜ) := ⟨rfl, fun _ _ ↦ rfl⟩

/-- Native colimit uniqueness detects maps on every exact original smaller standard coface. -/
theorem prefixBoundary_standard_face_hom_ext {X : SSet.{u}} (k n : ℕ)
    (f g : (prefixBoundary k n : SSet.{u}) ⟶ X)
    (h : ∀ j : Fin (k + 1), prefixFaceBoundaryInclusion k n j ≫ f =
      prefixFaceBoundaryInclusion k n j ≫ g) : f = g := by
  apply Multicofork.IsColimit.hom_ext (prefixInverseDiagram k n).isColimit'
  intro j
  apply (cancel_epi (SSet.stdSimplex.faceSingletonComplIso (prefixIndex k n j)).hom).mp
  simpa only [prefixFaceBoundaryInclusion, boundaryFaceInclusion, Category.assoc] using h j

/-- Native colimit uniqueness detects maps on every exact original remaining standard coface. -/
theorem restBoundary_standard_face_hom_ext {X : SSet.{u}} (k n : ℕ)
    (f g : (restPrefixBoundary k n : SSet.{u}) ⟶ X)
    (h : ∀ j : Fin (k + 1), restFaceBoundaryInclusion k n j ≫ f =
      restFaceBoundaryInclusion k n j ≫ g) : f = g := by
  apply Multicofork.IsColimit.hom_ext (restInverseDiagram k n).isColimit'
  intro j
  apply (cancel_epi
    (SSet.stdSimplex.faceSingletonComplIso (prefixIndex (k + 1) n j.succ)).hom).mp
  simpa only [restFaceBoundaryInclusion, boundaryFaceInclusion, Category.assoc] using h j

/-- Original standard vertex-join transposition is injective, with no filling assumption. -/
theorem zeroJoinStandardTranspose_injective (n : ℕ) (X : SSet.{u}) :
    Function.Injective (zeroJoinStandardTranspose (X := X) n) := by
  intro a b h
  apply (zeroJoinYonedaEquiv ⦋n⦌ X).injective
  apply (cancel_epi (SSet.stdSimplex.map (zeroJoinStandardIso n).inv)).mp
  exact h

/-- Gluing after the actual original cone transpose returns every original remaining-boundary
map exactly. -/
theorem inverseRestBoundaryMap_transpose {X : SSet.{u}} (k n : ℕ)
    (g : (restPrefixBoundary k n : SSet.{u}) ⟶ X) :
    inverseRestBoundaryMap k n (prefixConeTranspose k n g) = g := by
  apply restBoundary_standard_face_hom_ext k n
  intro j
  rw [inverseRestBoundaryMap_standardFace, inverseRestFaceStandardMap_transpose]

/-- The actual original cone transpose after gluing returns the original smaller-boundary map
exactly. -/
theorem prefixConeTranspose_inverse {X : SSet.{u}} (k n : ℕ)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    prefixConeTranspose k n (inverseRestBoundaryMap k n t) = t := by
  apply prefixBoundary_standard_face_hom_ext k n
  intro j
  apply zeroJoinStandardTranspose_injective (k + n) X
  haveI : IsIso (SSet.stdSimplex.{u}.map (restFaceSourceCast k n)) := by
    dsimp only [restFaceSourceCast]
    infer_instance
  apply (cancel_epi (SSet.stdSimplex.map (restFaceSourceCast k n))).mp
  change inverseRestFaceStandardMap k n j
      (prefixConeTranspose k n (inverseRestBoundaryMap k n t)) =
    inverseRestFaceStandardMap k n j t
  rw [inverseRestFaceStandardMap_transpose, inverseRestBoundaryMap_standardFace]

/-- The original mapping sets are equivalent via the exact proved cone transpose and gluing.
-/
def restConeTransposeEquiv (k n : ℕ) (X : SSet.{u}) :
    ((restPrefixBoundary k n : SSet.{u}) ⟶ X) ≃
      ((prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) where
  toFun := prefixConeTranspose k n
  invFun := inverseRestBoundaryMap k n
  left_inv := inverseRestBoundaryMap_transpose k n
  right_inv := prefixConeTranspose_inverse k n

end

end DaggerOriginalRestBoundaryConeInverseIdentities
