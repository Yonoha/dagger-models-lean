import OriginalTransposedBoundaryFaceAgreement

/-!
# Actual remaining-boundary face maps for the inverse cone construction

Restrict the original smaller-boundary map to each actual original prefix
coface. Native vertex-join transposition and the explicit original face-source
cast give maps on the original successor faces. Their agreement holds on
every entire original face intersection, including all original dimensions.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalZeroJoinStandardTransposition
open DaggerOriginalTransposedBoundaryFaceAgreement

universe u

namespace DaggerOriginalRestBoundaryInverseFaceMaps

noncomputable section

/-- The actual original standard prefix coface into the original smaller boundary. -/
def prefixFaceBoundaryInclusion (k n : ℕ) (j : Fin (k + 1)) :
    (Δ[k + n] : SSet.{u}) ⟶ prefixBoundary k n :=
  boundaryFaceInclusion (prefixBoundary k n) (prefixIndex k n j)
    (le_iSup (fun j : Fin (k + 1) ↦ SSet.stdSimplex.face {prefixIndex k n j}ᶜ) j)

/-- Its ambient operator is exactly the same original prefix coface. -/
theorem prefixFaceBoundaryInclusion_comp (k n : ℕ) (j : Fin (k + 1)) :
    prefixFaceBoundaryInclusion.{u} k n j ≫ (prefixBoundary k n).ι =
      SSet.stdSimplex.δ (prefixIndex k n j) := boundaryFaceInclusion_comp _ _ _

/-- The original successor face-source dimensions agree by the explicit ordinal equality. -/
theorem restFaceDimension_eq (k n : ℕ) : k + 1 + n = k + n + 1 := by omega

/-- The corresponding successor vertex is the exact original remaining-prefix face index. -/
theorem restFaceIndex_cast (k n : ℕ) (j : Fin (k + 1)) :
    Fin.cast (congrArg (fun v ↦ v + 2) (restFaceDimension_eq k n).symm)
      (prefixIndex k n j).succ = prefixIndex (k + 1) n j.succ := Fin.ext rfl

/-- The original successor face-source cast retains the actual original dimensions. -/
def restFaceSourceCast (k n : ℕ) : ⦋k + 1 + n⦌ ⟶ ⦋k + n + 1⦌ :=
  eqToHom (congrArg SimplexCategory.mk (restFaceDimension_eq k n))

/-- The inverse-construction standard map on each original remaining prefix face. -/
def inverseRestFaceStandardMap {X : SSet.{u}} (k n : ℕ) (j : Fin (k + 1))
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    (Δ[k + 1 + n] : SSet.{u}) ⟶ X :=
  SSet.stdSimplex.map (restFaceSourceCast k n) ≫
    zeroJoinStandardTranspose (k + n) (prefixFaceBoundaryInclusion k n j ≫ t)

/-- The actual map on the entire original remaining prefix face, through its native face iso.
-/
def inverseRestFaceMap {X : SSet.{u}} (k n : ℕ) (j : Fin (k + 1))
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    (SSet.stdSimplex.face {prefixIndex (k + 1) n j.succ}ᶜ : SSet.{u}) ⟶ X :=
  (SSet.stdSimplex.faceSingletonComplIso (prefixIndex (k + 1) n j.succ)).inv ≫
    inverseRestFaceStandardMap k n j t

/-- These inverse-construction maps agree on the entire original intersection of every pair.
-/
theorem inverseRestFaceMap_agreement {X : SSet.{u}} (k n : ℕ)
    (j l : Fin (k + 1)) (hjl : j < l)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    SSet.Subcomplex.homOfLE inf_le_left ≫ inverseRestFaceMap k n j t =
      SSet.Subcomplex.homOfLE inf_le_right ≫ inverseRestFaceMap k n l t := by
  by_cases hk : k = 0
  · subst k
    have hj := j.isLt
    have hl := l.isLt
    change j.val < l.val at hjl
    omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hN : 0 < k + n := by omega
    have hindices : prefixIndex k n j < prefixIndex k n l := hjl
    have h := transposed_boundary_face_agreement_of_lt (k + n) hN
      (prefixBoundary k n) (prefixIndex k n j) (prefixIndex k n l) hindices
      (le_iSup (fun j : Fin (k + 1) ↦ SSet.stdSimplex.face {prefixIndex k n j}ᶜ) j)
      (le_iSup (fun j : Fin (k + 1) ↦ SSet.stdSimplex.face {prefixIndex k n j}ᶜ) l) t
    have w := face_intersection_agreement_cast (restFaceDimension_eq k n)
      (prefixIndex k n j).succ (prefixIndex k n l).succ
      (zeroJoinStandardTranspose (k + n) (prefixFaceBoundaryInclusion k n j ≫ t))
      (zeroJoinStandardTranspose (k + n) (prefixFaceBoundaryInclusion k n l ≫ t)) h
    simpa only [restFaceIndex_cast, inverseRestFaceMap, inverseRestFaceStandardMap,
      restFaceSourceCast] using w

end

end DaggerOriginalRestBoundaryInverseFaceMaps
