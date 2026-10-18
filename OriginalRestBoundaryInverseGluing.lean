import OriginalRestBoundaryInverseFaceMaps

/-!
# Native multicoequalizer construction of the original inverse boundary map

The actual remaining successor prefix boundary is the original union of its
whole omitted-prefix faces. Their verified whole-intersection agreement gives
a native multicofork. Its native colimit constructs the inverse-direction map
with every exact original face restriction equation retained.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalTransposedBoundaryFaceAgreement DaggerOriginalRestBoundaryInverseFaceMaps

universe u

namespace DaggerOriginalRestBoundaryInverseGluing

noncomputable section

/-- The original remaining successor boundary is the native gluing of its actual prefix faces.
-/
theorem restInverseDiagram (k n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram (restPrefixBoundary.{u} k n)
      (fun j : Fin (k + 1) ↦ SSet.stdSimplex.face {prefixIndex (k + 1) n j.succ}ᶜ)
      (fun j l ↦ SSet.stdSimplex.face {prefixIndex (k + 1) n j.succ}ᶜ ⊓
        SSet.stdSimplex.face {prefixIndex (k + 1) n l.succ}ᶜ) := ⟨rfl, fun _ _ ↦ rfl⟩

/-- The actual inverse-direction face maps form the native original multicofork. -/
def inverseRestBoundaryCofork {X : SSet.{u}} (k n : ℕ)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    Multicofork ((restInverseDiagram k n).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j ↦ inverseRestFaceMap k n j t) (fun x ↦ by
    rcases x with ⟨⟨j, l⟩, hjl⟩
    exact inverseRestFaceMap_agreement k n j l hjl t)

/-- The actual map from the whole original remaining boundary, constructed by native gluing. -/
def inverseRestBoundaryMap {X : SSet.{u}} (k n : ℕ)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    (restPrefixBoundary k n : SSet.{u}) ⟶ X :=
  (restInverseDiagram k n).isColimit'.desc (inverseRestBoundaryCofork k n t)

/-- Restriction to each entire original remaining prefix face is the same prescribed map. -/
theorem inverseRestBoundaryMap_face {X : SSet.{u}} (k n : ℕ)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) (j : Fin (k + 1)) :
    SSet.Subcomplex.homOfLE
        (le_iSup (fun a : Fin (k + 1) ↦
          SSet.stdSimplex.face {prefixIndex (k + 1) n a.succ}ᶜ) j) ≫
        inverseRestBoundaryMap k n t = inverseRestFaceMap k n j t :=
  (restInverseDiagram k n).isColimit'.fac (inverseRestBoundaryCofork k n t) (.right j)

/-- The exact original standard coface into the remaining boundary. -/
def restFaceBoundaryInclusion (k n : ℕ) (j : Fin (k + 1)) :
    (Δ[k + 1 + n] : SSet.{u}) ⟶ restPrefixBoundary k n :=
  boundaryFaceInclusion (restPrefixBoundary k n) (prefixIndex (k + 1) n j.succ)
    (le_iSup (fun a : Fin (k + 1) ↦
      SSet.stdSimplex.face {prefixIndex (k + 1) n a.succ}ᶜ) j)

/-- Its ambient operator is the actual original successor prefix coface. -/
theorem restFaceBoundaryInclusion_comp (k n : ℕ) (j : Fin (k + 1)) :
    restFaceBoundaryInclusion.{u} k n j ≫ (restPrefixBoundary k n).ι =
      SSet.stdSimplex.δ (prefixIndex (k + 1) n j.succ) := boundaryFaceInclusion_comp _ _ _

/-- Every actual standard coface restriction of the glued map retains the prescribed data. -/
theorem inverseRestBoundaryMap_standardFace {X : SSet.{u}} (k n : ℕ)
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) (j : Fin (k + 1)) :
    restFaceBoundaryInclusion k n j ≫ inverseRestBoundaryMap k n t =
      inverseRestFaceStandardMap k n j t := by
  rw [restFaceBoundaryInclusion, boundaryFaceInclusion, Category.assoc,
    inverseRestBoundaryMap_face, inverseRestFaceMap, Iso.hom_inv_id_assoc]

end

end DaggerOriginalRestBoundaryInverseGluing
