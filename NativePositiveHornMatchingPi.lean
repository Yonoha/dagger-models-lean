import NativePositivePartialMatchingRestriction
import NativeHornAsPartialFaceUnion

/-! Canonical positive pi comparison and actual horn-restriction surjectivity at all vertices. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativePartialFaceUnionGeometry
open DaggerNativeReedyFibrantHorizontalMapping DaggerNativePositivePartialMatchingPi
open DaggerNativePositivePartialMatchingRestriction DaggerNativeHornAsPartialFaceUnion
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePositiveHornMatchingPi
noncomputable section

theorem horn_piComparison_bijective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (m : ℕ) (k : Fin (m + 2)) (q : ℕ)
    (v : (horizontalMapping (SSet.horn.{u} (m + 1) k) X) _⦋0⦌) :
    Function.Bijective (piComparison (SSet.horn.{u} (m + 1) k) X (q + 1) v) := by
  have hf := partialFace_piComparison_bijective X hX hπ (m + 1) (Finset.univ.erase k) k
    (Finset.notMem_erase k _) (horn_face_indices_nonempty m k)
  rw [faceUnion_erase_eq_horn] at hf
  exact hf q v

theorem horn_restriction_mapπ_surjective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (m : ℕ) (k : Fin (m + 2)) (q : ℕ)
    (v : (horizontalMapping (Δ[m + 1] : SSet.{u}) X) _⦋0⦌) :
    Function.Surjective (mapπ (horizontalPre (SSet.horn.{u} (m + 1) k).ι X) (q + 1) v
      ((horizontalPre (SSet.horn.{u} (m + 1) k).ι X).app _ v) rfl) := by
  have hf : ∀ w : (horizontalMapping (Δ[m + 1] : SSet.{u}) X) _⦋0⦌,
      Function.Surjective (mapπ (horizontalPre (faceUnion.{u} (Finset.univ.erase k)).ι X)
        (q + 1) w ((horizontalPre (faceUnion.{u} (Finset.univ.erase k)).ι X).app _ w) rfl) :=
    fun w ↦ partialFace_restriction_mapπ_surjective X hX hπ (m + 1)
      (Finset.univ.erase k) k (Finset.notMem_erase k _) (horn_face_indices_nonempty m k) q w
  rw [faceUnion_erase_eq_horn] at hf
  exact hf v

theorem horn_restriction_mapπ_surjective_rebased (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (m : ℕ) (k : Fin (m + 2)) (q : ℕ)
    (v : (horizontalMapping (Δ[m + 1] : SSet.{u}) X) _⦋0⦌)
    (w : (horizontalMapping (SSet.horn.{u} (m + 1) k) X) _⦋0⦌)
    (hw : (horizontalPre (SSet.horn.{u} (m + 1) k).ι X).app _ v = w) :
    Function.Surjective
      (mapπ (horizontalPre (SSet.horn.{u} (m + 1) k).ι X) (q + 1) v w hw) := by
  subst w
  exact horn_restriction_mapπ_surjective X hX hπ m k q v

end
end DaggerNativePositiveHornMatchingPi
