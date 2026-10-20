import NativeComponentMatchingGluing
import NativePartialFaceAttachmentComponents
import NativeHornAsPartialFaceUnion

/-! Full canonical component matching comparison for proper nonempty face unions and horns. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiSections
open DaggerNativePartialFaceUnionGeometry DaggerNativePartialFaceAttachmentAnodyne
open DaggerNativeReedyFibrantHorizontalMapping DaggerNativeComponentPartialMatchingComparison
open DaggerNativeComponentMatchingGluing DaggerNativePartialFaceAttachmentComponents
open DaggerNativeHornAsPartialFaceUnion
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeComponentPartialMatchingPi
noncomputable section

theorem partialFace_componentComparison_bijective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1))) :
    ∀ (m : ℕ) (S : Finset (Fin (m + 1))) (k : Fin (m + 1)), k ∉ S → S.Nonempty →
      Function.Bijective (componentComparison (faceUnion.{u} S) X) := by
  intro m
  induction m with
  | zero =>
    intro S k hk hS
    obtain ⟨j, hj⟩ := hS
    have hjk : j = k := Fin.ext (by omega)
    exact False.elim (hk (hjk ▸ hj))
  | succ m hm =>
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro k hk hS
      exact False.elim (Finset.not_nonempty_empty hS)
    | @insert i S hi ih =>
      intro k hk hS
      have hkS : k ∉ S := fun h ↦ hk (Finset.mem_insert_of_mem h)
      have hki : k ≠ i := by
        rintro rfl
        exact hk (Finset.mem_insert_self _ _)
      by_cases hS0 : S.Nonempty
      · have hP : Function.Bijective (componentComparison
            ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X) := by
          rw [faceUnion_preimage_face S i hi]
          obtain ⟨l, hl, hlS⟩ := faceIndices_missing S i k hkS hki
          exact hm (faceIndices S i) l hlS (faceIndices_nonempty S i hi hS0)
        exact componentComparison_bijective_of_pushout (faceUnion_attachment_isPushout S i) X
          hP.1 (ih k hkS hS0) (simplex_componentComparison_bijective X m)
          (attachment_component_pullback_bijective X hX hπ m S i hi k hkS hki hS0)
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS0
        subst S
        exact singletonFace_componentComparison_bijective m i X

theorem horn_componentComparison_bijective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1)))
    (m : ℕ) (k : Fin (m + 2)) :
    Function.Bijective (componentComparison (SSet.horn.{u} (m + 1) k) X) := by
  have hf := partialFace_componentComparison_bijective X hX hπ (m + 1)
    (Finset.univ.erase k) k (Finset.notMem_erase k _) (horn_face_indices_nonempty m k)
  rw [faceUnion_erase_eq_horn] at hf
  exact hf

end
end DaggerNativeComponentPartialMatchingPi
