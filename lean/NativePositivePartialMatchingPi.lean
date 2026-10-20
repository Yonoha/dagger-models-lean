import NativePartialFaceAttachmentAnodyne
import NativeReedyFibrantHorizontalMapping
import NativeHorizontalPiParameterIso
import NativeHorizontalPushoutPiInduction

/-! The canonical positive-pi comparison for every proper nonempty original face union. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativePartialFaceUnionGeometry
open DaggerNativePartialFaceAttachmentAnodyne DaggerNativeReedyFibrantHorizontalMapping
open DaggerNativeHorizontalPiParameterIso DaggerNativeHorizontalPushoutPiInduction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePositivePartialMatchingPi
noncomputable section

theorem partialFace_piComparison_bijective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1))) :
    ∀ (m : ℕ) (S : Finset (Fin (m + 1))) (k : Fin (m + 1)), k ∉ S → S.Nonempty →
      ∀ (q : ℕ) (v : (horizontalMapping (faceUnion.{u} S) X) _⦋0⦌),
        Function.Bijective (piComparison (faceUnion.{u} S) X (q + 1) v) := by
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
      intro k hk hS q v
      have hkS : k ∉ S := fun h ↦ hk (Finset.mem_insert_of_mem h)
      have hki : k ≠ i := by
        rintro rfl
        exact hk (Finset.mem_insert_self _ _)
      by_cases hS0 : S.Nonempty
      · have hP : ∀ (r : ℕ)
            (w : (horizontalMapping ((faceUnion.{u} S).preimage
              (SSet.stdSimplex.δ i)) X) _⦋0⦌),
            Function.Bijective (piComparison
              ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X (r + 1) w) := by
          rw [faceUnion_preimage_face S i hi]
          obtain ⟨l, hl, hlS⟩ := faceIndices_missing S i k hkS hki
          exact hm (faceIndices S i) l hlS (faceIndices_nonempty S i hi hS0)
        have : Mono ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) :=
          intersection_to_old_mono S i
        have : Fibration (horizontalPre
            ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) X) :=
          DaggerNativeReedyFibrantHorizontalMapping.restriction_fibration X hX _
        have : IsFibrant (horizontalMapping
            ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X) :=
          mapping_isFibrant X hX _
        have : IsFibrant (horizontalMapping (Δ[m] : SSet.{u}) X) :=
          mapping_isFibrant X hX _
        have ht := (mem_trivialCofibrations_iff _).mp
          (intersection_to_old_trivial_cofibration S i hi k hkS hki hS0)
        have : Cofibration ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := ht.1
        have : WeakEquivalence ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := ht.2
        have : Fibration (C := SSet.{u}) (rowProjection X (q + 2)) := hπ (q + 1)
        exact piComparison_bijective_of_anodyne_pushout (faceUnion_attachment_isPushout S i)
          X v q (hP q _).1 (ih k hkS hS0 q _) (simplex_piComparison_bijective X m (q + 1) _)
          (hP (q + 1) _).1 (ih k hkS hS0 (q + 1) _).2
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS0
        subst S
        exact singletonFace_piComparison_bijective m i X (q + 1) v

end
end DaggerNativePositivePartialMatchingPi
