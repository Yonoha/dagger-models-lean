import NativePositivePartialMatchingPi
import NativeHorizontalPiRebasedRestriction
import NativeHorizontalPushoutComponents

/-! Positive pi lifts give the actual component pullback formula at every face attachment. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativePartialFaceUnionGeometry
open DaggerNativePartialFaceAttachmentAnodyne DaggerNativeReedyFibrantHorizontalMapping
open DaggerNativePositivePartialMatchingPi DaggerNativeHorizontalPiRebasedRestriction
open DaggerNativeHorizontalPushoutComponents
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePartialFaceAttachmentComponents
noncomputable section

theorem attachment_restriction_mapπ_surjective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (n : ℕ) (S : Finset (Fin (n + 2))) (i : Fin (n + 2)) (hi : i ∉ S)
    (k : Fin (n + 2)) (hk : k ∉ S) (hki : k ≠ i) (hS : S.Nonempty) (q : ℕ)
    (e : (horizontalMapping (faceUnion.{u} S) X) _⦋0⦌)
    (d : (horizontalMapping ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X) _⦋0⦌)
    (he : (horizontalPre ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) X).app _ e = d) :
    Function.Surjective (mapπ
      (horizontalPre ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) X)
      (q + 1) e d he) := by
  have hP : ∀ (r : ℕ)
      (w : (horizontalMapping ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X) _⦋0⦌),
      Function.Bijective (piComparison
        ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X (r + 1) w) := by
    rw [faceUnion_preimage_face S i hi]
    obtain ⟨l, hl, hlS⟩ := faceIndices_missing S i k hk hki
    exact partialFace_piComparison_bijective X hX hπ n (faceIndices S i) l hlS
      (faceIndices_nonempty S i hi hS)
  have ht := (mem_trivialCofibrations_iff _).mp
    (intersection_to_old_trivial_cofibration S i hi k hk hki hS)
  have : Cofibration ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := ht.1
  have : WeakEquivalence ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := ht.2
  have : Fibration (C := SSet.{u}) (rowProjection X (q + 1)) := hπ q
  exact restriction_mapπ_surjective_rebased
    ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) X (q + 1) e d he
    (partialFace_piComparison_bijective X hX hπ (n + 1) S k hk hS q e).2 (hP q d).1

theorem attachment_component_pullback_bijective (X : BiSSet.{u}) (hX : ReedyFibrant X)
    (hπ : ∀ r : ℕ, Fibration (C := SSet.{u}) (rowProjection X (r + 1)))
    (n : ℕ) (S : Finset (Fin (n + 2))) (i : Fin (n + 2)) (hi : i ∉ S)
    (k : Fin (n + 2)) (hk : k ∉ S) (hki : k ≠ i) (hS : S.Nonempty) :
    Function.Bijective
      (mappingComponentsComparison (faceUnion_attachment_isPushout S i) X) := by
  have : Mono ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) :=
    intersection_to_old_mono S i
  have : Fibration (horizontalPre
      ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) X) :=
    DaggerNativeReedyFibrantHorizontalMapping.restriction_fibration X hX _
  have : IsFibrant (horizontalMapping
      ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i)) X) := mapping_isFibrant X hX _
  have : IsFibrant (horizontalMapping (Δ[n] : SSet.{u}) X) := mapping_isFibrant X hX _
  exact mappingComponentsComparison_bijective (faceUnion_attachment_isPushout S i) X
    (attachment_restriction_mapπ_surjective X hX hπ n S i hi k hk hki hS 0)

end
end DaggerNativePartialFaceAttachmentComponents
