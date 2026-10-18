import NativePartialFaceUnionContraction
import NativeWeaklyContractibleMaps

/-! The actual intersection-to-old-face-union arrow is anodyne in a proper attachment. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativePartialFaceUnionGeometry DaggerNativePartialFaceUnionContraction
open DaggerNativeWeaklyContractibleMaps
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePartialFaceAttachmentAnodyne
noncomputable section

theorem faceIndices_nonempty {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2))
    (hi : i ∉ S) (hS : S.Nonempty) : (faceIndices S i).Nonempty := by
  obtain ⟨j, hj⟩ := hS
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (show j ≠ i from fun h ↦ hi (h ▸ hj))
  exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl ▸ hj⟩⟩

theorem faceIndices_missing {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2))
    (k : Fin (n + 2)) (hk : k ∉ S) (hki : k ≠ i) :
    ∃ l : Fin (n + 1), i.succAbove l = k ∧ l ∉ faceIndices S i := by
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hki
  refine ⟨l, hl, ?_⟩
  intro h
  exact hk (hl ▸ (Finset.mem_filter.mp h).2)

theorem faceUnion_collapse_weak {n : ℕ} (S : Finset (Fin (n + 1))) (k : Fin (n + 1))
    (hk : k ∉ S) (hS : S.Nonempty) : WeakEquivalence (collapse (faceUnion.{u} S)) :=
  collapse_weak_of_const _ (constant_weak S k hk hS)

theorem intersection_collapse_weak {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2))
    (hi : i ∉ S) (k : Fin (n + 2)) (hk : k ∉ S) (hki : k ≠ i) (hS : S.Nonempty) :
    WeakEquivalence (collapse ((faceUnion.{u} S).preimage (SSet.stdSimplex.δ i))) := by
  rw [faceUnion_preimage_face S i hi]
  obtain ⟨l, hl, hlS⟩ := faceIndices_missing S i k hk hki
  exact faceUnion_collapse_weak (faceIndices S i) l hlS (faceIndices_nonempty S i hi hS)

theorem intersection_to_old_mono {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2)) :
    Mono ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := by
  exact mono_of_mono_fac (show (faceUnion S).fromPreimage (SSet.stdSimplex.δ i) ≫
    (faceUnion S).ι = ((faceUnion S).preimage (SSet.stdSimplex.δ i)).ι ≫
      SSet.stdSimplex.δ i from rfl)

theorem intersection_to_old_weak {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2))
    (hi : i ∉ S) (k : Fin (n + 2)) (hk : k ∉ S) (hki : k ≠ i) (hS : S.Nonempty) :
    WeakEquivalence ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) :=
  map_weak _ (intersection_collapse_weak S i hi k hk hki hS)
    (faceUnion_collapse_weak S k hk hS)

theorem intersection_to_old_trivial_cofibration {n : ℕ} (S : Finset (Fin (n + 2)))
    (i : Fin (n + 2)) (hi : i ∉ S) (k : Fin (n + 2)) (hk : k ∉ S)
    (hki : k ≠ i) (hS : S.Nonempty) :
    trivialCofibrations SSet.{u} ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) := by
  have : Mono ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i)) :=
    intersection_to_old_mono S i
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨(SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance,
      intersection_to_old_weak S i hi k hk hki hS⟩

end
end DaggerNativePartialFaceAttachmentAnodyne
