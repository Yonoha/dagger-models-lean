import NativeFreePathNerveNondegeneracy

/-! Merging the first two positive native paths preserves nondegeneracy. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveNondegeneracy DaggerNativeNerveFrontSubdivision
universe u
namespace DaggerNativeFreePathInnerFaceNondegeneracy

variable {V : Type u} [Quiver.{u + 1} V]

theorem nonDegenerate_iff_front {n : ℕ} (c : ComposableArrows (Paths V) (n + 1)) :
    c ∈ (nerve (Paths V)).nonDegenerate (n + 1) ↔
      0 < (c.map' 0 1).length ∧ c.δ₀ ∈ (nerve (Paths V)).nonDegenerate n := by
  simpa only [reconstruct] using precomp_nonDegenerate_iff c.δ₀ (c.map' 0 1)

theorem delta_one_nonDegenerate {n : ℕ} (c : ComposableArrows (Paths V) (n + 2))
    (hc : c ∈ (nerve (Paths V)).nonDegenerate (n + 2)) :
    (nerve (Paths V)).δ (1 : Fin (n + 3)) c ∈
      (nerve (Paths V)).nonDegenerate (n + 1) := by
  obtain ⟨d, X, f, rfl⟩ := ComposableArrows.precomp_surjective c
  obtain ⟨e, Y, g, rfl⟩ := ComposableArrows.precomp_surjective d
  rw [precomp_nonDegenerate_iff, precomp_nonDegenerate_iff] at hc
  rw [delta_one_precomp_precomp, precomp_nonDegenerate_iff]
  refine ⟨?_, hc.2.2⟩
  change 0 < (f.comp g).length
  rw [Quiver.Path.length_comp]
  omega

theorem first_length_delta_one {n : ℕ} (c : ComposableArrows (Paths V) (n + 2)) :
    ((show ComposableArrows (Paths V) (n + 1) from
      (nerve (Paths V)).δ (1 : Fin (n + 3)) c).map' 0 1).length =
      (c.map' 0 1).length + (c.map' 1 2).length := by
  obtain ⟨d, X, f, rfl⟩ := ComposableArrows.precomp_surjective c
  obtain ⟨e, Y, g, rfl⟩ := ComposableArrows.precomp_surjective d
  rw [delta_one_precomp_precomp]
  exact Quiver.Path.length_comp f g

theorem first_length_delta_one_gt_one {n : ℕ} (c : ComposableArrows (Paths V) (n + 2))
    (hc : c ∈ (nerve (Paths V)).nonDegenerate (n + 2))
    (hf : (c.map' 0 1).length = 1) :
    1 < ((show ComposableArrows (Paths V) (n + 1) from
      (nerve (Paths V)).δ (1 : Fin (n + 3)) c).map' 0 1).length := by
  have ht := (nonDegenerate_iff_front c).mp hc
  have hs := (nonDegenerate_iff_front c.δ₀).mp ht.2
  have hp : 0 < (c.map' 1 2).length := hs.1
  rw [first_length_delta_one, hf]
  omega

theorem nonDegenerate_iff_adjacent_positive {n : ℕ} (c : ComposableArrows (Paths V) n) :
    c ∈ (nerve (Paths V)).nonDegenerate n ↔
      ∀ i : Fin n, 0 < (c.map (homOfLE (Fin.castSucc_le_succ i))).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [nonDegenerate_iff_front, ih]
    constructor
    · rintro ⟨hf, ht⟩ i
      cases i using Fin.cases with
      | zero => exact hf
      | succ i => exact ht i
    · intro h
      exact ⟨h 0, fun i ↦ h i.succ⟩

end DaggerNativeFreePathInnerFaceNondegeneracy
