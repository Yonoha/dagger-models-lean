import TopCatModelCategory.SSet.PairingCore

/-! A unique codimension-one face which is nondegenerate forces its coface nondegenerate. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeUniqueFaceNondegeneracy

theorem coface_nonDegenerate {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) (y : X _⦋n + 1⦌)
    (hx : x ∈ X.nonDegenerate n) (hxy : SSet.IsUniquelyCodimOneFace x y) :
    y ∈ X.nonDegenerate (n + 1) := by
  obtain ⟨i, hi, hu⟩ : ∃! i : Fin (n + 2), X.δ i y = x := hxy.existsUnique_index
  by_contra hy
  have hy' : y ∈ X.degenerate (n + 1) := by
    simpa only [SSet.mem_degenerate_iff_notMem_nonDegenerate] using hy
  rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hy'
  obtain ⟨j, z, rfl⟩ := hy'
  have hf : X.map ((SimplexCategory.δ i ≫ SimplexCategory.σ j).op) z = x := by
    simpa only [op_comp, FunctorToTypes.map_comp_apply] using hi
  have : Mono (SimplexCategory.δ i ≫ SimplexCategory.σ j) :=
    X.mono_of_nonDegenerate ⟨x, hx⟩ _ z hf
  have he := SimplexCategory.eq_id_of_mono (SimplexCategory.δ i ≫ SimplexCategory.σ j)
  rw [he] at hf
  have hz : z = x := by simpa using hf
  have h₀ : X.δ j.castSucc (X.σ j z) = x :=
    (SSet.δ_comp_σ_self_apply (S := X) j z).trans hz
  have h₁ : X.δ j.succ (X.σ j z) = x :=
    (SSet.δ_comp_σ_succ_apply (S := X) j z).trans hz
  have hj := (hu j.castSucc h₀).trans (hu j.succ h₁).symm
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

end DaggerNativeUniqueFaceNondegeneracy
