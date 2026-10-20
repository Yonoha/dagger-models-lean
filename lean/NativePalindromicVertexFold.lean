import NativeRealEdgewiseSymmetry

/-! The palindromic vertex function on the UNCHANGED native ordinal-sum index. -/
set_option autoImplicit false
open CategoryTheory Simplicial AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSymmetry
namespace DaggerNativePalindromicVertexFold

/-- Reverse the left half and retain the right half, with the two central zeroes. -/
def vertex (n : SimplexCategory) (i : Fin ((epsilon.obj n).len + 1)) : Fin (n.len + 1) :=
  Fin.addCases Fin.rev id (Fin.cast (by rw [epsilon_obj_len]; omega) i)

theorem vertex_left (n : SimplexCategory) (i : Fin (n.len + 1)) :
    vertex n ((inl' n n).toOrderHom i) = i.rev := by
  unfold vertex
  rw [inl'_eval]
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [Fin.addCases_left]

theorem vertex_right (n : SimplexCategory) (i : Fin (n.len + 1)) :
    vertex n ((inr' n n).toOrderHom i) = i := by
  unfold vertex
  rw [inr'_eval]
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [Fin.addCases_right]
  rfl

/-- The two existing native injections cover all vertices of the SAME edgewise index. -/
theorem index_cases (n : SimplexCategory) (k : Fin ((epsilon.obj n).len + 1)) :
    (∃ i, k = (inl' n n).toOrderHom i) ∨ (∃ i, k = (inr' n n).toOrderHom i) := by
  by_cases h : k.val < n.len + 1
  · left
    refine ⟨⟨k.val, h⟩, ?_⟩
    apply Fin.ext
    rw [inl'_eval]
    rfl
  · right
    have hk := k.isLt
    change k.val < n.len + n.len + 1 + 1 at hk
    refine ⟨⟨k.val - (n.len + 1), by omega⟩, ?_⟩
    apply Fin.ext
    rw [inr'_eval]
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega

/-- Reversal of the original edgewise simplex fixes the palindromic vertex function. -/
theorem vertex_rev (n : SimplexCategory) (k : Fin ((epsilon.obj n).len + 1)) :
    vertex n k.rev = vertex n k := by
  rcases index_cases n k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [rev_inl, vertex_right, vertex_left]
  · rw [rev_inr, vertex_left, vertex_right, Fin.rev_rev]

/-- Every original simplex operator commutes with the entire palindromic vertex function. -/
theorem vertex_naturality {n m : SimplexCategory} (a : n ⟶ m)
    (k : Fin ((epsilon.obj n).len + 1)) :
    vertex m ((epsilon.map a).toOrderHom k) = a.toOrderHom (vertex n k) := by
  rcases index_cases n k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [epsilon_map_left, vertex_left, vertex_left, SimplexCategory.rev_map_apply, Fin.rev_rev]
    rfl
  · rw [epsilon_map_right, vertex_right, vertex_right]

end DaggerNativePalindromicVertexFold
