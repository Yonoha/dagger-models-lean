import OriginalPrefixDeleteFirstCoface

/-!
# The actual first-prefix coface is the original native ordinal-join map

The coface with its explicit dimension cast equals the native tensor of the
prefix zero coface and the suffix identity. Native block equations prove this
on every original vertex. Tensor interchange gives the exact naturality square
in every original prefix and suffix dimension.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces
open DaggerOriginalPrefixDeleteFirstCoface

namespace DaggerOriginalPrefixDeleteFirstNativeJoin

/-- The original native ordinal-sum map deleting the first prefix vertex. -/
def nativePrefixDeleteFirst (k n : ℕ) : ⦋k + n + 1⦌ ⟶ ⦋k + 1 + n + 1⦌ :=
  AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ (n := k) 0) (𝟙 ⦋n⦌)

/-- The native map shifts each original prefix vertex by one. -/
theorem nativePrefixDeleteFirst_prefix_eval (k n : ℕ) (a : Fin (k + 1)) :
    ((nativePrefixDeleteFirst k n).toOrderHom (prefixIndex k n a)).val = a.val + 1 := by
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (show WithInitial.of ⦋k⦌ ⟶ WithInitial.of ⦋k + 1⦌ from SimplexCategory.δ 0)
    (𝟙 (WithInitial.of ⦋n⦌))
  change AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌ ≫ nativePrefixDeleteFirst k n =
    SimplexCategory.δ 0 ≫ AugmentedSimplexCategory.inl' ⦋k + 1⦌ ⦋n⦌ at h
  have hv := congrArg (fun f ↦ (f.toOrderHom a).val) h
  change ((nativePrefixDeleteFirst k n).toOrderHom
    ((AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌).toOrderHom a)).val =
      ((AugmentedSimplexCategory.inl' ⦋k + 1⦌ ⦋n⦌).toOrderHom
        ((SimplexCategory.δ (n := k) 0).toOrderHom a)).val at hv
  rw [← prefixIndex_eq_native k n a, AugmentedSimplexCategory.inl'_eval] at hv
  change ((nativePrefixDeleteFirst k n).toOrderHom (prefixIndex k n a)).val =
    ((0 : Fin (k + 2)).succAbove a).val at hv
  rw [Fin.succAbove_zero] at hv
  exact hv

/-- The native map shifts each original suffix vertex by one, retaining its own block index. -/
theorem nativePrefixDeleteFirst_suffix_eval (k n : ℕ) (a : Fin (n + 1)) :
    ((nativePrefixDeleteFirst k n).toOrderHom (suffixIndex k n a)).val =
      k + 1 + 1 + a.val := by
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (show WithInitial.of ⦋k⦌ ⟶ WithInitial.of ⦋k + 1⦌ from SimplexCategory.δ 0)
    (𝟙 (WithInitial.of ⦋n⦌))
  change AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌ ≫ nativePrefixDeleteFirst k n =
    𝟙 ⦋n⦌ ≫ AugmentedSimplexCategory.inr' ⦋k + 1⦌ ⦋n⦌ at h
  rw [Category.id_comp] at h
  have hv := congrArg (fun f ↦ (f.toOrderHom a).val) h
  change ((nativePrefixDeleteFirst k n).toOrderHom
    ((AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌).toOrderHom a)).val =
      ((AugmentedSimplexCategory.inr' ⦋k + 1⦌ ⦋n⦌).toOrderHom a).val at hv
  rw [← suffixIndex_eq_native k n a, AugmentedSimplexCategory.inr'_eval] at hv
  exact hv

/-- The explicit original coface is the actual native prefix tensor map, with its casts retained.
-/
theorem prefixDeleteFirstOperator_eq_native (k n : ℕ) :
    prefixDeleteFirstOperator k n = nativePrefixDeleteFirst k n := by
  ext i : 3
  apply Fin.ext
  rw [prefixDeleteFirstOperator_eval]
  rcases vertex_eq_prefix_or_suffix k n i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [nativePrefixDeleteFirst_prefix_eval]
    rfl
  · rw [nativePrefixDeleteFirst_suffix_eval]
    change k + 1 + a.val + 1 = k + 1 + 1 + a.val
    omega

/-- The first-prefix coface commutes with every original suffix operator under the same join. -/
theorem prefixDeleteFirstOperator_naturality (k : ℕ) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (ordinalJoinLeft ⦋k⦌).map α ≫ prefixDeleteFirstOperator k n =
      prefixDeleteFirstOperator k m ≫ (ordinalJoinLeft ⦋k + 1⦌).map α := by
  rw [prefixDeleteFirstOperator_eq_native, prefixDeleteFirstOperator_eq_native]
  have h₁ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
    (𝟙 (WithInitial.of ⦋k⦌))
    (show WithInitial.of ⦋m⦌ ⟶ WithInitial.of ⦋n⦌ from α)
    (show WithInitial.of ⦋k⦌ ⟶ WithInitial.of ⦋k + 1⦌ from SimplexCategory.δ 0)
    (𝟙 (WithInitial.of ⦋n⦌))
  have h₂ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
    (show WithInitial.of ⦋k⦌ ⟶ WithInitial.of ⦋k + 1⦌ from SimplexCategory.δ 0)
    (𝟙 (WithInitial.of ⦋m⦌)) (𝟙 (WithInitial.of ⦋k + 1⦌))
    (show WithInitial.of ⦋m⦌ ⟶ WithInitial.of ⦋n⦌ from α)
  change (ordinalJoinLeft ⦋k⦌).map α ≫ nativePrefixDeleteFirst k n =
    AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋k⦌ ≫ SimplexCategory.δ 0) (α ≫ 𝟙 ⦋n⦌) at h₁
  change nativePrefixDeleteFirst k m ≫ (ordinalJoinLeft ⦋k + 1⦌).map α =
    AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ 0 ≫ 𝟙 ⦋k + 1⦌)
      (𝟙 ⦋m⦌ ≫ α) at h₂
  simp only [Category.id_comp, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

end DaggerOriginalPrefixDeleteFirstNativeJoin
