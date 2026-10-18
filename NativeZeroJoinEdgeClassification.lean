import OriginalJoinedCofaces
import Mathlib.Tactic.FinCases

/-! Every edge of the native vertex join is a prefix edge, a mapping vertex, or a suffix edge. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedCofaces
namespace DaggerNativeZeroJoinEdgeClassification

theorem edge_cases (n : ℕ) (α : ⦋1⦌ ⟶ (ordinalJoinLeft ⦋0⦌).obj ⦋n⦌) :
    α = SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫ AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌ ∨
      (∃ β : ⦋0⦌ ⟶ ⦋n⦌, α = (ordinalJoinLeft ⦋0⦌).map β) ∨
      ∃ β : ⦋1⦌ ⟶ ⦋n⦌, α = β ≫ AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌ := by
  rcases vertex_eq_prefix_or_suffix 0 n (α.toOrderHom 0) with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ea : a = 0 := Fin.ext (by have h := a.isLt; omega)
    subst a
    rcases vertex_eq_prefix_or_suffix 0 n (α.toOrderHom 1) with ⟨b, hb⟩ | ⟨b, hb⟩
    · have eb : b = 0 := Fin.ext (by have h := b.isLt; omega)
      subst b
      left
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      fin_cases i
      · change α.toOrderHom 0 = (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌).toOrderHom 0
        rw [← prefixIndex_eq_native]
        exact ha
      · change α.toOrderHom 1 = (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌).toOrderHom 0
        rw [← prefixIndex_eq_native]
        exact hb
    · right
      left
      refine ⟨SimplexCategory.const ⦋0⦌ ⦋n⦌ b, ?_⟩
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      fin_cases i
      · change α.toOrderHom 0 = ((ordinalJoinLeft ⦋0⦌).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ b)).toOrderHom (prefixIndex 0 0 0)
        rw [joinMap_prefix_eval]
        exact ha
      · change α.toOrderHom 1 = ((ordinalJoinLeft ⦋0⦌).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ b)).toOrderHom (suffixIndex 0 0 0)
        rw [joinMap_suffix_eval]
        exact hb
  · rcases vertex_eq_prefix_or_suffix 0 n (α.toOrderHom 1) with ⟨b, hb⟩ | ⟨b, hb⟩
    · have hm := α.toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)
      rw [ha, hb] at hm
      have hv : 0 + 1 + a.val ≤ b.val := hm
      have hblt := b.isLt
      omega
    · right
      right
      have hab : a ≤ b := by
        have hm := α.toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)
        rw [ha, hb] at hm
        change 0 + 1 + a.val ≤ 0 + 1 + b.val at hm
        exact show a.val ≤ b.val by omega
      let β : ⦋1⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom
        ⟨fun i ↦ if i = 0 then a else b, by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all⟩
      refine ⟨β, ?_⟩
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      fin_cases i
      · change α.toOrderHom 0 = (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).toOrderHom a
        rw [← suffixIndex_eq_native]
        exact ha
      · change α.toOrderHom 1 = (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).toOrderHom b
        rw [← suffixIndex_eq_native]
        exact hb

end DaggerNativeZeroJoinEdgeClassification
