import OriginalPrefixBoundaryConeTransposition

/-!
# Native vertex join and the exact shifted standard cofaces

The native join with the zero simplex identifies with the successor ordinal
through its explicit original dimension equality. Under this identification,
every native joined coface is the original coface with successor index. Both
original left and right block evaluations and all casts are retained.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces

namespace DaggerOriginalZeroJoinStandardCofaces

/-- The native vertex-joined original ordinal with its explicit original dimension cast. -/
def zeroJoinStandardIso (n : ℕ) : (ordinalJoinLeft ⦋0⦌).obj ⦋n⦌ ≅ ⦋n + 1⦌ :=
  eqToIso (congrArg SimplexCategory.mk (show 0 + n + 1 = n + 1 by omega))

/-- The original dimension cast preserves the value of every actual vertex. -/
theorem zeroJoinStandardIso_hom_eval (n : ℕ) (j : Fin (0 + n + 2)) :
    ((zeroJoinStandardIso n).hom.toOrderHom j).val = j.val := by
  rw [zeroJoinStandardIso, eqToIso.hom, SimplexCategory.eqToHom_toOrderHom]
  rfl

/-- The cast of the native apex is the original successor vertex zero. -/
theorem zeroJoinStandardIso_prefix_eval (n : ℕ) (j : Fin 1) :
    (zeroJoinStandardIso n).hom.toOrderHom (prefixIndex 0 n j) = 0 := by
  apply Fin.ext
  rw [zeroJoinStandardIso_hom_eval]
  change j.val = 0
  have hj := j.isLt
  omega

/-- The cast of the native suffix vertex is the original successor-index vertex. -/
theorem zeroJoinStandardIso_suffix_eval (n : ℕ) (j : Fin (n + 1)) :
    (zeroJoinStandardIso n).hom.toOrderHom (suffixIndex 0 n j) = j.succ := by
  apply Fin.ext
  rw [zeroJoinStandardIso_hom_eval]
  change 0 + 1 + j.val = j.val + 1
  omega

/-- Every original joined coface is exactly the original coface with successor index. -/
theorem zeroJoinStandardIso_coface (n : ℕ) (i : Fin (n + 2)) :
    (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i) ≫
        (zeroJoinStandardIso (n + 1)).hom =
      (zeroJoinStandardIso n).hom ≫ SimplexCategory.δ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  rcases vertex_eq_prefix_or_suffix 0 n j with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · change (zeroJoinStandardIso (n + 1)).hom.toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i)).toOrderHom (prefixIndex 0 n a)) =
        i.succ.succAbove ((zeroJoinStandardIso n).hom.toOrderHom (prefixIndex 0 n a))
    rw [joinMap_prefix_eval, zeroJoinStandardIso_prefix_eval, zeroJoinStandardIso_prefix_eval]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change 0 < i.val + 1; omega)]
    rfl
  · change (zeroJoinStandardIso (n + 1)).hom.toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ i)).toOrderHom (suffixIndex 0 n a)) =
        i.succ.succAbove ((zeroJoinStandardIso n).hom.toOrderHom (suffixIndex 0 n a))
    rw [joinMap_suffix_eval, zeroJoinStandardIso_suffix_eval, zeroJoinStandardIso_suffix_eval]
    change (i.succAbove a).succ = i.succ.succAbove a.succ
    by_cases h : a.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i a h,
        Fin.succAbove_of_castSucc_lt i.succ a.succ (by
          change a.val + 1 < i.val + 1
          change a.val < i.val at h
          omega)]
      rfl
    · have hh : i ≤ a.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc i a hh,
        Fin.succAbove_of_le_castSucc i.succ a.succ (by
          change i.val + 1 ≤ a.val + 1
          change i.val ≤ a.val at hh
          omega)]

end DaggerOriginalZeroJoinStandardCofaces
