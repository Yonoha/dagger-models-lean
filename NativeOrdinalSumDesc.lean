import NativeRealEdgewiseIndex

/-! Maps from Mathlib's ordinal sum, specified by two separated monotone maps. -/
set_option autoImplicit false
open CategoryTheory AugmentedSimplexCategory
namespace DaggerNativeOrdinalSumDesc

def desc {x y z : SimplexCategory} (l : x ⟶ z) (r : y ⟶ z)
    (h : ∀ i j, l.toOrderHom i ≤ r.toOrderHom j) : tensorObjOf x y ⟶ z :=
  let g : Fin ((x.len + 1) + (y.len + 1)) →o Fin (z.len + 1) :=
    { toFun := Fin.addCases l.toOrderHom r.toOrderHom
      monotone' i j hij := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at hij ⊢ <;>
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.addCases_left,
          Fin.addCases_right] at hij ⊢
        · exact l.toOrderHom.monotone hij
        · exact h _ _
        · omega
        · exact r.toOrderHom.monotone (by omega) }
  eqToHom (congrArg SimplexCategory.mk (Nat.succ_add x.len y.len)).symm ≫
    SimplexCategory.mkHom g

theorem desc_left {x y z : SimplexCategory} (l : x ⟶ z) (r : y ⟶ z)
    (h : ∀ i j, l.toOrderHom i ≤ r.toOrderHom j) (i : Fin (x.len + 1)) :
    (desc l r h).toOrderHom ((inl' x y).toOrderHom i) = l.toOrderHom i := by
  dsimp [desc]
  have he := inl'_eval x y i
  simp only [SimplexCategory.len_mk] at he
  rw [he]
  simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.cast_cast, Fin.cast_eq_self]
  change Fin.addCases (motive := fun _ ↦ Fin (z.len + 1))
    l.toOrderHom r.toOrderHom (i.castAdd (y.len + 1)) = l.toOrderHom i
  rw [Fin.addCases_left]

theorem desc_right {x y z : SimplexCategory} (l : x ⟶ z) (r : y ⟶ z)
    (h : ∀ i j, l.toOrderHom i ≤ r.toOrderHom j) (i : Fin (y.len + 1)) :
    (desc l r h).toOrderHom ((inr' x y).toOrderHom i) = r.toOrderHom i := by
  dsimp [desc]
  have he := inr'_eval x y i
  simp only [SimplexCategory.len_mk] at he
  rw [he]
  simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    Nat.succ_eq_add_one, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.cast_cast, Fin.cast_eq_self]
  change Fin.addCases (motive := fun _ ↦ Fin (z.len + 1))
    l.toOrderHom r.toOrderHom (i.natAdd (x.len + 1)) = r.toOrderHom i
  rw [Fin.addCases_right]

end DaggerNativeOrdinalSumDesc
