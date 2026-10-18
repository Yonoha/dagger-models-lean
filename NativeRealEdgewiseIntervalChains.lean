import NativeOrdinalSumDesc
import NativeRealEdgewiseSymmetry
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Original edgewise simplices as chains of nonempty finite closed intervals. -/
set_option autoImplicit false
open CategoryTheory AugmentedSimplexCategory Simplicial
open DaggerNativeRealEdgewiseIndex DaggerNativeOrdinalSumDesc
universe u
namespace DaggerNativeRealEdgewiseIntervalChains

abbrev Interval (n : ℕ) : Type :=
  {p : OrderDual (Fin (n + 1)) × Fin (n + 1) // OrderDual.ofDual p.1 ≤ p.2}

instance intervalOrderTop (n : ℕ) : OrderTop (Interval n) where
  top := ⟨(OrderDual.toDual 0, Fin.last n), Fin.zero_le _⟩
  le_top _ := ⟨Fin.zero_le _, Fin.le_last _⟩

theorem inl_le_inr (m : SimplexCategory) (i j : Fin (m.len + 1)) :
    (inl' m m).toOrderHom i ≤ (inr' m m).toOrderHom j := by
  rw [inl'_eval, inr'_eval]
  change i.val ≤ m.len + 1 + j.val
  omega

def intervalAt {n : ℕ} {m : SimplexCategory} (f : epsilon.obj m ⟶ ⦋n⦌)
    (i : Fin (m.len + 1)) : Interval n :=
  ⟨(OrderDual.toDual (f.toOrderHom ((inl' m m).toOrderHom i.rev)),
    f.toOrderHom ((inr' m m).toOrderHom i)), f.toOrderHom.monotone (inl_le_inr m _ _)⟩

theorem intervalAt_monotone {n : ℕ} {m : SimplexCategory}
    (f : epsilon.obj m ⟶ ⦋n⦌) : Monotone (intervalAt f) := by
  intro i j hij
  constructor
  · exact f.toOrderHom.monotone ((inl' m m).toOrderHom.monotone (Fin.rev_le_rev.mpr hij))
  · exact f.toOrderHom.monotone ((inr' m m).toOrderHom.monotone hij)

def toChain {n : ℕ} {m : SimplexCategory} (f : epsilon.obj m ⟶ ⦋n⦌) :
    Fin (m.len + 1) ⥤ ULift.{u} (Interval n) :=
  (show Monotone (fun i ↦ ULift.up (intervalAt f i)) from intervalAt_monotone f).functor

def leftMap {n : ℕ} {m : SimplexCategory}
    (s : Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) : m ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun i := OrderDual.ofDual (s.obj i.rev).down.val.1
      monotone' _ _ hij := (s.monotone (Fin.rev_le_rev.mpr hij)).1 }

def rightMap {n : ℕ} {m : SimplexCategory}
    (s : Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) : m ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun i := (s.obj i).down.val.2
      monotone' _ _ hij := (s.monotone hij).2 }

theorem leftMap_le_rightMap {n : ℕ} {m : SimplexCategory}
    (s : Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) (i j : Fin (m.len + 1)) :
    (leftMap s).toOrderHom i ≤ (rightMap s).toOrderHom j := by
  have hl : (leftMap s).toOrderHom i ≤ OrderDual.ofDual (s.obj 0).down.val.1 :=
    (s.monotone (Fin.zero_le i.rev)).1
  exact hl.trans ((s.obj 0).down.property.trans (s.monotone (Fin.zero_le j)).2)

def fromChain {n : ℕ} {m : SimplexCategory}
    (s : Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) : epsilon.obj m ⟶ ⦋n⦌ :=
  desc (leftMap s) (rightMap s) (leftMap_le_rightMap s)

theorem fromChain_toChain {n : ℕ} {m : SimplexCategory} (f : epsilon.obj m ⟶ ⦋n⦌) :
    fromChain (toChain.{u} f) = f := by
  apply DaggerNativeRealEdgewiseSymmetry.hom_ext
  · ext i : 3
    change (fromChain (toChain.{u} f)).toOrderHom ((inl' m m).toOrderHom i) = _
    exact (desc_left (leftMap (toChain.{u} f)) (rightMap (toChain.{u} f))
      (leftMap_le_rightMap (toChain.{u} f)) i).trans (by
        change f.toOrderHom ((inl' m m).toOrderHom i.rev.rev) =
          f.toOrderHom ((inl' m m).toOrderHom i)
        rw [Fin.rev_rev])
  · ext i : 3
    change (fromChain (toChain.{u} f)).toOrderHom ((inr' m m).toOrderHom i) = _
    exact desc_right (leftMap (toChain.{u} f)) (rightMap (toChain.{u} f))
      (leftMap_le_rightMap (toChain.{u} f)) i

theorem toChain_fromChain {n : ℕ} {m : SimplexCategory}
    (s : Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) : toChain (fromChain s) = s := by
  apply nerve.ext_of_isThin
  funext i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change (fromChain s).toOrderHom ((inl' m m).toOrderHom i.rev) = _
    exact (desc_left (leftMap s) (rightMap s) (leftMap_le_rightMap s) i.rev).trans (by
      change OrderDual.ofDual (s.obj i.rev.rev).down.val.1 =
        OrderDual.ofDual (s.obj i).down.val.1
      rw [Fin.rev_rev])
  · change (fromChain s).toOrderHom ((inr' m m).toOrderHom i) = _
    exact desc_right (leftMap s) (rightMap s) (leftMap_le_rightMap s) i

end DaggerNativeRealEdgewiseIntervalChains
