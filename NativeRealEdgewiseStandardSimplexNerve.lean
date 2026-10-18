import NativeRealEdgewiseIntervalChains
import NativeRealEdgewiseSSet
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! The original edgewise standard simplex is the native nerve of its interval poset.
The comparison is natural for every simplex operator, not only faces and degeneracies.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
open DaggerNativeRealEdgewiseIntervalChains
universe u
namespace DaggerNativeRealEdgewiseStandardSimplexNerve

theorem toChain_natural {n : ℕ} {k m : SimplexCategory} (a : k ⟶ m)
    (f : epsilon.obj m ⟶ ⦋n⦌) :
    toChain.{u} (epsilon.map a ≫ f) =
      (SimplexCategory.toCat.map a).toFunctor ⋙ toChain f := by
  apply nerve.ext_of_isThin
  funext i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change f.toOrderHom ((epsilon.map a).toOrderHom ((inl' k k).toOrderHom i.rev)) =
      f.toOrderHom ((inl' m m).toOrderHom (a.toOrderHom i).rev)
    rw [epsilon_map_left, SimplexCategory.rev_map_apply, Fin.rev_rev]
    rfl
  · change f.toOrderHom ((epsilon.map a).toOrderHom ((inr' k k).toOrderHom i)) =
      f.toOrderHom ((inr' m m).toOrderHom (a.toOrderHom i))
    rw [epsilon_map_right]

def chainEquiv (n : ℕ) (m : SimplexCategory) :
    (epsilon.obj m ⟶ ⦋n⦌) ≃ (Fin (m.len + 1) ⥤ ULift.{u} (Interval n)) where
  toFun := toChain
  invFun := fromChain
  left_inv := fromChain_toChain.{u}
  right_inv := toChain_fromChain

def simplexIso (n : ℕ) : edgewise.obj (Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Interval n)) :=
  NatIso.ofComponents
    (fun m ↦ ((SSet.stdSimplex.objEquiv (n := ⦋n⦌) (m := epsilon.op.obj m)).trans
      (chainEquiv n m.unop)).toIso)
    (by
      intro m k a
      funext s
      exact toChain_natural a.unop (SSet.stdSimplex.objEquiv s))

end DaggerNativeRealEdgewiseStandardSimplexNerve
