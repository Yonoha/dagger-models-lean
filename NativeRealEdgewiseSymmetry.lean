import NativeRealEdgewiseIndex

/-! Exact reversal symmetry of the ORIGINAL [n]^op * [n] index functor.
Use native Mathlib ordered-sum injections and its tensor-Hom extensionality.
-/
set_option autoImplicit false
open CategoryTheory Simplicial AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex
namespace DaggerNativeRealEdgewiseSymmetry

theorem rev_inl (n : SimplexCategory) (i : Fin (n.len + 1)) :
    ((inl' n n).toOrderHom i).rev = (inr' n n).toOrderHom i.rev := by
  rw [inl'_eval, inr'_eval]
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    tensorObjOf, SimplexCategory.len_mk]
  omega

theorem rev_inr (n : SimplexCategory) (i : Fin (n.len + 1)) :
    ((inr' n n).toOrderHom i).rev = (inl' n n).toOrderHom i.rev := by
  rw [inr'_eval, inl'_eval]
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    tensorObjOf, SimplexCategory.len_mk]
  omega

theorem hom_ext {n m : SimplexCategory} (f g : epsilon.obj n ⟶ m)
    (hl : inl' n n ≫ f = inl' n n ≫ g) (hr : inr' n n ≫ f = inr' n n ≫ g) : f = g := by
  apply inclusion.map_injective
  apply AugmentedSimplexCategory.tensorObj_hom_ext (x := .of n) (y := .of n) (z := .of m)
  · change inclusion.map (inl' n n ≫ f) = inclusion.map (inl' n n ≫ g)
    exact congrArg inclusion.map hl
  · change inclusion.map (inr' n n ≫ f) = inclusion.map (inr' n n ≫ g)
    exact congrArg inclusion.map hr

theorem epsilon_rev {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.rev.map (epsilon.map f) = epsilon.map f := by
  apply hom_ext
  · ext i : 3
    change (SimplexCategory.rev.map (epsilon.map f)).toOrderHom
      ((inl' n n).toOrderHom i) = (epsilon.map f).toOrderHom ((inl' n n).toOrderHom i)
    rw [SimplexCategory.rev_map_apply, rev_inl]
    exact (congrArg Fin.rev (epsilon_map_right f i.rev)).trans
      ((rev_inr m (f.toOrderHom i.rev)).trans (epsilon_map_left f i).symm)
  · ext i : 3
    change (SimplexCategory.rev.map (epsilon.map f)).toOrderHom
      ((inr' n n).toOrderHom i) = (epsilon.map f).toOrderHom ((inr' n n).toOrderHom i)
    rw [SimplexCategory.rev_map_apply, rev_inr]
    have h1 := congrArg Fin.rev (epsilon_map_left f i.rev)
    have h2 := rev_inl m ((SimplexCategory.rev.map f).toOrderHom i.rev)
    have h3 : ((SimplexCategory.rev.map f).toOrderHom i.rev).rev = f.toOrderHom i := by
      simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]
      rfl
    exact h1.trans (h2.trans ((congrArg (inr' m m).toOrderHom h3).trans
      (epsilon_map_right f i).symm))

end DaggerNativeRealEdgewiseSymmetry
