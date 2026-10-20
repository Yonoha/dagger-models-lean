import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-! The ORIGINAL edgewise index [n]^op * [n], reusing native Mathlib ordinal sum.
No independent ordered-sum category or tensor functor is introduced.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial
open AugmentedSimplexCategory
namespace DaggerNativeRealEdgewiseIndex

def epsilon : SimplexCategory ⥤ SimplexCategory where
  obj n := tensorObjOf n n
  map f := tensorHomOf (SimplexCategory.rev.map f) f
  map_id n := by
    have h := congrArg WithInitial.down (tensor_id (.of n) (.of n))
    change tensorHomOf (𝟙 n) (𝟙 n) = 𝟙 (tensorObjOf n n) at h
    have hrev : SimplexCategory.rev.map (𝟙 n) = 𝟙 n := SimplexCategory.rev.map_id n
    change tensorHomOf (SimplexCategory.rev.map (𝟙 n)) (𝟙 n) = 𝟙 _
    rw [hrev]
    exact h
  map_comp f g := by
    have h := congrArg WithInitial.down
      (AugmentedSimplexCategory.tensorHom_comp_tensorHom
        (inclusion.map (SimplexCategory.rev.map f)) (inclusion.map f)
        (inclusion.map (SimplexCategory.rev.map g)) (inclusion.map g))
    change tensorHomOf (SimplexCategory.rev.map f) f ≫
        tensorHomOf (SimplexCategory.rev.map g) g =
      tensorHomOf (SimplexCategory.rev.map f ≫ SimplexCategory.rev.map g) (f ≫ g) at h
    simpa only [Functor.map_comp] using h.symm

theorem epsilon_obj_len (n : SimplexCategory) : (epsilon.obj n).len = n.len + n.len + 1 := rfl

def targetInclusion : 𝟭 SimplexCategory ⟶ epsilon where
  app n := inr' n n
  naturality n m f := by
    have h := congrArg WithInitial.down
      (inr_comp_tensorHom (inclusion.map (SimplexCategory.rev.map f)) (inclusion.map f))
    change inr' n n ≫ tensorHomOf (SimplexCategory.rev.map f) f = f ≫ inr' m m at h
    exact h.symm

def sourceInclusion : SimplexCategory.rev ⟶ epsilon where
  app n := inl' n n
  naturality n m f := by
    have h := congrArg WithInitial.down
      (inl_comp_tensorHom (inclusion.map (SimplexCategory.rev.map f)) (inclusion.map f))
    change inl' n n ≫ tensorHomOf (SimplexCategory.rev.map f) f =
      SimplexCategory.rev.map f ≫ inl' m m at h
    exact h.symm

theorem epsilon_map_left {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (epsilon.map f).toOrderHom ((inl' n n).toOrderHom i) =
      (inl' m m).toOrderHom ((SimplexCategory.rev.map f).toOrderHom i) :=
  congrArg (fun g : n ⟶ epsilon.obj m ↦ g.toOrderHom i) (sourceInclusion.naturality f).symm

theorem epsilon_map_right {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (epsilon.map f).toOrderHom ((inr' n n).toOrderHom i) =
      (inr' m m).toOrderHom (f.toOrderHom i) :=
  congrArg (fun g : n ⟶ epsilon.obj m ↦ g.toOrderHom i) (targetInclusion.naturality f).symm

end DaggerNativeRealEdgewiseIndex
