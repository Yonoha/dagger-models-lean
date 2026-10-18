import NativeRealEdgewiseSymmetry
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-! The ORIGINAL edgewise precomposition and both actual simplicial projections. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSymmetry
universe u
namespace DaggerNativeRealEdgewiseSSet

def edgewise : SSet.{u} ⥤ SSet.{u} where
  obj X := epsilon.op ⋙ X
  map f := Functor.whiskerLeft epsilon.op f
  map_id _ := rfl
  map_comp _ _ := rfl

def targetProjection (X : SSet.{u}) : edgewise.obj X ⟶ X :=
  Functor.whiskerRight (NatTrans.op targetInclusion) X

def sourceProjection (X : SSet.{u}) : edgewise.obj X ⟶ X.op :=
  Functor.whiskerRight (NatTrans.op sourceInclusion) X

theorem targetProjection_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewise.map f ≫ targetProjection Y = targetProjection X ≫ f := by
  apply NatTrans.ext
  funext n
  exact (f.naturality (targetInclusion.app n.unop).op).symm

theorem sourceProjection_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewise.map f ≫ sourceProjection Y = sourceProjection X ≫ SSet.opFunctor.map f := by
  apply NatTrans.ext
  funext n
  exact (f.naturality (sourceInclusion.app n.unop).op).symm

theorem rev_left (n : SimplexCategory) :
    SimplexCategory.rev.map (inl' n n) = inr' n n := by
  ext i : 3
  rw [SimplexCategory.rev_map_apply]
  exact (rev_inl n i.rev).trans (congrArg (inr' n n).toOrderHom (Fin.rev_rev i))

theorem rev_right (n : SimplexCategory) :
    SimplexCategory.rev.map (inr' n n) = inl' n n := by
  ext i : 3
  rw [SimplexCategory.rev_map_apply]
  exact (rev_inr n i.rev).trans (congrArg (inl' n n).toOrderHom (Fin.rev_rev i))

end DaggerNativeRealEdgewiseSSet
