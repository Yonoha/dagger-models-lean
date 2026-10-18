import OriginalOrdinalJoinAssociativity
import OriginalSimplexCoslice

/-!
# Exact original joined presheaves rebracket through the native associator

Whisker the opposite of the actual native ordinal-join associativity by X.
The resulting isomorphism retains every simplex and native associator cast.
Its exact diagram factors the original suffix projection as the two original
suffix projections, rather than replacing either projection by an equivalent map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalOrdinalJoinAssociativity
open DaggerOriginalSimplexCoslice

universe u

namespace DaggerOriginalJoinedPresheafAssociativity

/-- Rebracket the same original joined presheaf by the native associator. -/
def joinedAssociativityIso (a b : SimplexCategory) (X : SSet.{u}) :
    joinedPresheaf (AugmentedSimplexCategory.tensorObjOf a b) X ≅
      joinedPresheaf b (joinedPresheaf a X) :=
  (Functor.isoWhiskerRight (NatIso.op (ordinalJoinAssociativity a b)) X).symm

/-- The comparison simplex is given by the actual inverse native associator. -/
theorem joinedAssociativityIso_hom_app (a b : SimplexCategory) (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ)
    (s : (joinedPresheaf (AugmentedSimplexCategory.tensorObjOf a b) X).obj n) :
    (joinedAssociativityIso a b X).hom.app n s =
      X.map (ordinalJoinAssociator a b n.unop).inv.op s := rfl

/-- The exact original suffix projection factors through the native rebracketing isomorphism.
-/
theorem joinedAssociativityIso_comp_projections (a b : SimplexCategory) (X : SSet.{u}) :
    (joinedAssociativityIso a b X).hom ≫ suffixProjection b (joinedPresheaf a X) ≫
      suffixProjection a X = suffixProjection (AugmentedSimplexCategory.tensorObjOf a b) X := by
  ext n s
  change X.map (AugmentedSimplexCategory.inr' a n.unop).op
    (X.map ((ordinalJoinLeft a).map (AugmentedSimplexCategory.inr' b n.unop)).op
      (X.map (ordinalJoinAssociator a b n.unop).inv.op s)) =
    X.map (AugmentedSimplexCategory.inr'
      (AugmentedSimplexCategory.tensorObjOf a b) n.unop).op s
  have h := suffix_comp_ordinalJoinAssociator_inv a b n.unop
  rw [← suffix_comp (k := a) (AugmentedSimplexCategory.inr' b n.unop)] at h
  have hop : (ordinalJoinAssociator a b n.unop).inv.op ≫
      ((ordinalJoinLeft a).map (AugmentedSimplexCategory.inr' b n.unop)).op ≫
        (AugmentedSimplexCategory.inr' a n.unop).op =
    (AugmentedSimplexCategory.inr'
      (AugmentedSimplexCategory.tensorObjOf a b) n.unop).op :=
    congrArg (fun f ↦ f.op) h
  calc
    _ = X.map ((ordinalJoinAssociator a b n.unop).inv.op ≫
        ((ordinalJoinLeft a).map (AugmentedSimplexCategory.inr' b n.unop)).op ≫
          (AugmentedSimplexCategory.inr' a n.unop).op) s := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl
    _ = _ := congrFun (congrArg X.map hop) s

end DaggerOriginalJoinedPresheafAssociativity
