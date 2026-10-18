import OriginalOrdinalJoinLeft

/-!
# Native associativity of the exact original ordinal-join functors

Descend the pinned Mathlib augmented-simplex associator to the ordinary
simplex category. Its naturality and right-block inclusion law descend as
well. All comparison maps are the actual native associator maps, retaining
ordinal casts; no independently chosen equivalent simplex is substituted.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Simplicial
open DaggerOriginalOrdinalJoinLeft

namespace DaggerOriginalOrdinalJoinAssociativity

/-- The actual native associator on the three nonempty original ordinal blocks. -/
def ordinalJoinAssociator (a b n : SimplexCategory) :
    AugmentedSimplexCategory.tensorObjOf (AugmentedSimplexCategory.tensorObjOf a b) n ≅
      AugmentedSimplexCategory.tensorObjOf a (AugmentedSimplexCategory.tensorObjOf b n) where
  hom := WithInitial.down (α_ (WithInitial.of a) (WithInitial.of b) (WithInitial.of n)).hom
  inv := WithInitial.down (α_ (WithInitial.of a) (WithInitial.of b) (WithInitial.of n)).inv
  hom_inv_id := by
    have h := congrArg WithInitial.down
      (α_ (WithInitial.of a) (WithInitial.of b) (WithInitial.of n)).hom_inv_id
    simpa only [WithInitial.down_comp, WithInitial.down_id] using h
  inv_hom_id := by
    have h := congrArg WithInitial.down
      (α_ (WithInitial.of a) (WithInitial.of b) (WithInitial.of n)).inv_hom_id
    simpa only [WithInitial.down_comp, WithInitial.down_id] using h

/-- Naturality is exactly the native monoidal associator equation. -/
theorem ordinalJoinAssociator_naturality (a b : SimplexCategory)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (ordinalJoinLeft (AugmentedSimplexCategory.tensorObjOf a b)).map f ≫
      (ordinalJoinAssociator a b n).hom =
    (ordinalJoinAssociator a b m).hom ≫
      (ordinalJoinLeft a).map ((ordinalJoinLeft b).map f) := by
  have h := associator_naturality (𝟙 (WithInitial.of a)) (𝟙 (WithInitial.of b))
    (show WithInitial.of m ⟶ WithInitial.of n from f)
  rw [AugmentedSimplexCategory.tensor_id] at h
  exact congrArg WithInitial.down h

/-- The actual natural ordinal-join associativity isomorphism. -/
def ordinalJoinAssociativity (a b : SimplexCategory) :
    ordinalJoinLeft (AugmentedSimplexCategory.tensorObjOf a b) ≅
      ordinalJoinLeft b ⋙ ordinalJoinLeft a :=
  NatIso.ofComponents (ordinalJoinAssociator a b)
    (fun f ↦ ordinalJoinAssociator_naturality a b f)

/-- The original suffix inclusion commutes with the native associator, as an exact equality. -/
theorem suffix_comp_ordinalJoinAssociator (a b n : SimplexCategory) :
    AugmentedSimplexCategory.inr' (AugmentedSimplexCategory.tensorObjOf a b) n ≫
      (ordinalJoinAssociator a b n).hom =
    AugmentedSimplexCategory.inr' b n ≫
      AugmentedSimplexCategory.inr' a (AugmentedSimplexCategory.tensorObjOf b n) := by
  exact congrArg WithInitial.down
    (AugmentedSimplexCategory.inr_comp_associator
      (WithInitial.of a) (WithInitial.of b) (WithInitial.of n))

/-- The inverse native associator retains the same original suffix inclusion. -/
theorem suffix_comp_ordinalJoinAssociator_inv (a b n : SimplexCategory) :
    (AugmentedSimplexCategory.inr' b n ≫
      AugmentedSimplexCategory.inr' a (AugmentedSimplexCategory.tensorObjOf b n)) ≫
        (ordinalJoinAssociator a b n).inv =
    AugmentedSimplexCategory.inr' (AugmentedSimplexCategory.tensorObjOf a b) n := by
  rw [← suffix_comp_ordinalJoinAssociator, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end DaggerOriginalOrdinalJoinAssociativity
