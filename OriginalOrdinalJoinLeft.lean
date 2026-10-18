import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import OriginalOrdinaryCoreHomotopyComparison

/-!
# Ordinal join on the left, reusing the native augmented simplex tensor

The object [k] joined to [n] is the native ordinal sum [k+n+1]. All maps,
composition laws and the two block inclusions use the pinned Mathlib tensor.
This is the indexing construction for the actual standard-simplex coslice
route to the general special outer-horn theorem. No Kan assertion is made.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory Simplicial

namespace DaggerOriginalOrdinalJoinLeft

/-- Join a fixed original ordinal on the left, using the native ordinal-sum maps. -/
def ordinalJoinLeft (k : SimplexCategory) : SimplexCategory ⥤ SimplexCategory where
  obj n := AugmentedSimplexCategory.tensorObjOf k n
  map f := AugmentedSimplexCategory.tensorHomOf (𝟙 k) f
  map_id n := by
    exact AugmentedSimplexCategory.tensor_id (.of k) (.of n)
  map_comp {a b c} f g := by
    have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (𝟙 (CategoryTheory.WithInitial.of k))
      (show CategoryTheory.WithInitial.of a ⟶ CategoryTheory.WithInitial.of b from f)
      (𝟙 (CategoryTheory.WithInitial.of k))
      (show CategoryTheory.WithInitial.of b ⟶ CategoryTheory.WithInitial.of c from g)
    change AugmentedSimplexCategory.tensorHomOf (𝟙 k) f ≫
      AugmentedSimplexCategory.tensorHomOf (𝟙 k) g =
      AugmentedSimplexCategory.tensorHomOf (𝟙 k ≫ 𝟙 k) (f ≫ g) at h
    simpa only [Category.id_comp] using h.symm

/-- The original left block is fixed by every native ordinal-join map. -/
theorem prefix_comp {k a b : SimplexCategory} (f : a ⟶ b) :
    AugmentedSimplexCategory.inl' k a ≫ (ordinalJoinLeft k).map f =
      AugmentedSimplexCategory.inl' k b := by
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (𝟙 (CategoryTheory.WithInitial.of k))
    (show CategoryTheory.WithInitial.of a ⟶ CategoryTheory.WithInitial.of b from f)
  change AugmentedSimplexCategory.inl' k a ≫ (ordinalJoinLeft k).map f =
    𝟙 k ≫ AugmentedSimplexCategory.inl' k b at h
  simpa only [Category.id_comp] using h

/-- The original right block follows the given simplex operator under the native join. -/
theorem suffix_comp {k a b : SimplexCategory} (f : a ⟶ b) :
    AugmentedSimplexCategory.inr' k a ≫ (ordinalJoinLeft k).map f =
      f ≫ AugmentedSimplexCategory.inr' k b := by
  exact AugmentedSimplexCategory.inr_comp_tensorHom
    (𝟙 (CategoryTheory.WithInitial.of k))
    (show CategoryTheory.WithInitial.of a ⟶ CategoryTheory.WithInitial.of b from f)

/-- The left block inclusion as an actual natural transformation. -/
def prefixInclusion (k : SimplexCategory) :
    (Functor.const SimplexCategory).obj k ⟶ ordinalJoinLeft k where
  app n := AugmentedSimplexCategory.inl' k n
  naturality a b f := by
    change 𝟙 k ≫ AugmentedSimplexCategory.inl' k b =
      AugmentedSimplexCategory.inl' k a ≫ (ordinalJoinLeft k).map f
    rw [Category.id_comp]
    exact (prefix_comp f).symm

/-- The right block inclusion as an actual natural transformation. -/
def suffixInclusion (k : SimplexCategory) : 𝟭 SimplexCategory ⟶ ordinalJoinLeft k where
  app n := AugmentedSimplexCategory.inr' k n
  naturality _ _ f := (suffix_comp (k := k) f).symm

end DaggerOriginalOrdinalJoinLeft
