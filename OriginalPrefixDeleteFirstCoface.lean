import OriginalPrefixBoundarySuccessorShapes

/-!
# The exact first-prefix coface with its original ordinal casts

Use the native zero coface followed by the explicit equality of the original
successor dimensions. Its range is the actual first omitted-prefix face.
The comparison is made in the original ambient simplex in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes

universe u

namespace DaggerOriginalPrefixDeleteFirstCoface

/-- The actual original successor dimensions agree. -/
theorem successorDimension_eq (k n : ℕ) : k + n + 1 + 1 = k + 1 + n + 1 := by omega

/-- The native first coface, with its exact original target-dimension cast. -/
def prefixDeleteFirstOperator (k n : ℕ) : ⦋k + n + 1⦌ ⟶ ⦋k + 1 + n + 1⦌ :=
  SimplexCategory.δ 0 ≫ eqToHom (congrArg SimplexCategory.mk (successorDimension_eq k n))

/-- The actual operator shifts each original vertex by one. -/
theorem prefixDeleteFirstOperator_eval (k n : ℕ) (i : Fin (k + n + 2)) :
    ((prefixDeleteFirstOperator k n).toOrderHom i).val = i.val + 1 := by
  change ((eqToHom (congrArg SimplexCategory.mk (successorDimension_eq k n))).toOrderHom
    ((0 : Fin (k + n + 3)).succAbove i)).val = i.val + 1
  rw [SimplexCategory.eqToHom_toOrderHom]
  simp only [OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
    Fin.castOrderIso_apply]
  rw [Fin.succAbove_zero]
  rfl

/-- The actual simplicial first-prefix coface. -/
def prefixDeleteFirstMap (k n : ℕ) :
    (Δ[k + n + 1] : SSet.{u}) ⟶ (Δ[k + 1 + n + 1] : SSet.{u}) :=
  SSet.stdSimplex.map (prefixDeleteFirstOperator k n)

/-- Transport of the native zero face along the literal ambient-dimension equality. -/
theorem face_zero_image_eqToHom {a b : ℕ} (h : a = b) :
    (SSet.stdSimplex.face.{u} {(0 : Fin (a + 1))}ᶜ).image
      (SSet.stdSimplex.map (eqToHom (congrArg SimplexCategory.mk h))) =
    SSet.stdSimplex.face {(0 : Fin (b + 1))}ᶜ := by
  subst b
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, SSet.Subcomplex.image_id]

/-- The range is the exact actual first omitted-prefix face, with no ambient replacement. -/
theorem prefixDeleteFirstMap_range (k n : ℕ) :
    SSet.Subcomplex.range (prefixDeleteFirstMap.{u} k n) = firstPrefixFace k n := by
  have hr : SSet.Subcomplex.range
      (SSet.stdSimplex.{u}.map (SimplexCategory.δ (n := k + n + 1) 0)) =
    SSet.stdSimplex.face {(0 : Fin (k + n + 3))}ᶜ :=
    SSet.stdSimplex.range_δ.{u} (n := k + n + 1) 0
  dsimp only [prefixDeleteFirstMap, prefixDeleteFirstOperator]
  rw [CategoryTheory.Functor.map_comp, SSet.Subcomplex.range_comp, hr,
    face_zero_image_eqToHom]
  rw [firstPrefixFace, firstPrefixIndex_eq_zero]
  omega

end DaggerOriginalPrefixDeleteFirstCoface
