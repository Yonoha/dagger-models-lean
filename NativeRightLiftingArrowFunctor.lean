import NativeRightLiftingSurjection

/-! Naturality of the entire lifting-square map used in the original RLP accessibility route. -/

set_option autoImplicit false
open CategoryTheory Opposite
universe u v

namespace DaggerNativeRightLiftingArrowFunctor

open DaggerNativeRightLiftingSurjection
variable {C : Type u} [Category.{v} C]

/-- Postcomposition preserves the complete square produced by a diagonal. -/
theorem diagonalMap_target_naturality (a : Arrow C) {f g : Arrow C}
    (β : f ⟶ g) (l : a.right ⟶ f.left) :
    diagonalMap a f l ≫ β = diagonalMap a g (l ≫ β.left) := by
  apply Arrow.hom_ext
  · simp [diagonalMap, Category.assoc]
  · simp [diagonalMap, Category.assoc]

/-- Precomposition also retains the literal generating arrow. -/
theorem diagonalMap_source_naturality {a b : Arrow C} (α : a ⟶ b)
    (f : Arrow C) (l : b.right ⟶ f.left) :
    α ≫ diagonalMap b f l = diagonalMap a f (α.right ≫ l) := by
  apply Arrow.hom_ext
  · simp [diagonalMap, ← Category.assoc]
  · simp [diagonalMap, Category.assoc]

/-- The source is the full type of diagonals, not a chosen subset. -/
def liftSource (a : Arrow C) : Arrow C ⥤ Type v :=
  Arrow.leftFunc ⋙ coyoneda.obj (op a.right)

/-- The target is the full arrow-category hom, hence all commutative squares. -/
def squareTarget (a : Arrow C) : Arrow C ⥤ Type v := coyoneda.obj (op a)

/-- Diagonals give a natural transformation to all squares. -/
def diagonalNatural (a : Arrow C) : liftSource a ⟶ squareTarget a where
  app f := diagonalMap a f
  naturality f g β := by
    funext l
    exact (diagonalMap_target_naturality a β l).symm

/-- The natural-transformation component tests exactly the original lifting property. -/
theorem diagonalNatural_surjective_iff (a f : Arrow C) :
    Function.Surjective ((diagonalNatural a).app f) ↔ HasLiftingProperty a.hom f.hom :=
  diagonalMap_surjective_iff a f

end DaggerNativeRightLiftingArrowFunctor
