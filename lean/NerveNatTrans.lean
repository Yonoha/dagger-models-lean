import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Functor.Currying

set_option autoImplicit false

open CategoryTheory CategoryTheory.Category MonoidalCategory Simplicial Opposite

universe u v

namespace DaggerNerveHomotopy

variable {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}

/-- The actual nerve homotopy map induced by a supplied natural transformation. -/
def natTransMap (α : F ⟶ G) : nerve C ⊗ SSet.stdSimplex.obj ⦋1⦌ ⟶ nerve D where
  app _ p :=
    ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor.prod' p.1) ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ α)
  naturality _ _ _ := rfl

/-- The zero endpoint is exactly the nerve of the original source functor. -/
theorem natTransMap_zero (α : F ⟶ G) : SSet.ι₀ ≫ natTransMap α = nerveMap F := by
  ext n x
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  · intro i j f
    change (𝟙 _) ≫ F.map (x.map f) = (𝟙 _) ≫ F.map (x.map f) ≫ (𝟙 _)
    simp

/-- The one endpoint is exactly the nerve of the original target functor. -/
theorem natTransMap_one (α : F ⟶ G) : SSet.ι₁ ≫ natTransMap α = nerveMap G := by
  ext n x
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    rfl
  · intro i j f
    change (𝟙 _) ≫ G.map (x.map f) = (𝟙 _) ≫ G.map (x.map f) ≫ (𝟙 _)
    simp

end DaggerNerveHomotopy
