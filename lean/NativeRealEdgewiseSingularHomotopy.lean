import NativeRealEdgewiseInterpolationParameters
import NativeRealEdgewiseRealizationComparison
import NativeRealEdgewiseTargetWeak

/-! An actual raw simplicial homotopy from the palindromic singular map to the target projection. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
open DaggerNativeRealEdgewiseRealizationComparison
open DaggerNativeRealEdgewiseInterpolationParameters
universe u
namespace DaggerNativeRealEdgewiseSingularHomotopy
noncomputable section

theorem iota_zero_operator {Z : SSet.{u}} (n : SimplexCategoryᵒᵖ) (z : Z.obj n) :
    SSet.stdSimplex.objEquiv ((SSet.ι₀.app n z).2) = constantOperator n.unop 0 := by
  ext i : 3
  rfl

theorem iota_one_operator {Z : SSet.{u}} (n : SimplexCategoryᵒᵖ) (z : Z.obj n) :
    SSet.stdSimplex.objEquiv ((SSet.ι₁.app n z).2) = constantOperator n.unop 1 := by
  ext i : 3
  rfl

def singularHomotopyMap (T : TopCat.{u}) :
    edgewise.obj (TopCat.toSSet.obj T) ⊗ Δ[1] ⟶ TopCat.toSSet.obj T where
  app n p := ULift.up (interpolationMap.{u} (SSet.stdSimplex.objEquiv p.2) ≫ p.1.down)
  naturality {n m} f := by
    funext p
    apply ULift.ext
    change (interpolationMap.{u} (f.unop ≫ SSet.stdSimplex.objEquiv p.2) ≫
      SimplexCategory.toTop.{u}.map (epsilon.map f.unop)) ≫ p.1.down =
        (SimplexCategory.toTop.{u}.map f.unop ≫
          interpolationMap.{u} (SSet.stdSimplex.objEquiv p.2)) ≫ p.1.down
    apply congrArg (fun k ↦ k ≫ p.1.down)
    exact (interpolationMap_natural f.unop (SSet.stdSimplex.objEquiv p.2)).symm

theorem singularHomotopyMap_zero (T : TopCat.{u}) :
    SSet.ι₀ ≫ singularHomotopyMap T = singularComponent T := by
  ext n z
  apply ULift.ext
  change interpolationMap.{u} (SSet.stdSimplex.objEquiv ((SSet.ι₀.app n z).2)) ≫ z.down = _
  rw [iota_zero_operator, interpolationMap_zero]
  rfl

theorem singularHomotopyMap_one (T : TopCat.{u}) :
    SSet.ι₁ ≫ singularHomotopyMap T = targetProjection (TopCat.toSSet.obj T) := by
  ext n z
  apply ULift.ext
  change interpolationMap.{u} (SSet.stdSimplex.objEquiv ((SSet.ι₁.app n z).2)) ≫ z.down = _
  rw [iota_one_operator, interpolationMap_one]
  rfl

def singularHomotopy (T : TopCat.{u}) :
    SSet.Homotopy (singularComponent T) (targetProjection (TopCat.toSSet.obj T)) :=
  SSet.Homotopy.mk (singularHomotopyMap T)
    (singularHomotopyMap_zero T) (singularHomotopyMap_one T)

def transposeHomotopy (X : SSet.{u}) :
    SSet.Homotopy (transpose X) (targetProjection X ≫ sSetTopAdj.unit.app X) :=
  ((singularHomotopy (SSet.toTop.obj X)).precomp
    (edgewise.map (sSetTopAdj.unit.app X))).congr rfl
      (targetProjection_natural (sSetTopAdj.unit.app X))

end
end DaggerNativeRealEdgewiseSingularHomotopy
