import NativeRealEdgewiseTopologicalParameters
import NativeRealEdgewiseSSet
import Mathlib.AlgebraicTopology.SingularSet

/-! The actual geometric palindromic comparison, using the existing realization adjunction. -/
set_option autoImplicit false
open CategoryTheory Opposite
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
open DaggerNativeRealEdgewiseTopologicalParameters
universe u
namespace DaggerNativeRealEdgewiseRealizationComparison
noncomputable section

def singularComponent (T : TopCat.{u}) : edgewise.obj (TopCat.toSSet.obj T) ⟶
    TopCat.toSSet.obj T where
  app n α := ULift.up (parameterMap.{u}.app n.unop ≫ α.down)
  naturality {n m} f := by
    funext α
    apply ULift.ext
    change (parameterMap.{u}.app m.unop ≫
      SimplexCategory.toTop.{u}.map (epsilon.map f.unop)) ≫ α.down =
        (SimplexCategory.toTop.{u}.map f.unop ≫ parameterMap.{u}.app n.unop) ≫ α.down
    apply congrArg (fun k ↦ k ≫ α.down)
    exact (parameterMap.{u}.naturality f.unop).symm

def singularParameter : TopCat.toSSet.{u} ⋙ edgewise ⟶ TopCat.toSSet.{u} where
  app := singularComponent
  naturality T U f := by
    ext n α
    apply ULift.ext
    change (parameterMap.{u}.app n.unop ≫ α.down) ≫ f =
      parameterMap.{u}.app n.unop ≫ (α.down ≫ f)
    exact Category.assoc _ _ _

def transpose (X : SSet.{u}) : edgewise.obj X ⟶ TopCat.toSSet.obj (SSet.toTop.obj X) :=
  edgewise.map (sSetTopAdj.unit.app X) ≫ singularComponent (SSet.toTop.obj X)

theorem transpose_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewise.map f ≫ transpose Y = transpose X ≫ TopCat.toSSet.map (SSet.toTop.map f) := by
  unfold transpose
  calc
    _ = edgewise.map (f ≫ sSetTopAdj.unit.app Y) ≫
        singularComponent (SSet.toTop.obj Y) := by
      rw [Functor.map_comp, Category.assoc]
    _ = edgewise.map (sSetTopAdj.unit.app X ≫ TopCat.toSSet.map (SSet.toTop.map f)) ≫
        singularComponent (SSet.toTop.obj Y) := by
      exact congrArg (fun k ↦ edgewise.map k ≫ singularComponent (SSet.toTop.obj Y))
        (sSetTopAdj.unit.naturality f)
    _ = edgewise.map (sSetTopAdj.unit.app X) ≫
        (edgewise.map (TopCat.toSSet.map (SSet.toTop.map f)) ≫
          singularComponent (SSet.toTop.obj Y)) := by
      rw [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [show edgewise.map (TopCat.toSSet.map (SSet.toTop.map f)) ≫
          singularComponent (SSet.toTop.obj Y) =
          singularComponent (SSet.toTop.obj X) ≫ TopCat.toSSet.map (SSet.toTop.map f) from
        singularParameter.naturality (SSet.toTop.map f)]
      exact (Category.assoc _ _ _).symm

def comparison (X : SSet.{u}) : SSet.toTop.obj (edgewise.obj X) ⟶ SSet.toTop.obj X :=
  (sSetTopAdj.homEquiv (edgewise.obj X) (SSet.toTop.obj X)).symm (transpose X)

theorem comparison_mate (X : SSet.{u}) :
    sSetTopAdj.unit.app (edgewise.obj X) ≫ TopCat.toSSet.map (comparison X) =
      transpose X := by
  exact (sSetTopAdj.homEquiv (edgewise.obj X) (SSet.toTop.obj X)).apply_symm_apply _

theorem comparison_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (edgewise.map f) ≫ comparison Y = comparison X ≫ SSet.toTop.map f := by
  apply (sSetTopAdj.homEquiv (edgewise.obj X) (SSet.toTop.obj Y)).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  calc
    _ = edgewise.map f ≫
        (sSetTopAdj.unit.app (edgewise.obj Y) ≫ TopCat.toSSet.map (comparison Y)) := by
      have hn : edgewise.map f ≫ sSetTopAdj.unit.app (edgewise.obj Y) =
          sSetTopAdj.unit.app (edgewise.obj X) ≫
            TopCat.toSSet.map (SSet.toTop.map (edgewise.map f)) :=
        sSetTopAdj.unit.naturality (edgewise.map f)
      rw [← Category.assoc, ← hn]
      rfl
    _ = edgewise.map f ≫ transpose Y := by rw [comparison_mate]
    _ = transpose X ≫ TopCat.toSSet.map (SSet.toTop.map f) := transpose_natural f
    _ = _ := by rw [← comparison_mate, Category.assoc]

def naturalComparison : edgewise ⋙ SSet.toTop.{u} ⟶ SSet.toTop.{u} where
  app := comparison
  naturality _ _ f := comparison_natural f

end
end DaggerNativeRealEdgewiseRealizationComparison
