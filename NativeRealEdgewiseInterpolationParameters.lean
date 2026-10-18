import NativeStdSimplexInterpolation
import NativeRealEdgewiseTopologicalParameters

/-! Natural barycentric interpolation from the SAME palindromic parameter to the right inclusion. -/
set_option autoImplicit false
open CategoryTheory Simplicial AugmentedSimplexCategory
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseParameters
open DaggerNativeStdSimplexInterpolation DaggerNativeRealEdgewiseTopologicalParameters
universe u
namespace DaggerNativeRealEdgewiseInterpolationParameters
noncomputable section

def constantOperator (n : SimplexCategory) (b : Fin 2) : n ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk { toFun := fun _ ↦ b, monotone' := fun _ _ _ ↦ le_rfl }

def timeCoordinate {n : SimplexCategory} (a : n ⟶ ⦋1⦌)
    (t : stdSimplex ℝ (Fin (n.len + 1))) : unitInterval :=
  stdSimplexHomeomorphUnitInterval (stdSimplex.map a.toOrderHom t)

theorem timeCoordinate_natural {n m : SimplexCategory} (f : n ⟶ m) (a : m ⟶ ⦋1⦌)
    (t : stdSimplex ℝ (Fin (n.len + 1))) :
    timeCoordinate (f ≫ a) t = timeCoordinate a (stdSimplex.map f.toOrderHom t) := by
  apply congrArg stdSimplexHomeomorphUnitInterval
  exact (stdSimplex.map_comp_apply f.toOrderHom a.toOrderHom t).symm

theorem timeCoordinate_zero (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    timeCoordinate (constantOperator n 0) t = 0 := by
  apply Subtype.ext
  change (FunOnFinite.linearMap ℝ ℝ (fun _ : Fin (n.len + 1) ↦ (0 : Fin 2)) t) 1 = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp

theorem timeCoordinate_one (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    timeCoordinate (constantOperator n 1) t = 1 := by
  apply Subtype.ext
  change (FunOnFinite.linearMap ℝ ℝ (fun _ : Fin (n.len + 1) ↦ (1 : Fin 2)) t) 1 = 1
  rw [FunOnFinite.linearMap_apply_apply]
  simp

theorem continuous_timeCoordinate {n : SimplexCategory} (a : n ⟶ ⦋1⦌) :
    Continuous (timeCoordinate a) :=
  stdSimplexHomeomorphUnitInterval.continuous_toFun.comp
    (stdSimplex.continuous_map a.toOrderHom)

def interpolate {n : SimplexCategory} (a : n ⟶ ⦋1⦌)
    (t : stdSimplex ℝ (Fin (n.len + 1))) : stdSimplex ℝ (Fin ((epsilon.obj n).len + 1)) :=
  blend (parameter n t) (rightPart n t) (timeCoordinate a t)

theorem interpolate_natural {n m : SimplexCategory} (f : n ⟶ m) (a : m ⟶ ⦋1⦌)
    (t : stdSimplex ℝ (Fin (n.len + 1))) :
    stdSimplex.map (epsilon.map f).toOrderHom (interpolate (f ≫ a) t) =
      interpolate a (stdSimplex.map f.toOrderHom t) := by
  unfold interpolate
  rw [map_blend, parameter_natural, rightPart_natural, timeCoordinate_natural]

theorem interpolate_zero (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    interpolate (constantOperator n 0) t = parameter n t := by
  unfold interpolate
  rw [timeCoordinate_zero, blend_zero]

theorem interpolate_one (n : SimplexCategory) (t : stdSimplex ℝ (Fin (n.len + 1))) :
    interpolate (constantOperator n 1) t = rightPart n t := by
  unfold interpolate
  rw [timeCoordinate_one, blend_one]

theorem continuous_interpolate {n : SimplexCategory} (a : n ⟶ ⦋1⦌) :
    Continuous (interpolate a) := by
  have hr : Continuous (rightPart n) := stdSimplex.continuous_map (inr' n n).toOrderHom
  have hp : Continuous (fun t ↦ (parameter n t, rightPart n t, timeCoordinate a t)) :=
    (continuous_parameter n).prodMk (hr.prodMk (continuous_timeCoordinate a))
  change Continuous (fun t ↦ blend (parameter n t) (rightPart n t) (timeCoordinate a t))
  exact Continuous.comp (f := fun t ↦ (parameter n t, rightPart n t, timeCoordinate a t))
    (g := fun p ↦ blend p.1 p.2.1 p.2.2) continuous_blend hp

def interpolationMap₀ {n : SimplexCategory} (a : n ⟶ ⦋1⦌) :
    SimplexCategory.toTop₀.obj n ⟶ SimplexCategory.toTop₀.obj (epsilon.obj n) :=
  TopCat.ofHom ⟨interpolate a, continuous_interpolate a⟩

def interpolationMap {n : SimplexCategory} (a : n ⟶ ⦋1⦌) :
    SimplexCategory.toTop.{u}.obj n ⟶ SimplexCategory.toTop.{u}.obj (epsilon.obj n) :=
  TopCat.uliftFunctor.map (interpolationMap₀ a)

theorem interpolationMap_natural {n m : SimplexCategory} (f : n ⟶ m) (a : m ⟶ ⦋1⦌) :
    SimplexCategory.toTop.{u}.map f ≫ interpolationMap a =
      interpolationMap (f ≫ a) ≫ SimplexCategory.toTop.{u}.map (epsilon.map f) := by
  ext t
  apply ULift.ext
  exact (interpolate_natural f a t.down).symm

theorem interpolationMap_zero (n : SimplexCategory) :
    interpolationMap.{u} (constantOperator n 0) = parameterMap.{u}.app n := by
  ext t
  apply ULift.ext
  exact interpolate_zero n t.down

theorem interpolationMap_one (n : SimplexCategory) :
    interpolationMap.{u} (constantOperator n 1) = SimplexCategory.toTop.{u}.map (inr' n n) := by
  ext t
  apply ULift.ext
  exact interpolate_one n t.down

end
end DaggerNativeRealEdgewiseInterpolationParameters
