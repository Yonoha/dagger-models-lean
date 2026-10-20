import NativeRealEdgewiseGeometricWeak
import OriginalDaggerRealizationContinuousAction

/-! Lift the SAME original C2 comparison to the existing category of continuous actions. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerNativeRealEdgewiseRealizationC2Comparison
universe u
namespace DaggerNativeRealEdgewiseContinuousComparison
noncomputable section

theorem realizedEdgewiseAction_isContinuous (X : DaggerSSet.{u}) :
    (realizedEdgewiseFunctor.obj X).IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact ((realizedEdgewiseFunctor.obj X).ρ g).asHom.hom.continuous

def realizedEdgewiseContinuousFunctor : DaggerSSet.{u} ⥤ ContAction TopCat.{u} C2.{u} :=
  ObjectProperty.lift _ realizedEdgewiseFunctor realizedEdgewiseAction_isContinuous

def continuousComparison (X : DaggerSSet.{u}) :
    realizedEdgewiseContinuousFunctor.obj X ⟶ realizedContinuousActionFunctor.obj X :=
  ⟨comparisonActionMap X⟩

theorem continuousComparison_hom (X : DaggerSSet.{u}) :
    (continuousComparison X).hom = comparisonActionMap X := rfl

def naturalContinuousComparison :
    realizedEdgewiseContinuousFunctor ⟶ realizedContinuousActionFunctor where
  app := continuousComparison
  naturality X Y f := by
    ext : 1
    exact naturalActionComparison.naturality f

end
end DaggerNativeRealEdgewiseContinuousComparison
