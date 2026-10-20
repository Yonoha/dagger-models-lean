import NativeHoIsoWalkingExtension
import NativeIhomHoObjects
import NativeIhomQuasicategories

/-! Isomorphisms in native functor homotopy categories give whole original J-homotopies. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualFreeAntiWalkingCategoricalCylinder DaggerNativeIhomHoObjects
open DaggerNativeIhomQuasicategories DaggerNativeHoIsoWalkingExtension
universe u
namespace DaggerNativeHoIsoWholeWalkingHomotopy
noncomputable section

def parameterPoint (b : Bool) : (𝟙_ SSet.{u}) ⟶ J.{u} :=
  SSet.const (ComposableArrows.mk₀ (parameterObject b))

theorem endpoint_factor (A : SSet.{u}) (b : Bool) :
    intervalEndpoint A b = (ρ_ A).inv ≫ A ◁ parameterPoint.{u} b := by
  apply NatTrans.ext
  funext q a
  rfl

theorem point_comp_eq_curry {A Z : SSet.{u}} (f : A ⟶ Z)
    (H : J.{u} ⟶ (ihom A).obj Z) (b : Bool) (t : (Δ[0] : SSet.{u}) ⟶ J.{u})
    (ht : SSet.yonedaEquiv t = ComposableArrows.mk₀ (parameterObject b))
    (h : t ≫ H = SSet.yonedaEquiv.symm
      (SSet.hoFunctor.obj.equiv ((ihom A).obj Z) (homObject f))) :
    parameterPoint.{u} b ≫ H = MonoidalClosed.curry' f := by
  apply (SSet.unitHomEquiv _).injective
  have hv := congrArg SSet.yonedaEquiv h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, ht] at hv
  exact hv

theorem uncurry_endpoint {A Z : SSet.{u}} (f : A ⟶ Z)
    (H : J.{u} ⟶ (ihom A).obj Z) (b : Bool)
    (h : parameterPoint.{u} b ≫ H = MonoidalClosed.curry' f) :
    intervalEndpoint A b ≫ MonoidalClosed.uncurry H = f := by
  rw [endpoint_factor, Category.assoc, ← MonoidalClosed.uncurry_natural_left, h,
    MonoidalClosed.curry', MonoidalClosed.uncurry_curry, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

theorem exists_homotopy {A Z : SSet.{u}} [Z.Quasicategory] (f g : A ⟶ Z)
    (e : homObject f ≅ homObject g) :
    ∃ H : A ⊗ J.{u} ⟶ Z,
      intervalEndpoint A false ≫ H = f ∧ intervalEndpoint A true ≫ H = g := by
  have : ((ihom A).obj Z).Quasicategory := ihom_quasicategory A Z
  obtain ⟨H, h0, h1⟩ := ho_iso_endpoint_extension ((ihom A).obj Z)
    (homObject f) (homObject g) e
  refine ⟨MonoidalClosed.uncurry H, ?_, ?_⟩
  · exact uncurry_endpoint f H false
      (point_comp_eq_curry f H false zeroInclusion rfl h0)
  · exact uncurry_endpoint g H true
      (point_comp_eq_curry g H true oneInclusion rfl h1)

end
end DaggerNativeHoIsoWholeWalkingHomotopy
