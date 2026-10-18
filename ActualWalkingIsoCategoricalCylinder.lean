import ActualWalkingIsoCategoricalEquivalence

/-!
# A categorical interval contraction of the entire original walking nerve

The parameter is the walking-isomorphism nerve itself. Every parameter arrow is
invertible. The two endpoints retain the original walking zero and one objects.
This supplies categorical interval data, without assuming or asserting a Joyal
or anti-involutive model structure.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualTaggedWalkingIsoSourceHomotopy
open DaggerOriginalNerveProduct
universe u
namespace DaggerActualWalkingIsoCategoricalCylinder
noncomputable section

/-- The original endpoint selected by the parameter bit. -/
def parameterObject (b : Bool) : walkingIso.{u} := ⟨⟨b⟩⟩

/-- The whole categorical interval acts by the constant zero or by the identity. -/
def contractionFunctor : (walkingIso.{u} × walkingIso.{u}) ⥤ walkingIso.{u} where
  obj p := if (ULift.down p.2).as then p.1 else walkingZero
  map _ := ⟨⟨⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Insert the selected original parameter endpoint, keeping the whole source object. -/
def endpointFunctor (b : Bool) : walkingIso.{u} ⥤ (walkingIso.{u} × walkingIso.{u}) :=
  (𝟭 walkingIso.{u}).prod' ((CategoryTheory.Functor.const walkingIso.{u}).obj
    (parameterObject b))

/-- The actual endpoint map of the product simplicial interval. -/
def endpoint (b : Bool) : J.{u} ⟶ J.{u} ⊗ J.{u} :=
  nerveMap (endpointFunctor b) ≫ (nerveProductIso walkingIso walkingIso).hom

/-- The full categorical contraction uses Mathlib's actual nerve/product comparison. -/
def cylinder : J.{u} ⊗ J.{u} ⟶ J.{u} :=
  (nerveProductIso walkingIso walkingIso).inv ≫ nerveMap contractionFunctor

/-- The initial categorical endpoint is literally the old collapse and zero inclusion. -/
theorem endpoint_zero_cylinder :
    endpoint.{u} false ≫ cylinder.{u} = collapse.{u} ≫ zeroInclusion.{u} := by
  simp only [endpoint, cylinder, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← nerve_constantWalking]
  apply NatTrans.ext
  funext n s
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The final categorical endpoint is the identity on the entire original walking nerve. -/
theorem endpoint_one_cylinder : endpoint.{u} true ≫ cylinder.{u} = 𝟙 J.{u} := by
  simp only [endpoint, cylinder, Category.assoc, Iso.hom_inv_id_assoc]
  apply NatTrans.ext
  funext n s
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The endpoint maps are precisely the product of the identity and selected constant map. -/
theorem endpoint_eq_lift (b : Bool) :
    endpoint.{u} b = lift (𝟙 J.{u}) (SSet.const (ComposableArrows.mk₀ (parameterObject b))) := by
  rw [endpoint, nerveProductIso_hom, comp_lift]
  congr 1

end
end DaggerActualWalkingIsoCategoricalCylinder
