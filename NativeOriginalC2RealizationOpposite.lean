import OriginalRealizationOppositeComparison
import NativeOriginalC2RealizationMapping

/-! Keep the OUTER simplicial opposite using the OLD natural realization ISO, equivariantly. -/
set_option autoImplicit false
open CategoryTheory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalRealizationOppositeComparison DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalC2RealizationOpposite
noncomputable section

def oppositeFunctor : Action SSet.{u} C2.{u} ⥤ Action SSet.{u} C2.{u} :=
  SSet.opFunctor.mapAction C2.{u}

def actionIso (A : Action SSet.{u} C2.{u}) :
    (SSet.toTop.mapAction C2.{u}).obj (oppositeFunctor.obj A) ≅
      (SSet.toTop.mapAction C2.{u}).obj A :=
  Action.mkIso (realizationOppositeIso.app A.V)
    (fun g ↦ realizationOppositeIso.hom.naturality (A.ρ g).asHom)

def continuousIso (A : Action SSet.{u} C2.{u}) :
    realizationFunctor.obj (oppositeFunctor.obj A) ≅ realizationFunctor.obj A where
  hom := ⟨(actionIso A).hom⟩
  inv := ⟨(actionIso A).inv⟩
  hom_inv_id := by
    ext : 1
    exact (actionIso A).hom_inv_id
  inv_hom_id := by
    ext : 1
    exact (actionIso A).inv_hom_id

theorem continuousIso_hom {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    realizationFunctor.map (oppositeFunctor.map f) ≫ (continuousIso B).hom =
      (continuousIso A).hom ≫ realizationFunctor.map f := by
  ext : 1
  apply Action.hom_ext
  exact realizationOppositeIso.hom.naturality f.hom

def mappingIso (A : Action SSet.{u} C2.{u}) :
    mappingFunctor.obj (oppositeFunctor.obj A) ≅ mappingFunctor.obj A :=
  mappingSingFunctor.mapIso (continuousIso A)

theorem mappingIso_weak (A : Action SSet.{u} C2.{u}) :
    HomotopicalAlgebra.WeakEquivalence (mappingIso A).hom := by infer_instance

theorem mappingIso_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    mappingFunctor.map (oppositeFunctor.map f) ≫ (mappingIso B).hom =
      (mappingIso A).hom ≫ mappingFunctor.map f := by
  have h := congrArg mappingSingFunctor.map (continuousIso_hom f)
  simpa only [CategoryTheory.Functor.map_comp] using h

end
end DaggerNativeOriginalC2RealizationOpposite
