import ActualTaggedWalkingCategoricalRetraction

/-!
# The native homotopy category of the original walking interval

Reuse the native nerve/ho comparison. Every two functors into this particular
homotopy category are naturally isomorphic, because the unchanged walking
category is codiscrete. No original simplicial set is assumed fibrant.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingCategoricalIntervalReversal
universe u
namespace DaggerNativeWalkingIntervalHomotopyCategory
noncomputable section

/-- Mathlib's exact nerve/ho isomorphism for the original interval. -/
def walkingIsoHoIso : SSet.hoFunctor.obj J.{u} ≅ Cat.of walkingIso.{u} :=
  nerveFunctorCompHoFunctorIso.app (Cat.of walkingIso)

/-- The actual native comparison functor, retaining the original walking objects. -/
def walkingIsoHoFunctor : SSet.hoFunctor.obj J.{u} ⥤ walkingIso.{u} :=
  walkingIsoHoIso.hom.toFunctor

/-- The strict native comparison gives an ordinary category equivalence with the same functor. -/
def walkingIsoHoEquivalence : SSet.hoFunctor.obj J.{u} ≌ walkingIso.{u} :=
  CategoryTheory.Equivalence.mk walkingIsoHoFunctor walkingIsoHoIso.inv.toFunctor
    (eqToIso (congrArg (fun k : SSet.hoFunctor.obj J ⟶ SSet.hoFunctor.obj J ↦ k.toFunctor)
      walkingIsoHoIso.hom_inv_id.symm))
    (eqToIso (congrArg (fun k : Cat.of walkingIso ⟶ Cat.of walkingIso ↦ k.toFunctor)
      walkingIsoHoIso.inv_hom_id))

instance walkingIsoHoFunctor_faithful : walkingIsoHoFunctor.{u}.Faithful :=
  show walkingIsoHoEquivalence.{u}.functor.Faithful by infer_instance

instance walkingIsoHoFunctor_full : walkingIsoHoFunctor.{u}.Full :=
  show walkingIsoHoEquivalence.{u}.functor.Full by infer_instance

/-- Native faithfulness reflects the unchanged unique walking arrows. -/
instance hoWalkingHomSubsingleton (x y : SSet.hoFunctor.obj J.{u}) :
    Subsingleton (x ⟶ y) :=
  ⟨fun f g ↦ walkingIsoHoFunctor.map_injective
    (Subsingleton.elim (walkingIsoHoFunctor.map f) (walkingIsoHoFunctor.map g))⟩

/-- Lift the original unique walking isomorphism to any pair of native ho objects. -/
def hoWalkingObjectIso (x y : SSet.hoFunctor.obj J.{u}) : x ≅ y :=
  walkingIsoHoFunctor.preimageIso
    { hom := ⟨⟨⟩⟩
      inv := ⟨⟨⟩⟩
      hom_inv_id := rfl
      inv_hom_id := rfl }

/-- Every two whole functors into the original interval's ho are naturally isomorphic. -/
def hoWalkingNatIso {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.hoFunctor.obj J.{u}) : F ≅ G :=
  NatIso.ofComponents (fun x ↦ hoWalkingObjectIso (F.obj x) (G.obj x))
    (fun _ ↦ Subsingleton.elim _ _)

end
end DaggerNativeWalkingIntervalHomotopyCategory
