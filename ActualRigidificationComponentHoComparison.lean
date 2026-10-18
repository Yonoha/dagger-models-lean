import ActualPiZeroConstantAdjunction
import ActualOrdinaryCoreRigidificationLocalization

/-! The actual rigidification component category is naturally isomorphic to native ho. -/
set_option autoImplicit false
open CategoryTheory DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open DaggerActualPiZeroConstantAdjunction DaggerActualConstantEnrichmentFunctor
open DaggerOriginalAmbientDaggerPiZeroGroupoid
universe u
namespace DaggerActualRigidificationComponentHoComparison
noncomputable section

/-- Composite of the original rigidification adjunction and the exact component adjunction. -/
def componentAdjunction : rigidification.{u} ⋙ piZeroFunctor ⊣ nerveFunctor :=
  (rigidificationCoherentNerveAdjunction.comp piZeroConstantAdjunction).ofNatIsoRight
    constantCoherentNerveIso

/-- Uniqueness of left adjoints compares these same original functors. -/
def comparison : rigidification.{u} ⋙ piZeroFunctor ≅ SSet.hoFunctor :=
  componentAdjunction.leftAdjointUniq nerveAdjunction

def componentHoIso (X : SSet.{u}) :
    Cat.of (componentObjects (rigidification.obj X)) ≅ SSet.hoFunctor.obj X :=
  comparison.app X

def componentHoEquivalence (X : SSet.{u}) :
    componentObjects (rigidification.obj X) ≌ SSet.hoFunctor.obj X :=
  CategoryTheory.Equivalence.mk (componentHoIso X).hom.toFunctor
    (componentHoIso X).inv.toFunctor
    (eqToIso (congrArg (fun k : Cat.of (componentObjects (rigidification.obj X)) ⟶
      Cat.of (componentObjects (rigidification.obj X)) ↦ k.toFunctor)
        (componentHoIso X).hom_inv_id.symm))
    (eqToIso (congrArg (fun k : SSet.hoFunctor.obj X ⟶ SSet.hoFunctor.obj X ↦ k.toFunctor)
      (componentHoIso X).inv_hom_id))

theorem component_groupoid_of_ho_isIso (X : SSet.{u})
    (hX : ∀ {x y : SSet.hoFunctor.obj X} (f : x ⟶ y), IsIso f) :
    HasActualComponentGroupoid (rigidification.obj X) := by
  let F := (componentHoEquivalence X).functor
  have : F.Full := inferInstance
  have : F.Faithful := inferInstance
  refine ⟨Groupoid.ofIsIso (fun {x y} f ↦ ?_), rfl⟩
  have : IsIso (F.map f) := hX _
  exact isIso_of_reflects_iso f F

end
end DaggerActualRigidificationComponentHoComparison
