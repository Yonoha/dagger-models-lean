import ActualRigidificationComponentHoComparison
import OriginalSimplicialPiZeroFunctor

/-! Local weakness of the SAME rigidification gives full faithfulness of the SAME native ho map.
The existing NATURAL component/ho isomorphism is used; no new homotopy category is introduced.
-/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open DaggerActualRigidificationComponentHoComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRigHomWeakHoFullyFaithful
noncomputable section

theorem ho_map_conjugacy {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.hoFunctor.map f = (componentHoIso X).inv ≫
      piZeroFunctor.map (rigidification.map f) ≫ (componentHoIso Y).hom := by
  have hs : piZeroFunctor.map (rigidification.map f) ≫ (componentHoIso Y).hom =
      (componentHoIso X).hom ≫ SSet.hoFunctor.map f := comparison.hom.naturality f
  calc
    _ = (componentHoIso X).inv ≫ (componentHoIso X).hom ≫ SSet.hoFunctor.map f := by
      rw [Iso.inv_hom_id_assoc]
    _ = _ := by rw [← hs]

theorem ho_map_fully_faithful {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) :
    (SSet.hoFunctor.map f).toFunctor.Full ∧ (SSet.hoFunctor.map f).toFunctor.Faithful := by
  let F := componentFunctor (rigidification.map f)
  let EX := componentHoEquivalence X
  let EY := componentHoEquivalence Y
  have hF := componentFunctorFullyFaithful (rigidification.map f) hf
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  have : EX.inverse.Full := inferInstance
  have : EX.inverse.Faithful := inferInstance
  have : EY.functor.Full := inferInstance
  have : EY.functor.Faithful := inferInstance
  rw [ho_map_conjugacy]
  change (EX.inverse ⋙ F ⋙ EY.functor).Full ∧ (EX.inverse ⋙ F ⋙ EY.functor).Faithful
  exact ⟨inferInstance, inferInstance⟩

end
end DaggerActualRigHomWeakHoFullyFaithful
