import ChosenEnrichedObjectTransport

open CategoryTheory EnrichedCategory

universe u o p

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {A : DaggerModels.SimplicialCat.{o,u}} {D : DaggerModels.SimplicialCat.{p,u}}

theorem transportObjects_eq (F : EnrichedFunctor SSet.{u} A.Obj D.Obj)
    (d : A.Obj → D.Obj) (h : ∀ x, F.obj x = d x) : transportObjects F d h = F := by
  apply EnrichedFunctor.ext SSet (fun x ↦ (h x).symm)
  intro x y
  change (F.map x y ≫ targetHomTransport (h x) (h y)) ≫
    eqToHom (show (d x ⟶[SSet.{u}] d y) = (F.obj x ⟶[SSet.{u}] F.obj y)
      by rw [(h x).symm, (h y).symm]) = F.map x y
  simp only [Category.assoc, targetHomTransport, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

end

end DaggerChosenRigidificationNecklace
