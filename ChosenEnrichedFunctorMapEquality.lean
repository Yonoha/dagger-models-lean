import ChosenEnrichedTransportEquality

open CategoryTheory EnrichedCategory

universe u o p

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {A : DaggerModels.SimplicialCat.{o,u}} {D : DaggerModels.SimplicialCat.{p,u}}

/-- Whole functor equality gives the same full Hom equality with both specified endpoint casts. -/
theorem enrichedFunctor_hom_congr {F G : EnrichedFunctor SSet.{u} A.Obj D.Obj}
    (h : F = G) (x y : A.Obj) (hx : F.obj x = G.obj x) (hy : F.obj y = G.obj y) :
    F.map x y ≫ targetHomTransport hx hy = G.map x y := by
  cases h
  simp only [targetHomTransport, eqToHom_refl, Category.comp_id]

end

end DaggerChosenRigidificationNecklace
