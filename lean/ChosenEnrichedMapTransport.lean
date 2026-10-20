import ChosenEnrichedFunctorMapEquality

open CategoryTheory EnrichedCategory

universe u o p

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {A : DaggerModels.SimplicialCat.{o,u}} {D : DaggerModels.SimplicialCat.{p,u}}

theorem enriched_map_endpoint_transport (F : EnrichedFunctor SSet.{u} A.Obj D.Obj)
    {a b c d : A.Obj} (ha : a = c) (hb : b = d) :
    targetHomTransport ha hb ≫ F.map c d =
      F.map a b ≫ targetHomTransport (congrArg F.obj ha) (congrArg F.obj hb) := by
  cases ha
  cases hb
  simp only [targetHomTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

theorem targetHomTransport_trans {a b c d e f : D.Obj}
    (ha : a = c) (hb : b = d) (hc : c = e) (hd : d = f) :
    targetHomTransport ha hb ≫ targetHomTransport hc hd =
      targetHomTransport (ha.trans hc) (hb.trans hd) := by
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

theorem enrichedFunctor_hom_congr_to_fixed
    {F G : EnrichedFunctor SSet.{u} A.Obj D.Obj} (h : F = G)
    (x y : A.Obj) (a b : D.Obj)
    (hFx : F.obj x = a) (hFy : F.obj y = b)
    (hGx : G.obj x = a) (hGy : G.obj y = b) :
    F.map x y ≫ targetHomTransport hFx hFy =
      G.map x y ≫ targetHomTransport hGx hGy := by
  cases h
  rfl

end

end DaggerChosenRigidificationNecklace
