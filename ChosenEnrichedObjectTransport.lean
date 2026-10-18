import ChosenNecklaceEnrichedFunctor

open CategoryTheory EnrichedCategory MonoidalCategory

universe u o p

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {A : DaggerModels.SimplicialCat.{o,u}} {D : DaggerModels.SimplicialCat.{p,u}}
variable (F : EnrichedFunctor SSet.{u} A.Obj D.Obj)

def targetHomTransport {a b c d : D.Obj} (ha : a = c) (hb : b = d) :
    (a ⟶[SSet.{u}] b) ⟶ (c ⟶[SSet.{u}] d) := eqToHom (by rw [ha, hb])

theorem targetHomTransport_id (x : A.Obj) (a : D.Obj) (ha : F.obj x = a) :
    eId SSet x ≫ F.map x x ≫ targetHomTransport ha ha = eId SSet a := by
  cases ha
  rw [targetHomTransport, eqToHom_refl, Category.comp_id]
  exact F.map_id x

theorem targetHomTransport_comp (x y z : A.Obj) (a b c : D.Obj)
    (ha : F.obj x = a) (hb : F.obj y = b) (hc : F.obj z = c) :
    eComp SSet x y z ≫ F.map x z ≫ targetHomTransport ha hc =
      ((F.map x y ≫ targetHomTransport ha hb) ⊗ₘ
        (F.map y z ≫ targetHomTransport hb hc)) ≫ eComp SSet a b c := by
  cases ha
  cases hb
  cases hc
  simp only [targetHomTransport, eqToHom_refl, Category.comp_id]
  exact F.map_comp x y z

/-- Align only the supplied equal object labels, retaining both full Hom transports. -/
def transportObjects (d : A.Obj → D.Obj) (h : ∀ x, F.obj x = d x) : EnrichedFunctor SSet.{u} A.Obj D.Obj where
  obj := d
  map x y := F.map x y ≫ targetHomTransport (h x) (h y)
  map_id x := targetHomTransport_id F x (d x) (h x)
  map_comp x y z := targetHomTransport_comp F x y z (d x) (d y) (d z) (h x) (h y) (h z)

theorem transportObjects_obj (d : A.Obj → D.Obj) (h : ∀ x, F.obj x = d x) (x : A.Obj) :
    (transportObjects F d h).obj x = d x := rfl

theorem transportObjects_hom (d : A.Obj → D.Obj) (h : ∀ x, F.obj x = d x) (x y : A.Obj) :
    (transportObjects F d h).map x y = F.map x y ≫ targetHomTransport (h x) (h y) := rfl

theorem transportObjects_original : transportObjects F F.obj (fun _ ↦ rfl) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  simp only [transportObjects, targetHomTransport, eqToHom_refl, Category.comp_id]

end

end DaggerChosenRigidificationNecklace
