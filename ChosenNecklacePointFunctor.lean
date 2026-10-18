import ChosenNecklaceSliceFac
import ChosenEnrichedTransportEquality

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode DaggerModels.SimplicialEnrichment

def pointObj : (NC.{u} point).Obj := ⟨ULift.up 0⟩

theorem pointObj_eq (a b : (NC.{u} point).Obj) : a = b := by
  change NecklaceThickening.mk a.as = NecklaceThickening.mk b.as
  apply congrArg NecklaceThickening.mk
  apply ULift.ext
  apply Fin.ext
  have ha := a.as.down.isLt
  have hb := b.as.down.isLt
  change a.as.down.val < 1 at ha
  change b.as.down.val < 1 at hb
  omega

/-- The literal identity-only point functor into an arbitrary supplied target object. -/
def pointNCFunctor (D : DaggerModels.SimplicialCat.{u,u}) (x : D.Obj) : NC.{u} point ⟶ D where
  obj _ := x
  map _ _ :=
    { app q _ := (eId SSet x).app q PUnit.unit
      naturality q r α := by
        funext z
        exact congrFun ((eId SSet x).naturality α) PUnit.unit }
  map_id a := by
    apply NatTrans.ext
    funext q v
    cases v
    rfl
  map_comp a b c := by
    apply NatTrans.ext
    funext q v
    rcases v with ⟨F,G⟩
    exact (Category.id_comp (𝟙 (show At D.Obj q from x))).symm

/-- Every full point functor is forced by its one actual object, in all degrees. -/
theorem pointNCFunctor_ext {D : DaggerModels.SimplicialCat.{u,u}}
    {F G : NC.{u} point ⟶ D} (h : F.obj pointObj = G.obj pointObj) : F = G := by
  have ho : ∀ a, F.obj a = G.obj a := by
    intro a
    rw [pointObj_eq a pointObj]
    exact h
  apply EnrichedFunctor.ext SSet ho
  intro a b
  have hab : b = a := pointObj_eq b a
  subst b
  apply NatTrans.ext
  funext q z
  rw [chainDiagonal q a.as z]
  exact (congrFun (NatTrans.congr_app
    (targetHomTransport_id F a (G.obj a) (ho a)) q) PUnit.unit).trans
      (congrFun (NatTrans.congr_app (G.map_id a) q) PUnit.unit).symm

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
