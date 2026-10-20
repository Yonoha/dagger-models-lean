import ChosenNecklaceCanonicalObjects

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T : NecklaceCode)

def forgetPath (a b : Vertices.{u} T) :
    JointPath a b ⥤ SimplicialThickening.Path a b where
  obj := JointPath.toPath
  map h := ⟨⟨⟨h.1.1.1⟩⟩⟩

/-- Retains every original vertex and subset; forgets only the joint proof. -/
def forgetNC : NC.{u} T ⟶ DaggerChosenRigidificationNecklace.T.obj ⦋T.len⦌ where
  obj a := ⟨a.as⟩
  map a b := nerveMap (forgetPath T a.as b.as)
  map_id a := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)
  map_comp a b c := by
    ext q x
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

theorem forgetNC_obj_injective : Function.Injective (forgetNC.{u} T).obj := by
  intro a b h
  apply congrArg NecklaceThickening.mk
  exact congrArg SimplicialThickening.as h

theorem forgetNC_map_injective (a b : (NC.{u} T).Obj) (q : SimplexCategoryᵒᵖ) :
    Function.Injective (((forgetNC T).map a b).app q) := by
  intro F G h
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    exact congrArg SimplicialThickening.Path.I (congrArg (fun K ↦ K.obj i) h)))

theorem forgetNC_transport {a b c d : (NC.{u} T).Obj} (ha : a = c) (hb : b = d) :
    targetHomTransport ha hb ≫ (forgetNC T).map c d =
      (forgetNC T).map a b ≫
        targetHomTransport (congrArg (forgetNC T).obj ha) (congrArg (forgetNC T).obj hb) := by
  cases ha
  cases hb
  rfl

/-- Full enriched cancellation, retaining the endpoint transports forced by whole equality. -/
theorem forgetNC_cancel {A : DaggerModels.SimplicialCat.{u,u}} (F G : A ⟶ NC.{u} T)
    (h : F ≫ forgetNC T = G ≫ forgetNC T) : F = G := by
  have ho : ∀ a, F.obj a = G.obj a := fun a ↦ forgetNC_obj_injective T
    (congrArg (fun K ↦ K.obj a) h)
  apply EnrichedFunctor.ext SSet ho
  intro a b
  have hm := enrichedFunctor_hom_congr h a b
    (congrArg (forgetNC T).obj (ho a)) (congrArg (forgetNC T).obj (ho b))
  apply NatTrans.ext
  funext q x
  apply forgetNC_map_injective T (G.obj a) (G.obj b) q
  have hh := congrFun (NatTrans.congr_app hm q) x
  have ht := congrFun (NatTrans.congr_app (forgetNC_transport T (ho a) (ho b)) q)
    (F.map a b |>.app q x)
  exact ht.trans hh

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
