import RigidificationCofBase

open CategoryTheory MonoidalCategory

universe u

namespace DaggerOrdinaryRigidificationCof

noncomputable section

/-- Transport only the object names of the SAME full enriched functor. -/
def reobject {E A : SC.{u}} (F : E ⟶ A) (g : E.Obj → A.Obj)
    (h : ∀ x, F.obj x = g x) : E ⟶ A where
  obj := g
  map x y := F.map x y ≫ eqToHom (by rw [h x, h y])
  map_id x := by
    have hg : F.obj = g := funext h
    cases hg
    simpa only [eqToHom_refl, Category.comp_id] using F.map_id x
  map_comp x y z := by
    have hg : F.obj = g := funext h
    cases hg
    simpa only [eqToHom_refl, Category.comp_id] using F.map_comp x y z

theorem reobject_obj {E A : SC.{u}} (F : E ⟶ A) (g : E.Obj → A.Obj)
    (h : ∀ x, F.obj x = g x) (x : E.Obj) : (reobject F g h).obj x = g x := rfl

theorem reobject_map {E A : SC.{u}} (F : E ⟶ A) (g : E.Obj → A.Obj)
    (h : ∀ x, F.obj x = g x) (x y : E.Obj) :
    (reobject F g h).map x y ≫ eqToHom (by rw [reobject_obj, reobject_obj]) =
      F.map x y ≫ eqToHom (by rw [h x, h y]) := by
  have hg : F.obj = g := funext h
  cases hg
  simp [reobject]

theorem reobject_comp {E D A : SC.{u}} (U : E ⟶ D) (F : D ⟶ A)
    (g : D.Obj → A.Obj) (h : ∀ x, F.obj x = g x) :
    U ≫ reobject F g h = reobject (U ≫ F) (g ∘ U.obj) (fun x => h (U.obj x)) := by
  have hg : F.obj = g := funext h
  cases hg
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro x y
  simp [reobject]

theorem reobject_self {E A : SC.{u}} (F : E ⟶ A) (g : E.Obj → A.Obj)
    (h : ∀ x, F.obj x = g x) : reobject F g h = F := by
  have hg : F.obj = g := funext h
  cases hg
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro x y
  simp [reobject]

theorem reobject_eq {E A : SC.{u}} {F G : E ⟶ A} (e : F = G)
    (g : E.Obj → A.Obj) (hF : ∀ x, F.obj x = g x) (hG : ∀ x, G.obj x = g x) :
    reobject F g hF = reobject G g hG := by
  cases e
  rfl

end

end DaggerOrdinaryRigidificationCof
