import OriginalOrdinaryEndpointTransportReconciled

/-!
# Moving-endpoint Hom diagrams for original ordinary simplicial categories

Both endpoint equalities transport the original enriched maps. The diagram and
cocone use actual functor and cocone legs, with arbitrary source objects and
arbitrary target endpoints.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryMovingHomColimits

noncomputable section

/-- An original enriched map followed by both target endpoint transports. -/
def castMap {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (a b : C.Obj) (x y : D.Obj) (hx : f.obj a = x) (hy : f.obj b = y) :
    C.enriched.Hom a b ⟶ D.enriched.Hom x y :=
  f.map a b ≫ OriginalOrdinaryEndpointTransport.transport D hx hy

/-- Equality of the original full functors preserves the casted Hom map. -/
theorem castMap_congr {C D : SimplicialCat.{u, u}} {f g : C ⟶ D} (h : f = g)
    (a b : C.Obj) (x y : D.Obj) (hx : f.obj a = x) (hy : f.obj b = y)
    (hx' : g.obj a = x) (hy' : g.obj b = y) :
    castMap f a b x y hx hy = castMap g a b x y hx' hy' := by
  cases h
  rfl

/-- Composition retains both intermediate and final endpoint transports. -/
theorem castMap_comp {C D E : SimplicialCat.{u, u}} (f : C ⟶ D) (g : D ⟶ E)
    (a b : C.Obj) (a' b' : D.Obj) (x y : E.Obj)
    (ha : f.obj a = a') (hb : f.obj b = b') (hx : g.obj a' = x) (hy : g.obj b' = y) :
    castMap (f ≫ g) a b x y ((congrArg g.obj ha).trans hx)
      ((congrArg g.obj hb).trans hy) =
      castMap f a b a' b' ha hb ≫ castMap g a' b' x y hx hy := by
  cases ha
  cases hb
  simp [castMap, SimplicialCat.comp_map, Category.assoc]

variable {J : Type u} [SmallCategory J]
variable (F : J ⥤ SimplicialCat.{u, u})
variable (s t : ∀ j : J, (F.obj j).Obj)
variable (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
variable (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)

/-- The original Hom transition, with both new endpoints identified. -/
def homMap {j k : J} (α : j ⟶ k) :
    (F.obj j).enriched.Hom (s j) (t j) ⟶ (F.obj k).enriched.Hom (s k) (t k) :=
  castMap (F.map α) (s j) (t j) (s k) (t k) (hs α) (ht α)

/-- The full moving-endpoint simplicial-set diagram. -/
def homDiagram : J ⥤ SSet.{u} where
  obj j := (F.obj j).enriched.Hom (s j) (t j)
  map α := homMap F s t hs ht α
  map_id j := by
    change castMap (F.map (𝟙 j)) (s j) (t j) (s j) (t j) (hs _) (ht _) = _
    rw [castMap_congr (F.map_id j) (s j) (t j) (s j) (t j) (hs _) (ht _) rfl rfl]
    simp [castMap]
  map_comp {j k l} α β := by
    exact (castMap_congr (F.map_comp α β) (s j) (t j) (s l) (t l) (hs _) (ht _)
      ((congrArg (F.map β).obj (hs α)).trans (hs β))
      ((congrArg (F.map β).obj (ht α)).trans (ht β))).trans
        (castMap_comp (F.map α) (F.map β) (s j) (t j) (s k) (t k) (s l) (t l)
          (hs α) (ht α) (hs β) (ht β))

variable (c : Cocone F) (x y : c.pt.Obj)
variable (hx : ∀ j, (c.ι.app j).obj (s j) = x)
variable (hy : ∀ j, (c.ι.app j).obj (t j) = y)

/-- The actual original enriched cocone leg with both endpoint casts. -/
def homLeg (j : J) : (F.obj j).enriched.Hom (s j) (t j) ⟶ c.pt.enriched.Hom x y :=
  castMap (c.ι.app j) (s j) (t j) x y (hx j) (hy j)

/-- The full simplicial Hom cocone, retaining every original leg. -/
def homCocone : Cocone (homDiagram F s t hs ht) where
  pt := c.pt.enriched.Hom x y
  ι :=
    { app := homLeg F s t c x y hx hy
      naturality := by
        intro j k α
        change castMap (F.map α) (s j) (t j) (s k) (t k) (hs α) (ht α) ≫
            castMap (c.ι.app k) (s k) (t k) x y (hx k) (hy k) =
          castMap (c.ι.app j) (s j) (t j) x y (hx j) (hy j) ≫ 𝟙 _
        rw [← castMap_comp (F.map α) (c.ι.app k) (s j) (t j) (s k) (t k) x y
          (hs α) (ht α) (hx k) (hy k), Category.comp_id]
        exact castMap_congr (c.w α) (s j) (t j) x y _ _ (hx j) (hy j) }

end

end DaggerModels.OriginalOrdinaryMovingHomColimits
