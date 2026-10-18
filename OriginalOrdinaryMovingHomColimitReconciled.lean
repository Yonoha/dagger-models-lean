import OriginalOrdinaryMovingGraphColimitsReconciled
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Filtered colimits of original ordinary moving-endpoint Hom objects

The actual vertex and total-edge colimits recover each original Hom simplex
after correcting both endpoint labels at a later stage. Equality of Hom
simplices is likewise detected at a later original stage. These two facts
give the full simplicial-set colimit universal property.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryMovingHomColimits

noncomputable section

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {F : J ⥤ SimplicialCat.{u, u}} {c : Cocone F} (hc : IsColimit c)
variable (s t : ∀ j : J, (F.obj j).Obj)
variable (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
variable (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)
variable (x y : c.pt.Obj)
variable (hx : ∀ j, (c.ι.app j).obj (s j) = x)
variable (hy : ∀ j, (c.ι.app j).obj (t j) = y)

include hc hs ht

/-- Every original point Hom simplex has a representative with both chosen endpoints. -/
theorem hom_degree_surjective (q : SimplexCategoryᵒᵖ)
    (z : (c.pt.enriched.Hom x y).obj q) :
    ∃ j, ∃ w : ((F.obj j).enriched.Hom (s j) (t j)).obj q,
      z = (homLeg F s t c x y hx hy j).app q w := by
  obtain ⟨j, e, he⟩ := Types.jointly_surjective_of_isColimit
    (edgeIsColimit hc q) (embed c.pt x y q z)
  rcases e with ⟨a, b, e⟩
  have ha : (c.ι.app j).obj a = x := congrArg (fun e ↦ e.1) he
  have hb : (c.ι.app j).obj b = y := congrArg (fun e ↦ e.2.1) he
  obtain ⟨k, α, haα⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (vertexIsColimit hc) a (s j)).1 (ha.trans (hx j).symm)
  have ha' : (F.map α).obj a = s k := haα.trans (hs α)
  have hb' : (c.ι.app k).obj ((F.map α).obj b) = y := by
    exact (congrArg (fun T : F.obj j ⟶ c.pt ↦ T.obj b) (c.w α)).trans hb
  obtain ⟨l, β, hbβ⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (vertexIsColimit hc) ((F.map α).obj b) (t k)).1 (hb'.trans (hy k).symm)
  let e' : total (F.obj l) q := (edgeDiagram F q).map (α ≫ β) ⟨a, b, e⟩
  have hsl : e'.1 = s l := by
    change (F.map (α ≫ β)).obj a = s l
    rw [F.map_comp, SimplicialCat.comp_obj, ha']
    exact hs β
  have htl : e'.2.1 = t l := by
    change (F.map (α ≫ β)).obj b = t l
    rw [F.map_comp, SimplicialCat.comp_obj]
    exact hbβ.trans (ht β)
  let w := SimplicialGraph.TotalSpace.fiberEquiv
    (F.obj l).underlyingGraph (s l) (t l) q ⟨e', hsl, htl⟩
  have hw : embed (F.obj l) (s l) (t l) q w = e' := by
    exact congrArg Subtype.val ((SimplicialGraph.TotalSpace.fiberEquiv
      (F.obj l).underlyingGraph (s l) (t l) q).symm_apply_apply ⟨e', hsl, htl⟩)
  refine ⟨l, w, (embed_injective c.pt x y q) ?_⟩
  rw [embed_leg, hw]
  exact he.symm.trans (congrFun ((edgeCocone c q).w (α ≫ β)) ⟨a, b, e⟩).symm

/-- Equality of same-stage Hom simplices is detected after one original transition. -/
theorem hom_degree_eventual_eq (q : SimplexCategoryᵒᵖ) (j : J)
    (a b : ((F.obj j).enriched.Hom (s j) (t j)).obj q)
    (h : (homLeg F s t c x y hx hy j).app q a =
      (homLeg F s t c x y hx hy j).app q b) :
    ∃ k, ∃ α : j ⟶ k, (homMap F s t hs ht α).app q a =
      (homMap F s t hs ht α).app q b := by
  have he : (edgeCocone c q).ι.app j (embed (F.obj j) (s j) (t j) q a) =
      (edgeCocone c q).ι.app j (embed (F.obj j) (s j) (t j) q b) := by
    rw [← embed_leg F s t c x y hx hy, ← embed_leg F s t c x y hx hy, h]
  obtain ⟨k, α, hα⟩ := (Types.FilteredColimit.isColimit_eq_iff' (edgeIsColimit hc q)
    (embed (F.obj j) (s j) (t j) q a) (embed (F.obj j) (s j) (t j) q b)).1 he
  refine ⟨k, α, (embed_injective (F.obj k) (s k) (t k) q) ?_⟩
  rw [embed_map, embed_map]
  exact hα

/-- The original Hom cocone is a Type colimit in every simplicial degree. -/
def homDegreeIsColimit (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj q).mapCocone
      (homCocone F s t hs ht c x y hx hy)) :=
  Types.FilteredColimit.isColimitOf' _ _
    (hom_degree_surjective hc s t hs ht x y hx hy q)
    (hom_degree_eventual_eq hc s t hs ht x y hx hy q)

/-- The full original moving-Hom simplicial cocone is colimiting. -/
def homIsColimit : IsColimit (homCocone F s t hs ht c x y hx hy) :=
  evaluationJointlyReflectsColimits _ (homDegreeIsColimit hc s t hs ht x y hx hy)

/-- The universal map to an arbitrary target simplicial cocone. -/
def homDesc (d : Cocone (homDiagram F s t hs ht)) : c.pt.enriched.Hom x y ⟶ d.pt :=
  (homIsColimit hc s t hs ht x y hx hy).desc d

/-- Every original Hom leg factors through the universal map. -/
theorem homDesc_fac (d : Cocone (homDiagram F s t hs ht)) (j : J) :
    homLeg F s t c x y hx hy j ≫ homDesc hc s t hs ht x y hx hy d = d.ι.app j :=
  (homIsColimit hc s t hs ht x y hx hy).fac d j

/-- A map agreeing with all original Hom legs is the universal map. -/
theorem homDesc_uniq (d : Cocone (homDiagram F s t hs ht))
    (m : c.pt.enriched.Hom x y ⟶ d.pt)
    (hm : ∀ j, homLeg F s t c x y hx hy j ≫ m = d.ι.app j) :
    m = homDesc hc s t hs ht x y hx hy d :=
  (homIsColimit hc s t hs ht x y hx hy).uniq d m hm

end

end DaggerModels.OriginalOrdinaryMovingHomColimits
