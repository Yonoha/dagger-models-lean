import OriginalOrdinaryMovingHomDiagramReconciled
import OriginalOrdinaryFilteredEnrichedColimitComparison
import OriginalOrdinaryGraphEvaluationPreservation
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Original ordinary graph values of an arbitrary filtered enriched colimit

The original graph-forgetful functor, vertex evaluation, and total-edge
evaluation preserve the given filtered colimit. A Hom simplex embeds with
its two original endpoint labels; both endpoint transports retain that
literal total edge. No dagger graph or fixed object set is used.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerModels.OriginalOrdinaryMovingHomColimits

noncomputable section

variable {J : Type u} [SmallCategory J]

/-- Original object evaluation of an original enriched simplicial category. -/
abbrev vertexValue : SimplicialCat.{u, u} ⥤ Type u :=
  SimplicialCat.graphForget ⋙ OriginalOrdinaryGraphEvaluation.vertices

/-- Original total edges in simplex degree `q`, retaining both endpoints. -/
abbrev edgeValue (q : SimplexCategoryᵒᵖ) : SimplicialCat.{u, u} ⥤ Type u :=
  (SimplicialCat.graphForget ⋙ SimplicialGraph.TotalSpace.edgeFunctor) ⋙
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj q

abbrev vertexDiagram (F : J ⥤ SimplicialCat.{u, u}) : J ⥤ Type u :=
  F ⋙ vertexValue

abbrev vertexCocone {F : J ⥤ SimplicialCat.{u, u}} (c : Cocone F) :
    Cocone (vertexDiagram F) :=
  vertexValue.mapCocone c

abbrev edgeDiagram (F : J ⥤ SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ) :
    J ⥤ Type u :=
  F ⋙ edgeValue q

abbrev edgeCocone {F : J ⥤ SimplicialCat.{u, u}} (c : Cocone F)
    (q : SimplexCategoryᵒᵖ) : Cocone (edgeDiagram F q) :=
  (edgeValue q).mapCocone c

/-- The same original graph cocone is colimiting. -/
noncomputable def graphIsColimit [IsFiltered J]
    {F : J ⥤ SimplicialCat.{u, u}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (SimplicialCat.graphForget.mapCocone c) := by
  letI : PreservesColimit F SimplicialCat.graphForget :=
    OriginalOrdinaryFilteredEnrichedPoint.graphForget_preservesColimit F
  exact isColimitOfPreserves SimplicialCat.graphForget hc

/-- The original vertex cocone is colimiting for this arbitrary cocone. -/
noncomputable def vertexIsColimit [IsFiltered J]
    {F : J ⥤ SimplicialCat.{u, u}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (vertexCocone c) := by
  letI : PreservesColimit F SimplicialCat.graphForget :=
    OriginalOrdinaryFilteredEnrichedPoint.graphForget_preservesColimit F
  letI : PreservesColimit (F ⋙ SimplicialCat.graphForget)
      OriginalOrdinaryGraphEvaluation.vertices :=
    OriginalOrdinaryGraphEvaluation.vertices_preservesColimit _
  exact isColimitOfPreserves vertexValue hc

/-- Total original edges in each simplicial degree are colimiting. -/
noncomputable def edgeIsColimit [IsFiltered J]
    {F : J ⥤ SimplicialCat.{u, u}} {c : Cocone F} (hc : IsColimit c)
    (q : SimplexCategoryᵒᵖ) : IsColimit (edgeCocone c q) := by
  letI : PreservesColimit F SimplicialCat.graphForget :=
    OriginalOrdinaryFilteredEnrichedPoint.graphForget_preservesColimit F
  letI : PreservesColimit (F ⋙ SimplicialCat.graphForget)
      SimplicialGraph.TotalSpace.edgeFunctor :=
    OriginalOrdinaryGraphEvaluation.edgeFunctor_preservesColimit _
  letI : PreservesColimit
      ((F ⋙ SimplicialCat.graphForget) ⋙ SimplicialGraph.TotalSpace.edgeFunctor)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj q) := inferInstance
  exact isColimitOfPreserves (edgeValue q) hc

@[simp] theorem vertex_leg {F : J ⥤ SimplicialCat.{u, u}}
    (c : Cocone F) (j : J) (a : (F.obj j).Obj) :
    (vertexCocone c).ι.app j a = (c.ι.app j).obj a := rfl

/-- Each actual colimit object has an original stage representative. -/
theorem object_jointly_surjective [IsFiltered J]
    {F : J ⥤ SimplicialCat.{u, u}} {c : Cocone F}
    (hc : IsColimit c) (x : c.pt.Obj) :
    ∃ j, ∃ a : (F.obj j).Obj, (c.ι.app j).obj a = x :=
  Types.jointly_surjective_of_isColimit (vertexIsColimit hc) x

/-- The literal original total edge type in one simplex degree. -/
abbrev total (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ) : Type u :=
  (SimplicialGraph.TotalSpace.edges (SimplicialCat.graphForget.obj C)).obj q

/-- Insert one original Hom simplex with both original endpoint labels. -/
abbrev embed (C : SimplicialCat.{u, u}) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (z : (C.enriched.Hom a b).obj q) : total C q :=
  ⟨a, b, z⟩

/-- The endpoint-labeled embedding is injective on every original Hom. -/
theorem embed_injective (C : SimplicialCat.{u, u}) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) : Function.Injective (embed C a b q) := by
  exact Subtype.val_injective.comp
    (SimplicialGraph.TotalSpace.fiberEquiv
      (SimplicialCat.graphForget.obj C) a b q).symm.injective

/-- Both original endpoint transports retain the same total-edge simplex. -/
theorem embed_cast (C : SimplicialCat.{u, u}) {a a' b b' : C.Obj}
    (ha : a = a') (hb : b = b') (q : SimplexCategoryᵒᵖ)
    (z : (C.enriched.Hom a b).obj q) :
    embed C a' b' q ((OriginalOrdinaryEndpointTransport.transport C ha hb).app q z) =
      embed C a b q z := by
  cases ha
  cases hb
  rfl

/-- The moving original Hom transition has the same literal total-edge map. -/
theorem embed_map (F : J ⥤ SimplicialCat.{u, u})
    (s t : ∀ j, (F.obj j).Obj)
    (hs : ∀ {j k} (α : j ⟶ k), (F.map α).obj (s j) = s k)
    (ht : ∀ {j k} (α : j ⟶ k), (F.map α).obj (t j) = t k)
    {j k : J} (α : j ⟶ k) (q : SimplexCategoryᵒᵖ)
    (z : ((F.obj j).enriched.Hom (s j) (t j)).obj q) :
    embed (F.obj k) (s k) (t k) q ((homMap F s t hs ht α).app q z) =
      (edgeDiagram F q).map α (embed (F.obj j) (s j) (t j) q z) :=
  embed_cast (F.obj k) (hs α) (ht α) q
    (((F.map α).map (s j) (t j)).app q z)

/-- The original enriched cocone leg has the same literal total-edge leg. -/
theorem embed_leg (F : J ⥤ SimplicialCat.{u, u})
    (s t : ∀ j, (F.obj j).Obj) (c : Cocone F) (x y : c.pt.Obj)
    (hx : ∀ j, (c.ι.app j).obj (s j) = x)
    (hy : ∀ j, (c.ι.app j).obj (t j) = y) (j : J)
    (q : SimplexCategoryᵒᵖ)
    (z : ((F.obj j).enriched.Hom (s j) (t j)).obj q) :
    embed c.pt x y q ((homLeg F s t c x y hx hy j).app q z) =
      (edgeCocone c q).ι.app j (embed (F.obj j) (s j) (t j) q z) :=
  embed_cast c.pt (hx j) (hy j) q
    (((c.ι.app j).map (s j) (t j)).app q z)

end

end DaggerModels.OriginalOrdinaryMovingHomColimits
