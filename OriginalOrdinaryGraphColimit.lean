import OriginalOrdinaryGraphValues
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Colimits of ordinary simplicial graphs from total edges

The vertex type is a Type colimit.  The total edge simplicial set is the
colimit of the original total-edge diagram.  Homs are its exact endpoint
fibers.  No enriched composition or filteredness is used.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.SimplicialGraph.TotalSpace.Colimit

variable {J : Type u} [SmallCategory J] (F : J ⥤ SimplicialGraph.{u})

/-- The original vertex diagram, retaining the original object maps. -/
def objectDiagram : J ⥤ Type u where
  obj j := (F.obj j).Obj
  map α := (F.map α).obj
  map_id j := by
    funext x
    exact congrArg (fun k : F.obj j ⟶ F.obj j ↦ k.obj x) (F.map_id j)
  map_comp α β := by
    funext x
    exact congrArg (fun k : F.obj _ ⟶ F.obj _ ↦ k.obj x) (F.map_comp α β)

/-- The colimit vertices. -/
noncomputable def objects : Type u := colimit (objectDiagram F)

/-- The original vertex injections. -/
noncomputable def objectι (j : J) : (F.obj j).Obj → objects F :=
  colimit.ι (objectDiagram F) j

@[simp] theorem objectι_map {i j : J} (α : i ⟶ j) (x : (F.obj i).Obj) :
    objectι F j ((F.map α).obj x) = objectι F i x :=
  congrFun (colimit.w (objectDiagram F) α) x

/-- The original diagram of all edges, including their endpoint labels. -/
def edgeDiagram : J ⥤ SSet.{u} := F ⋙ TotalSpace.edgeFunctor

/-- Its actual simplicial-set colimit. -/
noncomputable def totalEdges : SSet.{u} := colimit (edgeDiagram F)

/-- The degreewise total-edge injection. -/
noncomputable def edgeι (j : J) : TotalSpace.edges (F.obj j) ⟶ totalEdges F :=
  colimit.ι (edgeDiagram F) j

/-- The source cocone into the constant simplicial set of colimit vertices. -/
noncomputable def sourceCocone : Cocone (edgeDiagram F) where
  pt := (Functor.const SimplexCategoryᵒᵖ).obj (objects F)
  ι :=
    { app j := TotalSpace.source (F.obj j) ≫
        (Functor.const SimplexCategoryᵒᵖ).map (objectι F j)
      naturality := by
        intro i j α
        ext n e
        exact objectι_map F α e.1 }

/-- The target cocone into the constant simplicial set of colimit vertices. -/
noncomputable def targetCocone : Cocone (edgeDiagram F) where
  pt := (Functor.const SimplexCategoryᵒᵖ).obj (objects F)
  ι :=
    { app j := TotalSpace.target (F.obj j) ≫
        (Functor.const SimplexCategoryᵒᵖ).map (objectι F j)
      naturality := by
        intro i j α
        ext n e
        exact objectι_map F α e.2.1 }

/-- Source endpoint on the total-edge colimit. -/
noncomputable def source : totalEdges F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (objects F) :=
  colimit.desc (edgeDiagram F) (sourceCocone F)

/-- Target endpoint on the total-edge colimit. -/
noncomputable def target : totalEdges F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (objects F) :=
  colimit.desc (edgeDiagram F) (targetCocone F)

@[simp] theorem source_ι (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (TotalSpace.edges (F.obj j)).obj n) :
    (source F).app n ((edgeι F j).app n e) = objectι F j e.1 := by
  change ((colimit.ι (edgeDiagram F) j ≫
    colimit.desc (edgeDiagram F) (sourceCocone F)).app n e) = _
  rw [colimit.ι_desc]
  rfl

@[simp] theorem target_ι (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (TotalSpace.edges (F.obj j)).obj n) :
    (target F).app n ((edgeι F j).app n e) = objectι F j e.2.1 := by
  change ((colimit.ι (edgeDiagram F) j ≫
    colimit.desc (edgeDiagram F) (targetCocone F)).app n e) = _
  rw [colimit.ι_desc]
  rfl

/-- A Hom is the exact fiber of both endpoint maps at every degree. -/
noncomputable def hom (x y : objects F) : SSet.{u} where
  obj n := { e : (totalEdges F).obj n //
    (source F).app n e = x ∧ (target F).app n e = y }
  map α e := ⟨(totalEdges F).map α e.1, by
    constructor
    · have h := congrFun ((source F).naturality α) e.1
      simpa only [Functor.const_obj_map, FunctorToTypes.map_id_apply] using h.trans e.2.1
    · have h := congrFun ((target F).naturality α) e.1
      simpa only [Functor.const_obj_map, FunctorToTypes.map_id_apply] using h.trans e.2.2⟩
  map_id n := by
    funext e
    apply Subtype.ext
    exact FunctorToTypes.map_id_apply (totalEdges F) e.1
  map_comp α β := by
    funext e
    apply Subtype.ext
    exact FunctorToTypes.map_comp_apply (totalEdges F) α β e.1

/-- The ordinary graph assembled from the original vertex and total-edge colimits. -/
noncomputable def point : SimplicialGraph.{u} where
  Obj := objects F
  Hom := hom F

/-- An original Hom simplex enters its exact colimit endpoint fiber. -/
noncomputable def legHom (j : J) (x y : (F.obj j).Obj) :
    (F.obj j).Hom x y ⟶ hom F (objectι F j x) (objectι F j y) where
  app n e := ⟨(edgeι F j).app n ⟨x, y, e⟩, by
    constructor
    · exact source_ι F j n ⟨x, y, e⟩
    · exact target_ι F j n ⟨x, y, e⟩⟩
  naturality {n m} α := by
    funext e
    apply Subtype.ext
    exact congrFun ((edgeι F j).naturality α) ⟨x, y, e⟩

/-- The graph leg retains the original object and Hom maps. -/
noncomputable def leg (j : J) : F.obj j ⟶ point F where
  obj := objectι F j
  map := legHom F j

end DaggerModels.SimplicialGraph.TotalSpace.Colimit

namespace DaggerModels.SimplicialGraph.TotalSpace.Colimit

variable {J : Type u} [SmallCategory J] (F : J ⥤ SimplicialGraph.{u})

/-- Forget endpoint labels from an edge of the assembled graph. -/
noncomputable def project : TotalSpace.edges (point F) ⟶ totalEdges F where
  app _ e := e.2.2.1
  naturality {n m} α := by
    funext e
    rfl

/-- A total point edge is determined by its underlying colimit edge. -/
theorem project_app_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((project F).app n) := by
  intro a b h
  rcases a with ⟨x, y, ⟨e, hx, hy⟩⟩
  rcases b with ⟨x', y', ⟨e', hx', hy'⟩⟩
  change e = e' at h
  subst e'
  subst x
  subst y
  subst x'
  subst y'
  rfl

/-- Reinsert the two endpoints of a colimit edge to obtain a total point edge. -/
noncomputable def reconstruct : totalEdges F ⟶ TotalSpace.edges (point F) where
  app n e := ⟨(source F).app n e, (target F).app n e, ⟨e, rfl, rfl⟩⟩
  naturality {n m} α := by
    funext e
    apply project_app_injective F m
    rfl

@[simp] theorem reconstruct_project : reconstruct F ≫ project F = 𝟙 (totalEdges F) := by
  ext n e
  rfl

@[simp] theorem project_reconstruct : project F ≫ reconstruct F =
    𝟙 (TotalSpace.edges (point F)) := by
  ext n e
  apply project_app_injective F n
  rfl

/-- Reconstruction sends every original total edge through the original graph leg. -/
theorem reconstruct_ι (j : J) :
    edgeι F j ≫ reconstruct F = TotalSpace.edgeMap (leg F j) := by
  ext n e
  apply project_app_injective F n
  rfl

/-- A graph map is determined by its vertex map and its map on total edges. -/
theorem map_ext_total {G H : SimplicialGraph.{u}} (p q : G ⟶ H)
    (ho : p.obj = q.obj) (he : TotalSpace.edgeMap p = TotalSpace.edgeMap q) : p = q := by
  cases p with
  | mk pobj pmap =>
    cases q with
    | mk qobj qmap =>
      dsimp only at ho
      cases ho
      apply SimplicialGraph.Map.ext
        (f := ⟨pobj, pmap⟩) (g := ⟨pobj, qmap⟩) rfl
      apply heq_of_eq
      funext x y
      ext n e
      have h := congrFun (NatTrans.congr_app he n) ⟨x, y, e⟩
      change (⟨pobj x, pobj y, (pmap x y).app n e⟩ : (TotalSpace.edges H).obj n) =
        ⟨pobj x, pobj y, (qmap x y).app n e⟩ at h
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

/-- Original graph legs form a cocone, including equality after both endpoint transports. -/
noncomputable def cocone : Cocone F where
  pt := point F
  ι :=
    { app := leg F
      naturality := by
        intro i j α
        apply map_ext_total
        · funext x
          exact objectι_map F α x
        · calc
            TotalSpace.edgeMap (F.map α ≫ leg F j) =
                TotalSpace.edgeMap (F.map α) ≫ TotalSpace.edgeMap (leg F j) :=
              TotalSpace.edgeFunctor.map_comp _ _
            _ = TotalSpace.edgeMap (F.map α) ≫ edgeι F j ≫ reconstruct F := by
              rw [reconstruct_ι]
            _ = edgeι F i ≫ reconstruct F := by
              rw [← Category.assoc]
              exact congrArg (fun k ↦ k ≫ reconstruct F) (colimit.w (edgeDiagram F) α)
            _ = TotalSpace.edgeMap (leg F i) := reconstruct_ι F i }

/-- A graph cocone induces the ordinary cocone on its original vertices. -/
def objectCocone (s : Cocone F) : Cocone (objectDiagram F) where
  pt := s.pt.Obj
  ι :=
    { app j := (s.ι.app j).obj
      naturality := by
        intro i j α
        funext x
        exact congrArg (fun k : F.obj i ⟶ s.pt ↦ k.obj x) (s.w α) }

/-- A graph cocone induces the simplicial-set cocone on all total edges. -/
def edgeCocone (s : Cocone F) : Cocone (edgeDiagram F) where
  pt := TotalSpace.edges s.pt
  ι :=
    { app j := TotalSpace.edgeMap (s.ι.app j)
      naturality := by
        intro i j α
        change TotalSpace.edgeFunctor.map (F.map α) ≫
          TotalSpace.edgeFunctor.map (s.ι.app j) =
          TotalSpace.edgeFunctor.map (s.ι.app i)
        rw [← Functor.map_comp, s.w α] }

/-- The unique object function supplied by the Type colimit. -/
noncomputable def objectDesc (s : Cocone F) : objects F → s.pt.Obj :=
  colimit.desc (objectDiagram F) (objectCocone F s)

/-- The unique simplicial map supplied by the total-edge colimit. -/
noncomputable def edgeDesc (s : Cocone F) : totalEdges F ⟶ TotalSpace.edges s.pt :=
  colimit.desc (edgeDiagram F) (edgeCocone F s)

@[simp] theorem objectDesc_ι (s : Cocone F) (j : J) (x : (F.obj j).Obj) :
    objectDesc F s (objectι F j x) = (s.ι.app j).obj x :=
  congrFun (colimit.ι_desc (objectCocone F s) j) x

@[simp] theorem edgeDesc_ι (s : Cocone F) (j : J) :
    edgeι F j ≫ edgeDesc F s = TotalSpace.edgeMap (s.ι.app j) :=
  colimit.ι_desc (edgeCocone F s) j

/-- Descending total edges respects the source endpoint. -/
theorem edgeDesc_source (s : Cocone F) :
    edgeDesc F s ≫ TotalSpace.source s.pt =
      source F ≫ (Functor.const SimplexCategoryᵒᵖ).map (objectDesc F s) := by
  apply colimit.hom_ext
  intro j
  simp only [← Category.assoc]
  change (edgeι F j ≫ edgeDesc F s) ≫ TotalSpace.source s.pt =
    (edgeι F j ≫ source F) ≫
      (Functor.const SimplexCategoryᵒᵖ).map (objectDesc F s)
  rw [edgeDesc_ι F s j]
  have hs : edgeι F j ≫ source F = (sourceCocone F).ι.app j :=
    colimit.ι_desc (sourceCocone F) j
  rw [hs]
  ext n e
  exact (objectDesc_ι F s j e.1).symm

/-- Descending total edges respects the target endpoint. -/
theorem edgeDesc_target (s : Cocone F) :
    edgeDesc F s ≫ TotalSpace.target s.pt =
      target F ≫ (Functor.const SimplexCategoryᵒᵖ).map (objectDesc F s) := by
  apply colimit.hom_ext
  intro j
  simp only [← Category.assoc]
  change (edgeι F j ≫ edgeDesc F s) ≫ TotalSpace.target s.pt =
    (edgeι F j ≫ target F) ≫
      (Functor.const SimplexCategoryᵒᵖ).map (objectDesc F s)
  rw [edgeDesc_ι F s j]
  have ht : edgeι F j ≫ target F = (targetCocone F).ι.app j :=
    colimit.ι_desc (targetCocone F) j
  rw [ht]
  ext n e
  exact (objectDesc_ι F s j e.2.1).symm

/-- The source equation on a chosen edge of the total-edge colimit. -/
theorem edgeDesc_source_apply (s : Cocone F) (n : SimplexCategoryᵒᵖ)
    (e : (totalEdges F).obj n) :
    ((edgeDesc F s).app n e).1 = objectDesc F s ((source F).app n e) :=
  congrFun (NatTrans.congr_app (edgeDesc_source F s) n) e

/-- The target equation on a chosen edge of the total-edge colimit. -/
theorem edgeDesc_target_apply (s : Cocone F) (n : SimplexCategoryᵒᵖ)
    (e : (totalEdges F).obj n) :
    ((edgeDesc F s).app n e).2.1 = objectDesc F s ((target F).app n e) :=
  congrFun (NatTrans.congr_app (edgeDesc_target F s) n) e

/-- The induced Hom map takes an exact fiber to the target graph's exact fiber. -/
noncomputable def homDesc (s : Cocone F) (x y : objects F) :
    hom F x y ⟶ s.pt.Hom (objectDesc F s x) (objectDesc F s y) where
  app n e :=
    TotalSpace.fiberEquiv s.pt (objectDesc F s x) (objectDesc F s y) n
      ⟨(edgeDesc F s).app n e.1, by
        constructor
        · rw [edgeDesc_source_apply F s n e.1, e.2.1]
        · rw [edgeDesc_target_apply F s n e.1, e.2.2]⟩
  naturality {n m} α := by
    funext e
    let z : {t : (TotalSpace.edges s.pt).obj n //
        t.1 = objectDesc F s x ∧ t.2.1 = objectDesc F s y} :=
      ⟨(edgeDesc F s).app n e.1, by
        constructor
        · rw [edgeDesc_source_apply F s n e.1, e.2.1]
        · rw [edgeDesc_target_apply F s n e.1, e.2.2]⟩
    change TotalSpace.fiberEquiv s.pt _ _ m
        ⟨(edgeDesc F s).app m ((totalEdges F).map α e.1), _⟩ =
      (s.pt.Hom _ _).map α (TotalSpace.fiberEquiv s.pt _ _ n z)
    rw [← TotalSpace.fiberEquiv_naturality s.pt _ _ α z]
    congr 1
    apply Subtype.ext
    exact congrFun ((edgeDesc F s).naturality α) e.1

/-- The graph map induced by any original graph cocone. -/
noncomputable def desc (s : Cocone F) : point F ⟶ s.pt where
  obj := objectDesc F s
  map := homDesc F s

end DaggerModels.SimplicialGraph.TotalSpace.Colimit

namespace DaggerModels.SimplicialGraph.TotalSpace.Colimit

variable {J : Type u} [SmallCategory J] (F : J ⥤ SimplicialGraph.{u})

/-- The point's total-edge map induced by descent is the original edge colimit map. -/
theorem reconstruct_desc (s : Cocone F) :
    reconstruct F ≫ TotalSpace.edgeMap (desc F s) = edgeDesc F s := by
  ext n e
  let z : {t : (TotalSpace.edges s.pt).obj n //
      t.1 = objectDesc F s ((source F).app n e) ∧
      t.2.1 = objectDesc F s ((target F).app n e)} :=
    ⟨(edgeDesc F s).app n e, by
      constructor
      · exact edgeDesc_source_apply F s n e
      · exact edgeDesc_target_apply F s n e⟩
  change (⟨objectDesc F s ((source F).app n e),
    objectDesc F s ((target F).app n e),
    TotalSpace.fiberEquiv s.pt _ _ n z⟩ : (TotalSpace.edges s.pt).obj n) = z.1
  exact congrArg Subtype.val ((TotalSpace.fiberEquiv s.pt _ _ n).left_inv z)

/-- The descended graph map has the required original graph legs. -/
theorem leg_desc (s : Cocone F) (j : J) : leg F j ≫ desc F s = s.ι.app j := by
  apply map_ext_total
  · funext x
    exact objectDesc_ι F s j x
  · calc
      TotalSpace.edgeMap (leg F j ≫ desc F s) =
          TotalSpace.edgeMap (leg F j) ≫ TotalSpace.edgeMap (desc F s) :=
        TotalSpace.edgeFunctor.map_comp _ _
      _ = edgeι F j ≫ reconstruct F ≫ TotalSpace.edgeMap (desc F s) := by
        rw [← reconstruct_ι F j]
        exact Category.assoc _ _ _
      _ = edgeι F j ≫ edgeDesc F s := by rw [reconstruct_desc]
      _ = TotalSpace.edgeMap (s.ι.app j) := edgeDesc_ι F s j

/-- The original legs jointly determine a graph map out of this point. -/
theorem hom_ext {H : SimplicialGraph.{u}} (p q : point F ⟶ H)
    (ho : p.obj = q.obj)
    (he : reconstruct F ≫ TotalSpace.edgeMap p =
      reconstruct F ≫ TotalSpace.edgeMap q) : p = q := by
  apply map_ext_total p q ho
  have h := congrArg (fun k ↦ project F ≫ k) he
  simpa only [← Category.assoc, project_reconstruct, Category.id_comp] using h

/-- The assembled cocone is a colimit for every small ordinary graph diagram. -/
noncomputable def isColimit : IsColimit (cocone F) where
  desc s := desc F s
  fac s j := leg_desc F s j
  uniq s m hm := by
    apply hom_ext F m (desc F s)
    · apply colimit.hom_ext (F := objectDiagram F)
      intro j
      funext x
      exact (congrArg (fun k : F.obj j ⟶ s.pt ↦ k.obj x) (hm j)).trans
        (objectDesc_ι F s j x).symm
    · calc
        reconstruct F ≫ TotalSpace.edgeMap m = edgeDesc F s := by
          apply colimit.hom_ext
          intro j
          change (edgeι F j ≫ reconstruct F) ≫ TotalSpace.edgeMap m =
            edgeι F j ≫ edgeDesc F s
          rw [reconstruct_ι F j, edgeDesc_ι F s j]
          change TotalSpace.edgeFunctor.map (leg F j) ≫
            TotalSpace.edgeFunctor.map m = TotalSpace.edgeFunctor.map (s.ι.app j)
          rw [← Functor.map_comp]
          exact congrArg TotalSpace.edgeFunctor.map (hm j)
      _ = reconstruct F ≫ TotalSpace.edgeMap (desc F s) :=
        (reconstruct_desc F s).symm

end DaggerModels.SimplicialGraph.TotalSpace.Colimit
