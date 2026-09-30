import DaggerModels.DaggerSimplicialForget

/-!
# The dagger graph forgetful functor reflects isomorphisms

This proves the reflection sentence in the second paragraph of Part I
`bg.lem.presentable`. The actual inverse dagger graph map acquires enriched
identity and composition preservation. Endpoint equalities are transported
explicitly, so object maps need not be identities. Monicity of each forward
mapping-space map is derived from the graph inverse.

The functor is the existing `DaggerSimplicialCat.forgetGraph`, for objects and
mapping spaces in the same arbitrary universe `u`. This module proves the
reflection ingredient, without claiming monadicity or local presentability.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.DaggerSimplicialCat

private lemma comp_eqToHom_of_heq {A B B' : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ B'} (h : B = B') (hh : HEq f g) :
    f ≫ eqToHom h = g := by
  subst h
  simpa using eq_of_heq hh

private lemma graph_comp_obj {G H : DaggerSimplicialGraph.{u}}
    (f : G ⟶ H) (g : H ⟶ G) (h : f ≫ g = 𝟙 G) (x : G.Obj) :
    g.obj (f.obj x) = x := congrArg (fun k : G ⟶ G ↦ k.obj x) h

private lemma graph_comp_map {G H : DaggerSimplicialGraph.{u}}
    (f : G ⟶ H) (g : H ⟶ G) (h : f ≫ g = 𝟙 G) (x y : G.Obj) :
    f.map x y ≫ g.map (f.obj x) (f.obj y) ≫
      eqToHom (by rw [graph_comp_obj f g h x, graph_comp_obj f g h y]) = 𝟙 _ := by
  rw [← Category.assoc]
  apply comp_eqToHom_of_heq
  exact congr_arg_heq (fun k : G ⟶ G ↦ k.map x y) h

private lemma eId_transport (C : Type u) [EnrichedCategory SSet.{u} C]
    {x x' : C} (h : x = x') :
    eId SSet x ≫ eqToHom (by rw [h]) = eId SSet x' := by
  subst h
  simp

private lemma eComp_transport (C : Type u) [EnrichedCategory SSet.{u} C]
    {x y z x' y' z' : C} (hx : x = x') (hy : y = y') (hz : z = z') :
    eComp SSet x y z ≫ eqToHom (by rw [hx, hz]) =
      (eqToHom (by rw [hx, hy]) ⊗ₘ eqToHom (by rw [hy, hz])) ≫
        eComp SSet x' y' z' := by
  subst hx
  subst hy
  subst hz
  simp

section Inverse

variable {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
  (g : underlyingGraph D ⟶ underlyingGraph C)
  (hfg : underlyingGraphMap F ≫ g = 𝟙 (underlyingGraph C))
  (hgf : g ≫ underlyingGraphMap F = 𝟙 (underlyingGraph D))

include g hfg in
private lemma map_mono (x y : C.Obj) : Mono (F.map x y) := by
  apply SplitMono.mono
  have hx : g.obj (F.obj x) = x := graph_comp_obj _ _ hfg x
  have hy : g.obj (F.obj y) = y := graph_comp_obj _ _ hfg y
  refine ⟨g.map (F.obj x) (F.obj y) ≫ eqToHom
    (by rw [hx, hy]; rfl), ?_⟩
  simpa only [Category.assoc] using graph_comp_map (underlyingGraphMap F) g hfg x y

private lemma inverse_map_comp (x y : D.Obj) :
    g.map x y ≫ F.map (g.obj x) (g.obj y) =
      eqToHom (by
        change D.enriched.Hom x y = D.enriched.Hom
          ((underlyingGraphMap F).obj (g.obj x)) ((underlyingGraphMap F).obj (g.obj y))
        rw [graph_comp_obj g (underlyingGraphMap F) hgf x,
          graph_comp_obj g (underlyingGraphMap F) hgf y]) := by
  have h := graph_comp_map g (underlyingGraphMap F) hgf x y
  have hx : F.obj (g.obj x) = x := graph_comp_obj _ _ hgf x
  have hy : F.obj (g.obj y) = y := graph_comp_obj _ _ hgf y
  apply (cancel_mono (eqToHom
    (congrArg₂ (fun a b : D.Obj ↦ (a ⟶[SSet] b)) hx hy))).1
  simpa using h

/-- Lift a specified two-sided graph inverse, retaining its exact object and hom maps. -/
def inverseOfGraphInverse : Hom D C where
  obj := g.obj
  map := g.map
  map_id x := by
    have : Mono (F.map (g.obj x) (g.obj x)) := map_mono F g hfg _ _
    apply (cancel_mono (F.map (g.obj x) (g.obj x))).1
    rw [Category.assoc, inverse_map_comp F g hgf, F.map_id]
    exact eId_transport D.Obj (graph_comp_obj g (underlyingGraphMap F) hgf x).symm
  map_comp x y z := by
    have : Mono (F.map (g.obj x) (g.obj z)) := map_mono F g hfg _ _
    apply (cancel_mono (F.map (g.obj x) (g.obj z))).1
    rw [Category.assoc, inverse_map_comp F g hgf, Category.assoc, F.map_comp,
      ← Category.assoc, tensorHom_comp_tensorHom,
      inverse_map_comp F g hgf, inverse_map_comp F g hgf]
    exact eComp_transport D.Obj (graph_comp_obj g (underlyingGraphMap F) hgf x).symm
      (graph_comp_obj g (underlyingGraphMap F) hgf y).symm
      (graph_comp_obj g (underlyingGraphMap F) hgf z).symm
  map_dagger := g.map_dagger

/-- Forgetting the lifted inverse recovers the specified graph map exactly. -/
@[simp] theorem underlyingGraphMap_inverseOfGraphInverse :
    underlyingGraphMap (inverseOfGraphInverse F g hfg hgf) = g := rfl

end Inverse

/-- Every specified two-sided graph inverse lifts to a full dagger enriched functor.
The object equations and heterogeneous hom equations are the raw components of
the two graph inverse laws. No identity-on-objects or monicity assumption is added. -/
theorem exists_inverseOfGraphInverse {C D : DaggerSimplicialCat.{u, u}} (F : Hom C D)
    (g : DaggerSimplicialGraph.Map (underlyingGraph D) (underlyingGraph C))
    (hfg_obj : g.obj ∘ F.obj = id)
    (hfg_map : HEq (fun x y ↦ F.map x y ≫ g.map (F.obj x) (F.obj y))
      (fun x y : C.Obj ↦ 𝟙 (x ⟶[SSet.{u}] y)))
    (hgf_obj : F.obj ∘ g.obj = id)
    (hgf_map : HEq (fun x y ↦ g.map x y ≫ F.map (g.obj x) (g.obj y))
      (fun x y : D.Obj ↦ 𝟙 (x ⟶[SSet.{u}] y))) :
    ∃ G : Hom D C, underlyingGraphMap G = g := by
  have hfg : underlyingGraphMap F ≫ g = 𝟙 (underlyingGraph C) :=
    DaggerSimplicialGraph.Map.ext hfg_obj hfg_map
  have hgf : g ≫ underlyingGraphMap F = 𝟙 (underlyingGraph D) :=
    DaggerSimplicialGraph.Map.ext hgf_obj hgf_map
  exact ⟨inverseOfGraphInverse F g hfg hgf, rfl⟩

/-- The inverse graph map is automatically an inverse dagger enriched functor. -/
noncomputable def inverseOfGraphIso {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    [IsIso (forgetGraph.map F)] : Hom D C :=
  inverseOfGraphInverse F (inv (forgetGraph.map F))
    (IsIso.hom_inv_id (forgetGraph.map F)) (IsIso.inv_hom_id (forgetGraph.map F))

/-- The enriched inverse has the actual graph inverse as its underlying graph map. -/
@[simp] theorem underlyingGraphMap_inverseOfGraphIso
    {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) [IsIso (forgetGraph.map F)] :
    underlyingGraphMap (inverseOfGraphIso F) = inv (forgetGraph.map F) := rfl

/-- The forward functor followed by its lifted inverse is the actual identity functor. -/
@[simp] theorem comp_inverseOfGraphIso {C D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ D) [IsIso (forgetGraph.map F)] : F ≫ inverseOfGraphIso F = 𝟙 C := by
  apply forgetGraph.map_injective
  change forgetGraph.map F ≫ underlyingGraphMap (inverseOfGraphIso F) = 𝟙 _
  rw [underlyingGraphMap_inverseOfGraphIso, IsIso.hom_inv_id]

/-- The lifted inverse followed by the forward functor is also the actual identity functor. -/
@[simp] theorem inverseOfGraphIso_comp {C D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ D) [IsIso (forgetGraph.map F)] : inverseOfGraphIso F ≫ F = 𝟙 D := by
  apply forgetGraph.map_injective
  change underlyingGraphMap (inverseOfGraphIso F) ≫ forgetGraph.map F = 𝟙 _
  rw [underlyingGraphMap_inverseOfGraphIso, IsIso.inv_hom_id]

/-- The reflection ingredient of the second paragraph of Part I `bg.lem.presentable`. -/
instance forgetGraphReflectsIsomorphisms : forgetGraph.{u}.ReflectsIsomorphisms where
  reflects F := ⟨inverseOfGraphIso F, comp_inverseOfGraphIso F, inverseOfGraphIso_comp F⟩

/-- The actual graph forgetful functor reflects isomorphisms. -/
theorem forgetGraph_reflectsIsomorphisms : forgetGraph.{u}.ReflectsIsomorphisms := inferInstance

end DaggerModels.DaggerSimplicialCat
