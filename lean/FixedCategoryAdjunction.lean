import FixedGraphCore
import DaggerModels.FreeSimplicialMap
import Mathlib.Logic.Equiv.Basic

/-! The original fixed-object dagger simplicial categories and their actual free adjunction.
The object type is literally `O`; every arrow is an original enriched dagger functor with
object function `id`. The free paths, maps and Hom equivalence are restricted from the
existing graph-free construction. No limits, colimits or model structure are asserted.
-/

open CategoryTheory

universe u

namespace DaggerModels

/-- A full simplicial enrichment and dagger on the original object type. -/
structure FixedDaggerSimplicialCat (O : Type u) where
  enriched : EnrichedCategory SSet.{u} O
  daggerStructure : @DaggerSimplicialStructure O enriched

namespace FixedDaggerSimplicialCat

variable {O : Type u}

/-- The original ambient category, with no change to its objects or Hom spaces. -/
def toCat (C : FixedDaggerSimplicialCat O) : DaggerSimplicialCat.{u, u} :=
  ⟨⟨O, C.enriched⟩, C.daggerStructure⟩

/-- All original enriched functors with identity object function. -/
abbrev Hom (C D : FixedDaggerSimplicialCat O) :=
  {f : C.toCat ⟶ D.toCat // f.obj = id}

instance : Category (FixedDaggerSimplicialCat O) where
  Hom := Hom
  id C := ⟨𝟙 C.toCat, rfl⟩
  comp f g := ⟨f.val ≫ g.val, by
    funext x
    change g.val.obj (f.val.obj x) = x
    rw [f.property, g.property]
    rfl⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- The adapter keeps the entire original enriched dagger functor. -/
def forget (O : Type u) : FixedDaggerSimplicialCat O ⥤ DaggerSimplicialCat.{u, u} where
  obj := toCat
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget O).Faithful where
  map_injective := fun h ↦ Subtype.ext h

@[simp] theorem toCat_obj (C : FixedDaggerSimplicialCat O) : C.toCat.Obj = O := rfl

@[simp] theorem forget_map_obj {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    ((forget O).map f).obj = id := f.property

/-- Forget only identity and composition, retaining the original full Hom and dagger. -/
def underlyingGraph (C : FixedDaggerSimplicialCat O) : FixedDaggerSimplicialGraph O where
  Hom := C.toCat.underlyingGraph.Hom
  dagger := C.toCat.underlyingGraph.dagger
  dagger_involutive := C.toCat.underlyingGraph.dagger_involutive

/-- Restrict the actual ambient graph map using its identity object equation. -/
def underlyingGraphMap {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    C.underlyingGraph ⟶ D.underlyingGraph :=
  FixedDaggerSimplicialGraph.fromGraphMap
    (DaggerSimplicialCat.forgetGraph.map f.val) f.property

theorem graph_map_injective {G H : FixedDaggerSimplicialGraph O} {f g : G ⟶ H}
    (h : FixedDaggerSimplicialGraph.toGraphMap f =
      FixedDaggerSimplicialGraph.toGraphMap g) : f = g :=
  FixedDaggerSimplicialGraph.mapEquiv.injective (Subtype.ext h)

/-- The full ambient map is exactly the original map after the graph adapter. -/
theorem underlyingGraphMap_toGraph {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    FixedDaggerSimplicialGraph.toGraphMap (underlyingGraphMap f) =
      DaggerSimplicialCat.forgetGraph.map f.val := by
  exact congrArg Subtype.val
    ((FixedDaggerSimplicialGraph.mapEquiv
      (G := C.underlyingGraph) (H := D.underlyingGraph)).apply_symm_apply
      ⟨DaggerSimplicialCat.forgetGraph.map f.val, f.property⟩)

/-- The actual fixed-object graph forgetful functor. -/
def forgetGraph (O : Type u) :
    FixedDaggerSimplicialCat O ⥤ FixedDaggerSimplicialGraph O where
  obj := underlyingGraph
  map := underlyingGraphMap
  map_id C := by
    apply graph_map_injective
    rw [underlyingGraphMap_toGraph]
    exact DaggerSimplicialCat.forgetGraph.map_id C.toCat
  map_comp f g := by
    apply graph_map_injective
    rw [underlyingGraphMap_toGraph]
    change DaggerSimplicialCat.forgetGraph.map (f.val ≫ g.val) =
      FixedDaggerSimplicialGraph.toGraphMap (underlyingGraphMap f) ≫
        FixedDaggerSimplicialGraph.toGraphMap (underlyingGraphMap g)
    rw [underlyingGraphMap_toGraph, underlyingGraphMap_toGraph, Functor.map_comp]

theorem forgetGraph_toGraph_obj (C : FixedDaggerSimplicialCat O) :
    ((forgetGraph O).obj C).toGraph = DaggerSimplicialCat.forgetGraph.obj C.toCat := rfl

theorem forgetGraph_toGraph_map {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    FixedDaggerSimplicialGraph.toGraphMap ((forgetGraph O).map f) =
      DaggerSimplicialCat.forgetGraph.map ((forget O).map f) :=
  underlyingGraphMap_toGraph f

end FixedDaggerSimplicialCat
end DaggerModels

namespace DaggerFixedCategoryAdjunction

open DaggerModels
open FixedDaggerSimplicialCat

variable {O : Type u}

noncomputable section

/-- The original finite-path enrichment and dagger, now bundled on literal `O`. -/
def freeObj (G : FixedDaggerSimplicialGraph O) : FixedDaggerSimplicialCat O where
  enriched := FreeSimplicialPaths.enrichedCategory G.toGraph
  daggerStructure := FreeSimplicialPaths.daggerStructure G.toGraph

theorem freeObj_toCat (G : FixedDaggerSimplicialGraph O) :
    (freeObj G).toCat = FreeDaggerSimplicialCategory.functor.obj G.toGraph := rfl

/-- Restrict the actual ambient free map, retaining every path component. -/
def freeMap {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) : freeObj G ⟶ freeObj H :=
  ⟨FreeDaggerSimplicialCategory.functor.map (FixedDaggerSimplicialGraph.toGraphMap f), by
    rw [FreeDaggerSimplicialCategory.functor_map_obj]
    rfl⟩

/-- The actual free functor on the original fixed-object categories. -/
def free (O : Type u) : FixedDaggerSimplicialGraph O ⥤ FixedDaggerSimplicialCat O where
  obj := freeObj
  map := freeMap
  map_id G := Subtype.ext (FreeDaggerSimplicialCategory.functor.map_id G.toGraph)
  map_comp f g := Subtype.ext (FreeDaggerSimplicialCategory.functor.map_comp
    (FixedDaggerSimplicialGraph.toGraphMap f) (FixedDaggerSimplicialGraph.toGraphMap g))

theorem free_toCat_map {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (FixedDaggerSimplicialCat.forget O).map ((free O).map f) =
      FreeDaggerSimplicialCategory.functor.map (FixedDaggerSimplicialGraph.toGraphMap f) := rfl

/-- The original Hom equivalence restricted to the exact identity-object predicates. -/
def restrictedHomEquiv (G : FixedDaggerSimplicialGraph O) (C : FixedDaggerSimplicialCat O) :
    (freeObj G ⟶ C) ≃
      {f : G.toGraph ⟶ C.underlyingGraph.toGraph // f.obj = id} :=
  (FreeDaggerSimplicialCategory.homEquiv G.toGraph C.toCat).subtypeEquiv
    (p := fun (f : FreeSimplicialPaths.daggerCat G.toGraph ⟶ C.toCat) ↦ f.obj = id)
    (q := fun (f : G.toGraph ⟶ DaggerSimplicialCat.forgetGraph.obj C.toCat) ↦ f.obj = id)
    (fun _ ↦ Iff.rfl)

/-- The full fixed-object Hom equivalence uses the existing graph map adapter. -/
def homEquiv (G : FixedDaggerSimplicialGraph O) (C : FixedDaggerSimplicialCat O) :
    (freeObj G ⟶ C) ≃ (G ⟶ C.underlyingGraph) :=
  (restrictedHomEquiv G C).trans
    (FixedDaggerSimplicialGraph.mapEquiv (G := G) (H := C.underlyingGraph)).symm

theorem homEquiv_forward (G : FixedDaggerSimplicialGraph O) (C : FixedDaggerSimplicialCat O)
    (f : freeObj G ⟶ C) :
    FixedDaggerSimplicialGraph.toGraphMap (homEquiv G C f) =
      FreeDaggerSimplicialCategory.homEquiv G.toGraph C.toCat f.val := by
  exact congrArg Subtype.val
    ((FixedDaggerSimplicialGraph.mapEquiv (G := G) (H := C.underlyingGraph)).apply_symm_apply
      (restrictedHomEquiv G C f))

theorem homEquiv_inverse (G : FixedDaggerSimplicialGraph O) (C : FixedDaggerSimplicialCat O)
    (f : G ⟶ C.underlyingGraph) :
    ((homEquiv G C).symm f).val =
      (FreeDaggerSimplicialCategory.homEquiv G.toGraph C.toCat).symm
        (FixedDaggerSimplicialGraph.toGraphMap f) := rfl

theorem homEquiv_naturality_right {G : FixedDaggerSimplicialGraph O}
    {C D : FixedDaggerSimplicialCat O} (f : freeObj G ⟶ C) (g : C ⟶ D) :
    homEquiv G D (f ≫ g) = homEquiv G C f ≫ (forgetGraph O).map g := by
  apply graph_map_injective
  rw [homEquiv_forward]
  change FreeDaggerSimplicialCategory.homEquiv G.toGraph D.toCat (f.val ≫ g.val) =
    FixedDaggerSimplicialGraph.toGraphMap (homEquiv G C f) ≫
      FixedDaggerSimplicialGraph.toGraphMap ((forgetGraph O).map g)
  rw [homEquiv_forward, forgetGraph_toGraph_map]
  exact FreeDaggerSimplicialCategory.homEquiv_naturality G.toGraph C.toCat D.toCat g.val f.val

theorem homEquiv_naturality_left_symm {G H : FixedDaggerSimplicialGraph O}
    {C : FixedDaggerSimplicialCat O} (f : G ⟶ H) (g : H ⟶ C.underlyingGraph) :
    (homEquiv G C).symm (f ≫ g) = (free O).map f ≫ (homEquiv H C).symm g := by
  apply Subtype.ext
  rw [homEquiv_inverse]
  change (FreeDaggerSimplicialCategory.homEquiv G.toGraph C.toCat).symm
      (FixedDaggerSimplicialGraph.toGraphMap f ≫ FixedDaggerSimplicialGraph.toGraphMap g) =
    FreeDaggerSimplicialCategory.functor.map (FixedDaggerSimplicialGraph.toGraphMap f) ≫
      ((homEquiv H C).symm g).val
  rw [homEquiv_inverse]
  have h := FreeDaggerSimplicialCategory.adjunction.homEquiv_naturality_left_symm
    (X' := G.toGraph) (X := H.toGraph) (Y := C.toCat)
    (FixedDaggerSimplicialGraph.toGraphMap f) (FixedDaggerSimplicialGraph.toGraphMap g)
  simpa only [FreeDaggerSimplicialCategory.adjunction, Adjunction.adjunctionOfEquivLeft,
    Adjunction.mkOfHomEquiv_homEquiv] using h

/-- The original free/forgetful adjunction restricted to all identity-object enriched maps. -/
def adjunction (O : Type u) : free O ⊣ forgetGraph O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm
      homEquiv_naturality_right := homEquiv_naturality_right }

theorem adjunction_homEquiv (G : FixedDaggerSimplicialGraph O)
    (C : FixedDaggerSimplicialCat O) :
    (adjunction O).homEquiv G C = homEquiv G C := by
  exact congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) G) C

/-- The actual unit is the original singleton-edge map in all degrees. -/
theorem unit_toGraph (G : FixedDaggerSimplicialGraph O) :
    FixedDaggerSimplicialGraph.toGraphMap ((adjunction O).unit.app G) =
      FreeDaggerSimplicialCategory.unit G.toGraph := by
  change FixedDaggerSimplicialGraph.toGraphMap (homEquiv G (freeObj G) (𝟙 _)) = _
  rw [homEquiv_forward]
  change FreeDaggerSimplicialCategory.unit G.toGraph ≫
    DaggerSimplicialCat.forgetGraph.map (𝟙 _) = _
  simp

/-- The actual counit is the original path-composition extension, including empty paths. -/
theorem counit_toCat (C : FixedDaggerSimplicialCat O) :
    ((adjunction O).counit.app C).val =
      FreeDaggerSimplicialCategory.lift (𝟙 (DaggerSimplicialCat.underlyingGraph C.toCat)) := by
  change ((homEquiv C.underlyingGraph C).symm (𝟙 _)).val = _
  rw [homEquiv_inverse]
  rfl

theorem unit_ambient (G : FixedDaggerSimplicialGraph O) :
    FixedDaggerSimplicialGraph.toGraphMap ((adjunction O).unit.app G) =
      FreeDaggerSimplicialCategory.adjunction.unit.app G.toGraph := by
  rw [unit_toGraph, FreeDaggerSimplicialCategory.adjunction_unit]

theorem counit_ambient (C : FixedDaggerSimplicialCat O) :
    ((adjunction O).counit.app C).val =
      FreeDaggerSimplicialCategory.adjunction.counit.app C.toCat := by
  rw [counit_toCat]
  rfl

/-- The original free functor acts edgewise on every actual finite path. -/
theorem free_map_app {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) {x y : O} (p : FreeSimplicialPaths.Path G.toGraph n x y) :
    (((free O).map f).val.map x y).app n p =
      (FreeDaggerSimplicialCategory.degreeMap
        (FixedDaggerSimplicialGraph.toGraphMap f) n).mapPath p :=
  FreeDaggerSimplicialCategory.functor_map_app _ n p

/-- The actual fixed unit includes the same original edge as a path of length one. -/
theorem unit_app (G : FixedDaggerSimplicialGraph O) (n : SimplexCategoryᵒᵖ) {x y : O}
    (e : (G.Hom x y).obj n) :
    (((adjunction O).unit.app G).map x y).app n e =
      @Quiver.Hom.toPath (FreeSimplicialPaths.At G.toGraph n)
        (FreeSimplicialPaths.quiverAt G.toGraph n) x y e := rfl

/-- Evaluate any original path by the original enriched identities and composition. -/
theorem counit_app (C : FixedDaggerSimplicialCat O) (n : SimplexCategoryᵒᵖ) {x y : O}
    (p : FreeSimplicialPaths.Path C.underlyingGraph.toGraph n x y) :
    (((adjunction O).counit.app C).val.map x y).app n p =
      FreeSimplicialExtension.value C.underlyingGraph.toGraph (C := C.toCat.Obj)
        id (fun x y ↦ 𝟙 (C.underlyingGraph.Hom x y)) n p := rfl

theorem counit_nil (C : FixedDaggerSimplicialCat O) (n : SimplexCategoryᵒᵖ) (x : O) :
    (((adjunction O).counit.app C).val.map x x).app n Quiver.Path.nil =
      (C.enriched.id x).app n PUnit.unit := rfl

theorem homEquiv_naturality_left {G H : FixedDaggerSimplicialGraph O}
    {C : FixedDaggerSimplicialCat O} (f : G ⟶ H) (g : freeObj H ⟶ C) :
    homEquiv G C ((free O).map f ≫ g) = f ≫ homEquiv H C g := by
  have h := (adjunction O).homEquiv_naturality_left f g
  simpa only [adjunction_homEquiv] using h

theorem homEquiv_naturality_right_symm {G : FixedDaggerSimplicialGraph O}
    {C D : FixedDaggerSimplicialCat O} (f : G ⟶ C.underlyingGraph) (g : C ⟶ D) :
    (homEquiv G D).symm (f ≫ (forgetGraph O).map g) =
      (homEquiv G C).symm f ≫ g := by
  have h := (adjunction O).homEquiv_naturality_right_symm f g
  simpa only [adjunction_homEquiv] using h

end
end DaggerFixedCategoryAdjunction
