import DaggerModels.DaggerSimplicialGraph
import DaggerModels.DaggerSimplicialCategory
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Simplicial paths in a dagger simplicial graph

The hom simplicial sets consist of actual finite quiver paths, including the
empty path. Simplicial operators act on each edge. Dagger reverses the order
of the edges and applies the graph dagger to each edge, without reversing
the simplicial operator. This is the free-word construction of Part I
`bg.lem.presentable`. The common arbitrary universe `u` ensures that the
path homs have the same universe as the objects and edges.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.FreeSimplicialPaths

/-- The graph's vertex type viewed in a fixed simplicial degree. -/
def At (G : DaggerSimplicialGraph.{u}) (_n : SimplexCategoryᵒᵖ) : Type u := G.Obj

/-- The quiver of edges in simplicial degree `n`. -/
def quiverAt (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver G.Obj where
  Hom x y := (G.Hom x y).obj n

instance (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver (At G n) :=
  quiverAt G n

instance (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    Quiver.HasInvolutiveReverse (At G n) where
  reverse' := fun {x y} e ↦ (G.dagger x y).app n e
  inv' := fun {x y} e ↦ G.dagger_app_involutive x y n e

/-- Actual finite composable words in the graph's degreewise edges. -/
abbrev Path (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (x y : G.Obj) : Type u :=
  @Quiver.Path (At G n) (quiverAt G n) x y

/-- An ordinary simplicial operator acting on the degreewise edge quiver. -/
def operator (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    At G m ⥤q At G n where
  obj := id
  map := fun {x y} e ↦ (G.Hom x y).map f e

/-- Apply a simplicial operator to every edge in a path. -/
def map (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    {x y : G.Obj} (p : Path G m x y) : Path G n x y := (operator G f).mapPath p

@[simp] theorem map_nil (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) (x : G.Obj) : map G f (Quiver.Path.nil : Path G m x x) = .nil := rfl

@[simp] theorem map_cons (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (e : (G.Hom y z).obj m) :
    map G f (p.cons e) = (map G f p).cons ((G.Hom y z).map f e) := rfl

@[simp] theorem map_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : map G (𝟙 n) p = p := by
  letI := quiverAt G n
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (map G (𝟙 n) p).cons ((G.Hom _ _).map (𝟙 n) e) = p.cons e
    rw [ih, FunctorToTypes.map_id_apply]

@[simp] theorem map_comp (G : DaggerSimplicialGraph.{u}) {l m n : SimplexCategoryᵒᵖ}
    (f : l ⟶ m) (g : m ⟶ n) {x y : G.Obj} (p : Path G l x y) :
    map G (f ≫ g) p = map G g (map G f p) := by
  letI := quiverAt G n
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (map G (f ≫ g) p).cons ((G.Hom _ _).map (f ≫ g) e) =
      (map G g (map G f p)).cons ((G.Hom _ _).map g ((G.Hom _ _).map f e))
    rw [ih, FunctorToTypes.map_comp_apply]

@[simp] theorem map_pathComp (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (q : Path G m y z) :
    map G f (p.comp q) = (map G f p).comp (map G f q) :=
  Prefunctor.mapPath_comp (operator G f) p q

/-- The simplicial set of paths from `x` to `y`. -/
def hom (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : SSet.{u} where
  obj n := Path G n x y
  map f := map G f
  map_id n := by funext p; exact map_id G n p
  map_comp f g := by funext p; exact map_comp G f g p

/-- The canonical inclusion of an edge as a singleton path. -/
def inclusion (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : G.Hom x y ⟶ hom G x y where
  app n e := @Quiver.Hom.toPath (At G n) (quiverAt G n) x y e
  naturality _ _ _ := rfl

/-- The empty path is the enriched identity. -/
def id (G : DaggerSimplicialGraph.{u}) (x : G.Obj) : 𝟙_ SSet.{u} ⟶ hom G x x where
  app _ _ := Quiver.Path.nil
  naturality _ _ _ := rfl

/-- Enriched composition concatenates two paths. -/
def comp (G : DaggerSimplicialGraph.{u}) (x y z : G.Obj) :
    hom G x y ⊗ hom G y z ⟶ hom G x z where
  app _ p := p.1.comp p.2
  naturality m n f := by
    funext p
    exact (map_pathComp G f p.1 p.2).symm

/-- The actual simplicial enrichment on the graph's vertices. -/
def enrichedCategory (G : DaggerSimplicialGraph.{u}) : EnrichedCategory SSet.{u} G.Obj where
  Hom := hom G
  id := id G
  comp := comp G
  id_comp x y := by
    ext n p
    exact Quiver.Path.nil_comp p
  comp_id x y := by
    ext n p
    exact Quiver.Path.comp_nil p
  assoc w x y z := by
    ext n p
    exact Quiver.Path.comp_assoc p.1 p.2.1 p.2.2

attribute [local instance] enrichedCategory

/-- The bundled simplicial category of finite words. -/
def simplicialCat (G : DaggerSimplicialGraph.{u}) : SimplicialCat.{u, u} :=
  SimplicialCat.of G.Obj

/-- Reverse the word and apply the graph dagger to each letter. -/
def reverse (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : Path G n y x := p.reverse

@[simp] theorem reverse_nil (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (x : G.Obj) : reverse G n (Quiver.Path.nil : Path G n x x) = .nil := rfl

@[simp] theorem reverse_cons (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y z : G.Obj} (p : Path G n x y) (e : (G.Hom y z).obj n) :
    reverse G n (p.cons e) =
      (@Quiver.Hom.toPath (At G n) (quiverAt G n) z y ((G.dagger y z).app n e)).comp
        (reverse G n p) := rfl

@[simp] theorem reverse_comp (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y z : G.Obj} (p : Path G n x y) (q : Path G n y z) :
    reverse G n (p.comp q) = (reverse G n q).comp (reverse G n p) :=
  Quiver.Path.reverse_comp p q

@[simp] theorem reverse_involutive (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : Path G n x y) :
    reverse G n (reverse G n p) = p := Quiver.Path.reverse_reverse p

instance operator_mapReverse (G : DaggerSimplicialGraph.{u})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) : (operator G f).MapReverse where
  map_reverse' {x y} e :=
    (congrFun ((G.dagger x y).naturality f) e).symm

private theorem mapPath_reverse {V W : Type u} [Quiver.{u + 1} V] [Quiver.{u + 1} W]
    [Quiver.HasReverse V] [Quiver.HasReverse W] (F : V ⥤q W) [F.MapReverse]
    {x y : V} (p : Quiver.Path x y) : F.mapPath p.reverse = (F.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Quiver.Path.reverse, Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
      Prefunctor.map_reverse, ih, Prefunctor.mapPath_cons]

@[simp] theorem map_reverse (G : DaggerSimplicialGraph.{u})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) {x y : G.Obj} (p : Path G m x y) :
    map G f (reverse G m p) = reverse G n (map G f p) :=
  mapPath_reverse (operator G f) p

/-- The path dagger is an ordinary simplicial map. -/
def dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : hom G x y ⟶ hom G y x where
  app n := reverse G n
  naturality m n f := by
    funext p
    exact (map_reverse G f p).symm

@[simp] theorem dagger_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    dagger G x y ≫ dagger G y x = 𝟙 (hom G x y) := by
  ext n p
  exact reverse_involutive G n p

@[simp] theorem inclusion_dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    inclusion G x y ≫ dagger G x y = G.dagger x y ≫ inclusion G y x := rfl

@[simp] theorem id_dagger (G : DaggerSimplicialGraph.{u}) (x : G.Obj) :
    id G x ≫ dagger G x x = id G x := rfl

/-- Dagger reverses the order of the enriched composition factors. -/
theorem comp_dagger (G : DaggerSimplicialGraph.{u}) (x y z : G.Obj) :
    comp G x y z ≫ dagger G x z =
      (dagger G x y ⊗ₘ dagger G y z) ≫
        (β_ (hom G y x) (hom G z y)).hom ≫ comp G z y x := by
  ext n p
  exact reverse_comp G n p.1 p.2

/-- The free paths carry the identity-on-objects simplicial dagger. -/
noncomputable def daggerStructure (G : DaggerSimplicialGraph.{u}) :
    DaggerSimplicialStructure G.Obj where
  dagger := dagger G
  dagger_involutive := dagger_involutive G
  dagger_id := id_dagger G
  dagger_comp := comp_dagger G

/-- The actual dagger simplicial category of finite paths in the graph. -/
noncomputable def daggerCat (G : DaggerSimplicialGraph.{u}) : DaggerSimplicialCat.{u, u} :=
  ⟨simplicialCat G, daggerStructure G⟩

/-- The degreewise mapping-space elements are exactly the graph's finite paths. -/
def homObjEquiv (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) (n : SimplexCategoryᵒᵖ) :
    (hom G x y).obj n ≃ Path G n x y := Equiv.refl _

end DaggerModels.FreeSimplicialPaths
