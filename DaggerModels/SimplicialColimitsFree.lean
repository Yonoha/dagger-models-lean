import DaggerModels.SimplicialCat
import DaggerModels.SimplicialEnrichment
import Mathlib.CategoryTheory.PathCategory.Basic

/-! Ordinary simplicial graphs, finite paths, and their unrestricted
free enriched universal property. No dagger or colimit existence is assumed. -/

open CategoryTheory MonoidalCategory
universe u
namespace DaggerModels
structure SimplicialGraph where
  Obj : Type u
  Hom : Obj → Obj → SSet.{u}
namespace SimplicialGraph
structure Map (G H : SimplicialGraph.{u}) where
  obj : G.Obj → H.Obj
  map : ∀ x y, G.Hom x y ⟶ H.Hom (obj x) (obj y)
@[ext] theorem Map.ext {G H : SimplicialGraph.{u}} {f g : Map G H}
    (hobj : f.obj = g.obj) (hmap : HEq f.map g.map) : f = g := by
  cases f
  cases g
  cases hobj
  cases hmap
  rfl
theorem Map.ext' {G H : SimplicialGraph.{u}} {f g : Map G H}
    (hobj : ∀ x, f.obj x = g.obj x)
    (hmap : ∀ x y, f.map x y ≫ eqToHom (by rw [hobj, hobj]) = g.map x y) : f = g := by
  match f, g with
  | ⟨fobj, fmap⟩, ⟨gobj, gmap⟩ =>
    obtain rfl : fobj = gobj := funext hobj
    congr
    funext x y
    simpa using hmap x y
theorem Map.congr_map {G H : SimplicialGraph.{u}} {f g : Map G H} (h : f = g)
    (x y : G.Obj) : f.map x y ≫ eqToHom (by rw [h]) = g.map x y := by
  cases h
  simp
instance : Category SimplicialGraph.{u} where
  Hom := Map
  id G := ⟨id, fun x y ↦ 𝟙 (G.Hom x y)⟩
  comp f g := ⟨g.obj ∘ f.obj, fun x y ↦ f.map x y ≫ g.map (f.obj x) (f.obj y)⟩
  id_comp f := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp
  comp_id f := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp
  assoc f g h := by
    apply Map.ext rfl
    apply heq_of_eq
    funext x y
    simp [Category.assoc]
end SimplicialGraph
namespace SimplicialCat
 def underlyingGraph (C : SimplicialCat.{u,u}) : SimplicialGraph.{u} :=
   ⟨C.Obj, fun x y ↦ (x ⟶[SSet] y)⟩
 def graphForget : SimplicialCat.{u,u} ⥤ SimplicialGraph.{u} where
   obj := underlyingGraph
   map F := ⟨F.obj, F.map⟩
 instance : graphForget.{u}.Faithful where
   map_injective := by
     intro C D F G h
     cases F
     cases G
     cases h
     rfl
end SimplicialCat
end DaggerModels

namespace DaggerModels.SimplicialColimitsFree.Paths

/-- The graph's vertex type viewed in a fixed simplicial degree. -/
def At (G : SimplicialGraph.{u}) (_n : SimplexCategoryᵒᵖ) : Type u := G.Obj

/-- The quiver of edges in simplicial degree `n`. -/
def quiverAt (G : SimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver G.Obj where
  Hom x y := (G.Hom x y).obj n

instance (G : SimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) : Quiver (At G n) :=
  quiverAt G n

/-- Actual finite composable words in the graph's degreewise edges. -/
abbrev Path (G : SimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (x y : G.Obj) : Type u :=
  @Quiver.Path (At G n) (quiverAt G n) x y

/-- An ordinary simplicial operator acting on the degreewise edge quiver. -/
def operator (G : SimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    At G m ⥤q At G n where
  obj := id
  map := fun {x y} e ↦ (G.Hom x y).map f e

/-- Apply a simplicial operator to every edge in a path. -/
def map (G : SimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    {x y : G.Obj} (p : Path G m x y) : Path G n x y := (operator G f).mapPath p

@[simp] theorem map_nil (G : SimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) (x : G.Obj) : map G f (Quiver.Path.nil : Path G m x x) = .nil := rfl

@[simp] theorem map_cons (G : SimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (e : (G.Hom y z).obj m) :
    map G f (p.cons e) = (map G f p).cons ((G.Hom y z).map f e) := rfl

@[simp] theorem map_id (G : SimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : map G (𝟙 n) p = p := by
  letI := quiverAt G n
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (map G (𝟙 n) p).cons ((G.Hom _ _).map (𝟙 n) e) = p.cons e
    rw [ih, FunctorToTypes.map_id_apply]

@[simp] theorem map_comp (G : SimplicialGraph.{u}) {l m n : SimplexCategoryᵒᵖ}
    (f : l ⟶ m) (g : m ⟶ n) {x y : G.Obj} (p : Path G l x y) :
    map G (f ≫ g) p = map G g (map G f p) := by
  letI := quiverAt G n
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (map G (f ≫ g) p).cons ((G.Hom _ _).map (f ≫ g) e) =
      (map G g (map G f p)).cons ((G.Hom _ _).map g ((G.Hom _ _).map f e))
    rw [ih, FunctorToTypes.map_comp_apply]

@[simp] theorem map_pathComp (G : SimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (q : Path G m y z) :
    map G f (p.comp q) = (map G f p).comp (map G f q) :=
  Prefunctor.mapPath_comp (operator G f) p q

/-- The simplicial set of paths from `x` to `y`. -/
def hom (G : SimplicialGraph.{u}) (x y : G.Obj) : SSet.{u} where
  obj n := Path G n x y
  map f := map G f
  map_id n := by funext p; exact map_id G n p
  map_comp f g := by funext p; exact map_comp G f g p

/-- The canonical inclusion of an edge as a singleton path. -/
def inclusion (G : SimplicialGraph.{u}) (x y : G.Obj) : G.Hom x y ⟶ hom G x y where
  app n e := @Quiver.Hom.toPath (At G n) (quiverAt G n) x y e
  naturality _ _ _ := rfl

/-- The empty path is the enriched identity. -/
def id (G : SimplicialGraph.{u}) (x : G.Obj) : 𝟙_ SSet.{u} ⟶ hom G x x where
  app _ _ := Quiver.Path.nil
  naturality _ _ _ := rfl

/-- Enriched composition concatenates two paths. -/
def comp (G : SimplicialGraph.{u}) (x y z : G.Obj) :
    hom G x y ⊗ hom G y z ⟶ hom G x z where
  app _ p := p.1.comp p.2
  naturality m n f := by
    funext p
    exact (map_pathComp G f p.1 p.2).symm

/-- The actual simplicial enrichment on the graph's vertices. -/
def enrichedCategory (G : SimplicialGraph.{u}) : EnrichedCategory SSet.{u} G.Obj where
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
def simplicialCat (G : SimplicialGraph.{u}) : SimplicialCat.{u, u} :=
  SimplicialCat.of G.Obj


end DaggerModels.SimplicialColimitsFree.Paths

namespace DaggerModels.SimplicialColimitsFree.Extension

attribute [local instance] SimplicialColimitsFree.Paths.enrichedCategory

variable (G : SimplicialGraph.{u}) {C : Type u}
  [EnrichedCategory SSet.{u} C]
  (f : G.Obj → C) (φ : ∀ x y, G.Hom x y ⟶ (f x ⟶[SSet.{u}] f y))

/-- The edge assignment in one degree, before freely composing paths. -/
def edgeMap (n : SimplexCategoryᵒᵖ) :
    SimplicialColimitsFree.Paths.At G n ⥤q SimplicialEnrichment.At C n where
  obj := f
  map {x y} e := (φ x y).app n e

/-- Freely compose an assigned path in the target degreewise category. -/
def extendAt (n : SimplexCategoryᵒᵖ) :
    Paths (SimplicialColimitsFree.Paths.At G n) ⥤ SimplicialEnrichment.At C n :=
  Paths.lift (edgeMap G f φ n)

/-- The value of the extension on an actual finite path. -/
def value (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : SimplicialColimitsFree.Paths.Path G n x y) :
    (f x ⟶[SSet.{u}] f y).obj n := (extendAt G f φ n).map p

@[simp] theorem value_nil (n : SimplexCategoryᵒᵖ) (x : G.Obj) :
    value G f φ n (Quiver.Path.nil : SimplicialColimitsFree.Paths.Path G n x x) =
      (eId SSet (f x)).app n PUnit.unit := rfl

@[simp] theorem value_cons (n : SimplexCategoryᵒᵖ) {x y z : G.Obj}
    (p : SimplicialColimitsFree.Paths.Path G n x y) (e : (G.Hom y z).obj n) :
    value G f φ n (p.cons e) =
      (eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, (φ y z).app n e) := rfl

@[simp] theorem value_comp (n : SimplexCategoryᵒᵖ) {x y z : G.Obj}
    (p : SimplicialColimitsFree.Paths.Path G n x y)
    (q : SimplicialColimitsFree.Paths.Path G n y z) :
    value G f φ n (p.comp q) =
      (eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, value G f φ n q) :=
  (extendAt G f φ n).map_comp p q

@[simp] theorem value_singleton (n : SimplexCategoryᵒᵖ) {x y : G.Obj}
    (e : (G.Hom x y).obj n) :
    value G f φ n (Quiver.Hom.toPath e) = (φ x y).app n e :=
  Paths.lift_toPath (edgeMap G f φ n) e

/-- Extension respects the same simplicial operator on every edge. -/
theorem value_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) {x y : G.Obj}
    (p : SimplicialColimitsFree.Paths.Path G n x y) :
    (f x ⟶[SSet.{u}] f y).map α (value G f φ n p) =
      value G f φ m (SimplicialColimitsFree.Paths.map G α p) := by
  induction p with
  | nil =>
    exact (congrArg (fun p ↦ p PUnit.unit) ((eId SSet (f x)).naturality α)).symm
  | @cons y z p e ih =>
    rw [SimplicialColimitsFree.Paths.map_cons, value_cons, value_cons]
    have hc := congrArg (fun h ↦ h (value G f φ n p, (φ y z).app n e))
      ((eComp SSet (f x) (f y) (f z)).naturality α)
    change (eComp SSet (f x) (f y) (f z)).app m
      ((f x ⟶[SSet.{u}] f y).map α (value G f φ n p),
        (f y ⟶[SSet.{u}] f z).map α ((φ y z).app n e)) =
      (f x ⟶[SSet.{u}] f z).map α
        ((eComp SSet (f x) (f y) (f z)).app n (value G f φ n p, (φ y z).app n e)) at hc
    rw [← hc, ih]
    have he : (f y ⟶[SSet.{u}] f z).map α ((φ y z).app n e) =
        (φ y z).app m ((G.Hom y z).map α e) :=
      (congrArg (fun h ↦ h e) ((φ y z).naturality α)).symm
    rw [he]

/-- The enriched functor obtained by freely composing the assigned edges. -/
def extend : EnrichedFunctor SSet.{u} G.Obj C where
  obj := f
  map x y :=
    { app := fun n p ↦ value G f φ n p
      naturality := fun n m α ↦ by
        funext p
        exact (value_naturality G f φ α p).symm }
  map_id x := by
    ext n e
    exact value_nil G f φ n x
  map_comp x y z := by
    ext n p
    exact value_comp G f φ n p.1 p.2

/-- On singleton edges, the extension is the specified simplicial edge map. -/
theorem inclusion_extend (x y : G.Obj) :
    SimplicialColimitsFree.Paths.inclusion G x y ≫ (extend G f φ).map x y = φ x y := by
  ext n e
  exact value_singleton G f φ n e

/-- Evaluating a path using a functor's edge restriction recovers that functor. -/
theorem value_restrict (F : EnrichedFunctor SSet.{u} G.Obj C)
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : SimplicialColimitsFree.Paths.Path G n x y) :
    value G F.obj (fun x y ↦ SimplicialColimitsFree.Paths.inclusion G x y ≫ F.map x y) n p =
      (F.map x y).app n p := by
  induction p with
  | nil =>
    exact (congrArg (fun h ↦ h.app n PUnit.unit) (F.map_id x)).symm
  | @cons y z p e ih =>
    rw [value_cons, ih]
    exact (congrArg (fun h ↦ h.app n (p, Quiver.Hom.toPath e))
      (F.map_comp x y z)).symm

/-- The extension is determined by its values on the original edges. -/
theorem extend_restrict (F : EnrichedFunctor SSet.{u} G.Obj C) :
    extend G F.obj (fun x y ↦ SimplicialColimitsFree.Paths.inclusion G x y ≫ F.map x y) = F := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro x
    rfl
  case h_map =>
    intro x y
    simp only [eqToHom_refl, Category.comp_id]
    ext n p
    exact value_restrict G F n p

end DaggerModels.SimplicialColimitsFree.Extension


namespace DaggerModels.SimplicialColimitsFree
open Extension
namespace Paths
attribute [local instance] enrichedCategory
end Paths

def unit (G : SimplicialGraph.{u}) :
    G ⟶ SimplicialCat.graphForget.obj (Paths.simplicialCat G) :=
  ⟨id, Paths.inclusion G⟩

def restrict {G : SimplicialGraph.{u}} {C : SimplicialCat.{u,u}}
    (F : Paths.simplicialCat G ⟶ C) : G ⟶ SimplicialCat.graphForget.obj C :=
  unit G ≫ SimplicialCat.graphForget.map F

def lift {G : SimplicialGraph.{u}} {C : SimplicialCat.{u,u}}
    (F : G ⟶ SimplicialCat.graphForget.obj C) : Paths.simplicialCat G ⟶ C :=
  extend G (C := C.Obj) F.obj F.map

@[simp] theorem restrict_lift {G : SimplicialGraph.{u}} {C : SimplicialCat.{u,u}}
    (F : G ⟶ SimplicialCat.graphForget.obj C) : restrict (lift F) = F := by
  apply SimplicialGraph.Map.ext (f := restrict (lift F)) (g := F) rfl
  apply heq_of_eq
  funext x y
  exact inclusion_extend G (C := C.Obj) F.obj F.map x y

@[simp] theorem lift_restrict {G : SimplicialGraph.{u}} {C : SimplicialCat.{u,u}}
    (F : Paths.simplicialCat G ⟶ C) : lift (restrict F) = F :=
  extend_restrict G F

def homEquiv (G : SimplicialGraph.{u}) (C : SimplicialCat.{u,u}) :
    (Paths.simplicialCat G ⟶ C) ≃ (G ⟶ SimplicialCat.graphForget.obj C) where
  toFun := restrict
  invFun := lift
  left_inv := lift_restrict
  right_inv := restrict_lift
end DaggerModels.SimplicialColimitsFree
