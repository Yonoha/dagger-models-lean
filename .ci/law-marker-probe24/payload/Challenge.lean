import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
Uncompiled source-only original-public carrier/graph/path marker proposal.
Only named proposition proofs are replaced; all data and inline laws are copied.
Every placeholder needs explicit configuration and a clean candidate proof.
Cell/adjunction/walking closure and the full23 comparisons are still separate.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Limits Opposite Simplicial
universe o v u
namespace DaggerModels

structure SimplicialCat where
  Obj : Type o
  enriched : EnrichedCategory SSet.{v} Obj
attribute [instance] SimplicialCat.enriched

namespace SimplicialCat

/-- Bundle an existing simplicial enrichment, with the original public name. -/
def of (C : Type o) [EnrichedCategory SSet.{v} C] : SimplicialCat.{o, v} :=
  ⟨C, inferInstance⟩

end SimplicialCat

noncomputable instance sSetBraidedCategory : BraidedCategory SSet.{v} :=
  .ofCartesianMonoidalCategory

class DaggerSimplicialStructure (C : Type o) [EnrichedCategory SSet.{v} C] where
  dagger (X Y : C) : (X ⟶[SSet.{v}] Y) ⟶ (Y ⟶[SSet.{v}] X)
  dagger_involutive (X Y : C) : dagger X Y ≫ dagger Y X = 𝟙 _
  dagger_id (X : C) : eId SSet X ≫ dagger X X = eId SSet X
  dagger_comp (X Y Z : C) :
    eComp SSet X Y Z ≫ dagger X Z =
      (dagger X Y ⊗ₘ dagger Y Z) ≫
        (β_ (Y ⟶[SSet.{v}] X) (Z ⟶[SSet.{v}] Y)).hom ≫ eComp SSet Z Y X

structure DaggerSimplicialCat where
  toSimplicialCat : SimplicialCat.{o, v}
  daggerStructure : DaggerSimplicialStructure toSimplicialCat.Obj
namespace DaggerSimplicialCat
abbrev Obj (C : DaggerSimplicialCat.{o, v}) := C.toSimplicialCat.Obj
instance : CoeSort (DaggerSimplicialCat.{o, v}) (Type o) := ⟨Obj⟩
instance enriched (C : DaggerSimplicialCat.{o, v}) : EnrichedCategory SSet.{v} C.Obj :=
  C.toSimplicialCat.enriched
instance daggerStructureInstance (C : DaggerSimplicialCat.{o, v}) :
    DaggerSimplicialStructure C.Obj := C.daggerStructure

structure Hom (C D : DaggerSimplicialCat.{o, v}) extends
    EnrichedFunctor SSet.{v} C.Obj D.Obj where
  map_dagger (X Y : C.Obj) :
    map X Y ≫ DaggerSimplicialStructure.dagger (obj X) (obj Y) =
      DaggerSimplicialStructure.dagger X Y ≫ map Y X
@[ext]
theorem Hom.ext {C D : DaggerSimplicialCat.{o, v}} {F G : Hom C D}
    (h : F.toEnrichedFunctor = G.toEnrichedFunctor) : F = G := by sorry
def Hom.id (C : DaggerSimplicialCat.{o, v}) : Hom C C where
  toEnrichedFunctor := EnrichedFunctor.id SSet C.Obj
  map_dagger X Y := by simp
def Hom.comp {C D E : DaggerSimplicialCat.{o, v}} (F : Hom C D) (G : Hom D E) :
    Hom C E where
  toEnrichedFunctor := F.toEnrichedFunctor.comp SSet G.toEnrichedFunctor
  map_dagger X Y := by
    dsimp
    rw [Category.assoc, G.map_dagger, ← Category.assoc, F.map_dagger, Category.assoc]
instance : Category DaggerSimplicialCat.{o, v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  comp_id F := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.id, Hom.comp, EnrichedFunctor.id, EnrichedFunctor.comp]
  assoc F G H := by
    apply Hom.ext
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp [Hom.comp, EnrichedFunctor.comp, Category.assoc]

end DaggerSimplicialCat

end DaggerModels

namespace DaggerModels

/-- A small simplicial graph with an involution exchanging edge endpoints. -/
structure DaggerSimplicialGraph where
  Obj : Type u
  Hom : Obj → Obj → SSet.{u}
  dagger : ∀ x y, Hom x y ⟶ Hom y x
  dagger_involutive : ∀ x y, dagger x y ≫ dagger y x = 𝟙 (Hom x y)

namespace DaggerSimplicialGraph

/-- A map of dagger simplicial graphs. -/
structure Map (G H : DaggerSimplicialGraph.{u}) where
  obj : G.Obj → H.Obj
  map : ∀ x y, G.Hom x y ⟶ H.Hom (obj x) (obj y)
  map_dagger : ∀ x y, map x y ≫ H.dagger (obj x) (obj y) = G.dagger x y ≫ map y x

@[ext] theorem Map.ext {G H : DaggerSimplicialGraph.{u}} {f g : Map G H}
    (hobj : f.obj = g.obj) (hmap : HEq f.map g.map) : f = g := by sorry

instance : Category (DaggerSimplicialGraph.{u}) where
  Hom := Map
  id G :=
    { obj := id
      map := fun x y ↦ 𝟙 (G.Hom x y)
      map_dagger := fun x y ↦ by simp }
  comp f g :=
    { obj := g.obj ∘ f.obj
      map := fun x y ↦ f.map x y ≫ g.map (f.obj x) (f.obj y)
      map_dagger := fun x y ↦ by
        dsimp only [Function.comp_apply]
        rw [Category.assoc, g.map_dagger, ← Category.assoc, f.map_dagger,
          Category.assoc] }
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

@[simp] theorem id_obj (G : DaggerSimplicialGraph.{u}) : (𝟙 G : G ⟶ G).obj = id := by sorry

@[simp] theorem id_map (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    (𝟙 G : G ⟶ G).map x y = 𝟙 (G.Hom x y) := by sorry

@[simp] theorem comp_obj {G H K : DaggerSimplicialGraph.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).obj = g.obj ∘ f.obj := by sorry

@[simp] theorem comp_map {G H K : DaggerSimplicialGraph.{u}} (f : G ⟶ H) (g : H ⟶ K)
    (x y : G.Obj) : (f ≫ g).map x y = f.map x y ≫ g.map (f.obj x) (f.obj y) := by sorry

@[simp] theorem dagger_app_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    (n : SimplexCategoryᵒᵖ) (e : (G.Hom x y).obj n) :
    (G.dagger y x).app n ((G.dagger x y).app n e) = e := by sorry

end DaggerSimplicialGraph
end DaggerModels

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
    (f : m ⟶ n) (x : G.Obj) : map G f (Quiver.Path.nil : Path G m x x) = .nil := by sorry

@[simp] theorem map_cons (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (e : (G.Hom y z).obj m) :
    map G f (p.cons e) = (map G f p).cons ((G.Hom y z).map f e) := by sorry

@[simp] theorem map_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : G.Obj} (p : Path G n x y) : map G (𝟙 n) p = p := by sorry

@[simp] theorem map_comp (G : DaggerSimplicialGraph.{u}) {l m n : SimplexCategoryᵒᵖ}
    (f : l ⟶ m) (g : m ⟶ n) {x y : G.Obj} (p : Path G l x y) :
    map G (f ≫ g) p = map G g (map G f p) := by sorry

@[simp] theorem map_pathComp (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) {x y z : G.Obj} (p : Path G m x y) (q : Path G m y z) :
    map G f (p.comp q) = (map G f p).comp (map G f q) := by sorry

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
    (x : G.Obj) : reverse G n (Quiver.Path.nil : Path G n x x) = .nil := by sorry

@[simp] theorem reverse_cons (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y z : G.Obj} (p : Path G n x y) (e : (G.Hom y z).obj n) :
    reverse G n (p.cons e) =
      (@Quiver.Hom.toPath (At G n) (quiverAt G n) z y ((G.dagger y z).app n e)).comp
        (reverse G n p) := by sorry

@[simp] theorem reverse_comp (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y z : G.Obj} (p : Path G n x y) (q : Path G n y z) :
    reverse G n (p.comp q) = (reverse G n q).comp (reverse G n p) := by sorry

@[simp] theorem reverse_involutive (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : Path G n x y) :
    reverse G n (reverse G n p) = p := by sorry

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
    map G f (reverse G m p) = reverse G n (map G f p) := by sorry

/-- The path dagger is an ordinary simplicial map. -/
def dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : hom G x y ⟶ hom G y x where
  app n := reverse G n
  naturality m n f := by
    funext p
    exact (map_reverse G f p).symm

@[simp] theorem dagger_involutive (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    dagger G x y ≫ dagger G y x = 𝟙 (hom G x y) := by sorry

@[simp] theorem inclusion_dagger (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) :
    inclusion G x y ≫ dagger G x y = G.dagger x y ≫ inclusion G y x := by sorry

@[simp] theorem id_dagger (G : DaggerSimplicialGraph.{u}) (x : G.Obj) :
    id G x ≫ dagger G x x = id G x := by sorry

/-- Dagger reverses the order of the enriched composition factors. -/
theorem comp_dagger (G : DaggerSimplicialGraph.{u}) (x y z : G.Obj) :
    comp G x y z ≫ dagger G x z =
      (dagger G x y ⊗ₘ dagger G y z) ≫
        (β_ (hom G y x) (hom G z y)).hom ≫ comp G z y x := by sorry

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

namespace DaggerModels.TwoObjectDaggerGraph

/-- Universe-sized names for the two vertices. -/
abbrev Vertex := ULift.{u} Bool

def left : Vertex.{u} := ⟨false⟩
def right : Vertex.{u} := ⟨true⟩

/-- The degreewise empty simplicial set, with ordinary simplicial operators. -/
def empty : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

/-- There is exactly one simplicial map from the degreewise empty simplicial set. -/
def emptyMap (K : SSet.{u}) : empty ⟶ K where
  app _ := PEmpty.elim
  naturality {X Y} α := by
    ext x
    exact x.elim

theorem emptyMap_unique {K : SSet.{u}} (f : empty ⟶ K) : f = emptyMap K := by sorry

/-- Two literal copies of `K`, with both diagonal edge spaces empty. -/
def hom (K : SSet.{u}) : Vertex.{u} → Vertex.{u} → SSet.{u}
  | ⟨false⟩, ⟨false⟩ => empty
  | ⟨false⟩, ⟨true⟩ => K
  | ⟨true⟩, ⟨false⟩ => K
  | ⟨true⟩, ⟨true⟩ => empty

/-- The manuscript's two-object graph, with dagger identifying the two copies. -/
def graph (K : SSet.{u}) : DaggerSimplicialGraph.{u} where
  Obj := Vertex
  Hom := hom K
  dagger
    | ⟨false⟩, ⟨false⟩ => 𝟙 _
    | ⟨false⟩, ⟨true⟩ => 𝟙 _
    | ⟨true⟩, ⟨false⟩ => 𝟙 _
    | ⟨true⟩, ⟨true⟩ => 𝟙 _
  dagger_involutive x y := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y <;> simp

/-- A simplicial map acts on both copies, while the vertex map is the identity. -/
def map {K L : SSet.{u}} (φ : K ⟶ L) : graph K ⟶ graph L where
  obj := id
  map
    | ⟨false⟩, ⟨false⟩ => 𝟙 _
    | ⟨false⟩, ⟨true⟩ => φ
    | ⟨true⟩, ⟨false⟩ => φ
    | ⟨true⟩, ⟨true⟩ => 𝟙 _
  map_dagger a b := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    cases a <;> cases b <;> simp [graph]

/-- The actual two-object construction is a functor on all simplicial sets in `Type u`. -/
def functor : SSet.{u} ⥤ DaggerSimplicialGraph.{u} where
  obj := graph
  map := map
  map_id K := by
    apply DaggerSimplicialGraph.Map.ext
    case hobj => rfl
    case hmap =>
      apply heq_of_eq
      funext a b
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      cases a <;> cases b <;> rfl
  map_comp φ ψ := by
    apply DaggerSimplicialGraph.Map.ext
    case hobj => rfl
    case hmap =>
      apply heq_of_eq
      funext a b
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      cases a <;> cases b <;> simp [map]

end DaggerModels.TwoObjectDaggerGraph

namespace DaggerModels.FreeSimplicialPaths
example (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (x y : G.Obj) :
    (hom G x y).obj n ≃ Path G n x y := homObjEquiv G x y n
example (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    {x y z : G.Obj} (p : Path G m x y) (q : Path G m y z) :
    map G f (p.comp q) = (map G f p).comp (map G f q) := map_pathComp G f p q
example (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) {x y z : G.Obj}
    (p : Path G n x y) (q : Path G n y z) :
    reverse G n (p.comp q) = (reverse G n q).comp (reverse G n p) := reverse_comp G n p q
example (G : DaggerSimplicialGraph.{u}) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    {x y : G.Obj} (p : Path G m x y) :
    map G f (reverse G m p) = reverse G n (map G f p) := map_reverse G f p
end DaggerModels.FreeSimplicialPaths

namespace DaggerModels.LawMarkerPathExample

noncomputable section

open FreeSimplicialPaths

/-- Only equalities of the three already visible raw path operations. -/
theorem enrichment_laws (G : DaggerSimplicialGraph.{u}) :
    (∀ x y : G.Obj,
      (λ_ (hom G x y)).inv ≫ FreeSimplicialPaths.id G x ▷ _ ≫ comp G x x y = 𝟙 _) ∧
    (∀ x y : G.Obj,
      (ρ_ (hom G x y)).inv ≫ _ ◁ FreeSimplicialPaths.id G y ≫ comp G x y y = 𝟙 _) ∧
    (∀ w x y z : G.Obj,
      (α_ (hom G w x) (hom G x y) (hom G y z)).inv ≫
        comp G w x y ▷ _ ≫ comp G w y z = _ ◁ comp G x y z ≫ comp G w x z) := by
  sorry

/-- The same Hom, empty-path identity and concatenation, with named law wiring. -/
def enrichment (G : DaggerSimplicialGraph.{u}) : EnrichedCategory SSet.{u} G.Obj where
  Hom := hom G
  id := FreeSimplicialPaths.id G
  comp := comp G
  id_comp x y := (enrichment_laws G).1 x y
  comp_id x y := (enrichment_laws G).2.1 x y
  assoc w x y z := (enrichment_laws G).2.2 w x y z

/-- Same literal record type; this does not identify different nominal carriers. -/
theorem enrichment_eq (G : DaggerSimplicialGraph.{u}) :
    enrichment G = FreeSimplicialPaths.enrichedCategory G := by
  rfl

end
end DaggerModels.LawMarkerPathExample
