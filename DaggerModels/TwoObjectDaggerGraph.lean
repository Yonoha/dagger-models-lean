import DaggerModels.DaggerSimplicialGraph

/-!
The actual two-object dagger graph of Part I `bg.not.cells` and its graph-level universal
property in `bg.eq.A-univ`. Objects and edge spaces share the arbitrary small universe `u`.
The two target objects may coincide. No finite presentability claim is made here.
-/

open CategoryTheory Opposite

universe u

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

theorem emptyMap_unique {K : SSet.{u}} (f : empty ⟶ K) : f = emptyMap K := by
  ext n x
  exact x.elim

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

variable {K : SSet.{u}} {G : DaggerSimplicialGraph.{u}}

/-- Read the ordered pair of object images and the forward edge map. -/
def classify (f : graph K ⟶ G) : Σ x : G.Obj, Σ y : G.Obj, (K ⟶ G.Hom x y) :=
  ⟨f.obj left, f.obj right, f.map left right⟩

/-- A forward edge map determines the reverse edge map by target dagger. -/
def fromData (x y : G.Obj) (f : K ⟶ G.Hom x y) : graph K ⟶ G where
  obj
    | ⟨false⟩ => x
    | ⟨true⟩ => y
  map
    | ⟨false⟩, ⟨false⟩ => emptyMap (G.Hom x x)
    | ⟨false⟩, ⟨true⟩ => f
    | ⟨true⟩, ⟨false⟩ => f ≫ G.dagger x y
    | ⟨true⟩, ⟨true⟩ => emptyMap (G.Hom y y)
  map_dagger a b := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    cases a <;> cases b
    · simpa only [Category.id_comp] using
        emptyMap_unique (emptyMap (G.Hom x x) ≫ G.dagger x x)
    · simp [graph]
    · simp [graph, Category.assoc, G.dagger_involutive]
    · simpa only [Category.id_comp] using
        emptyMap_unique (emptyMap (G.Hom y y) ≫ G.dagger y y)

@[simp]
theorem classify_fromData (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    classify (fromData x y f) = ⟨x, y, f⟩ := rfl

/-- Every actual graph map is determined by its object images and forward edge map. -/
@[simp]
theorem fromData_classify (f : graph K ⟶ G) :
    fromData (f.obj left) (f.obj right) (f.map left right) = f := by
  apply DaggerSimplicialGraph.Map.ext
  · funext a
    rcases a with ⟨a⟩
    cases a <;> rfl
  · apply Function.hfunext rfl
    intro a a' ha
    obtain rfl := eq_of_heq ha
    apply Function.hfunext rfl
    intro b b' hb
    obtain rfl := eq_of_heq hb
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    cases a <;> cases b <;> apply heq_of_eq
    · exact (emptyMap_unique (f.map left left)).symm
    · rfl
    · simpa only [Category.id_comp] using f.map_dagger left right
    · exact (emptyMap_unique (f.map right right)).symm

/-- The graph-level factor of the exact two-object cell universal property. -/
def homEquiv (K : SSet.{u}) (G : DaggerSimplicialGraph.{u}) :
    (graph K ⟶ G) ≃ (Σ x : G.Obj, Σ y : G.Obj, (K ⟶ G.Hom x y)) where
  toFun := classify
  invFun p := fromData p.1 p.2.1 p.2.2
  left_inv := fromData_classify
  right_inv p := by rcases p with ⟨x, y, f⟩; rfl

@[simp]
theorem graph_hom_left_right (K : SSet.{u}) : (graph K).Hom left right = K := rfl

@[simp]
theorem graph_hom_right_left (K : SSet.{u}) : (graph K).Hom right left = K := rfl

@[simp]
theorem graph_hom_left_left (K : SSet.{u}) : (graph K).Hom left left = empty := rfl

@[simp]
theorem graph_hom_right_right (K : SSet.{u}) : (graph K).Hom right right = empty := rfl

@[simp]
theorem graph_dagger_left_right (K : SSet.{u}) :
    (graph K).dagger left right = 𝟙 K := rfl

@[simp]
theorem graph_dagger_right_left (K : SSet.{u}) :
    (graph K).dagger right left = 𝟙 K := rfl

@[simp]
theorem fromData_obj_left (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    (fromData x y f).obj left = x := rfl

@[simp]
theorem fromData_obj_right (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    (fromData x y f).obj right = y := rfl

@[simp]
theorem fromData_map_left_right (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    (fromData x y f).map left right = f := rfl

@[simp]
theorem fromData_map_right_left (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    (fromData x y f).map right left = f ≫ G.dagger x y := rfl

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

/-- Contravariant naturality in the actual generating simplicial set. -/
theorem homEquiv_naturality_left {K L : SSet.{u}} (φ : K ⟶ L) (f : graph L ⟶ G) :
    homEquiv K G (functor.map φ ≫ f) =
      ⟨f.obj left, f.obj right, φ ≫ f.map left right⟩ := rfl

/-- Postcomposition acts on both target objects and the specified full edge map. -/
def postData {G H : DaggerSimplicialGraph.{u}} (p : G ⟶ H)
    (q : Σ x : G.Obj, Σ y : G.Obj, (K ⟶ G.Hom x y)) :
    Σ x : H.Obj, Σ y : H.Obj, (K ⟶ H.Hom x y) :=
  ⟨p.obj q.1, p.obj q.2.1, q.2.2 ≫ p.map q.1 q.2.1⟩

/-- Covariant naturality for arbitrary target graph maps and arbitrary object maps. -/
theorem homEquiv_naturality_right {G H : DaggerSimplicialGraph.{u}}
    (f : graph K ⟶ G) (p : G ⟶ H) :
    homEquiv K H (f ≫ p) = postData p (homEquiv K G f) := rfl

/-- The inverse classification also commutes with source simplicial maps. -/
theorem fromData_naturality_left {K L : SSet.{u}} (φ : K ⟶ L)
    (x y : G.Obj) (f : L ⟶ G.Hom x y) :
    fromData x y (φ ≫ f) = functor.map φ ≫ fromData x y f := by
  apply (homEquiv K G).injective
  rfl

/-- The inverse classification also commutes with arbitrary target object maps. -/
theorem fromData_naturality_right {G H : DaggerSimplicialGraph.{u}} (p : G ⟶ H)
    (x y : G.Obj) (f : K ⟶ G.Hom x y) :
    fromData (p.obj x) (p.obj y) (f ≫ p.map x y) = fromData x y f ≫ p := by
  apply (homEquiv K H).injective
  rfl

end DaggerModels.TwoObjectDaggerGraph
