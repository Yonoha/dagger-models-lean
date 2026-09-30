import DaggerModels.DaggerSimplicialGraph

/-!
# Total edge spaces of dagger simplicial graphs

The total space records both endpoints and the original edge simplex. Its
ordinary simplicial operators preserve endpoints, and dagger exchanges them.
-/

open CategoryTheory

universe u

namespace DaggerModels.DaggerSimplicialGraph.TotalSpace

/-- All edges in each simplicial degree, including their source and target labels. -/
def edges (G : DaggerSimplicialGraph.{u}) : SSet.{u} where
  obj n := Σ x : G.Obj, Σ y : G.Obj, (G.Hom x y).obj n
  map α e := ⟨e.1, e.2.1, (G.Hom e.1 e.2.1).map α e.2.2⟩
  map_id n := by
    funext e
    rcases e with ⟨x, y, e⟩
    simp
  map_comp α β := by
    funext e
    rcases e with ⟨x, y, e⟩
    simp

/-- A graph map acts on both endpoint labels and the actual edge simplex. -/
def edgeMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) : edges G ⟶ edges H where
  app n e := ⟨k.obj e.1, k.obj e.2.1, (k.map e.1 e.2.1).app n e.2.2⟩
  naturality {n m} α := by
    funext e
    rcases e with ⟨x, y, e⟩
    exact congrArg (fun a ↦ (⟨k.obj x, k.obj y, a⟩ : (edges H).obj m))
      (congrFun ((k.map x y).naturality α) e)

/-- Total edges form an actual simplicial-set valued functor on dagger graphs. -/
def edgeFunctor : DaggerSimplicialGraph.{u} ⥤ SSet.{u} where
  obj := edges
  map := edgeMap

/-- The object labels, regarded as a constant simplicial set. -/
def vertices (G : DaggerSimplicialGraph.{u}) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj G.Obj

def vertexMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) : vertices G ⟶ vertices H :=
  (Functor.const SimplexCategoryᵒᵖ).map k.obj

def vertexFunctor : DaggerSimplicialGraph.{u} ⥤ SSet.{u} where
  obj := vertices
  map := vertexMap

/-- The source endpoint, in all simplicial degrees. -/
def source (G : DaggerSimplicialGraph.{u}) : edges G ⟶ vertices G where
  app _ e := e.1

/-- The target endpoint, in all simplicial degrees. -/
def target (G : DaggerSimplicialGraph.{u}) : edges G ⟶ vertices G where
  app _ e := e.2.1

def sourceNatural : edgeFunctor.{u} ⟶ vertexFunctor where
  app := source

def targetNatural : edgeFunctor.{u} ⟶ vertexFunctor where
  app := target

/-- Dagger on total edges exchanges endpoints and uses the original graph dagger. -/
def dagger (G : DaggerSimplicialGraph.{u}) : edges G ⟶ edges G where
  app n e := ⟨e.2.1, e.1, (G.dagger e.1 e.2.1).app n e.2.2⟩
  naturality {n m} α := by
    funext e
    rcases e with ⟨x, y, e⟩
    exact congrArg (fun a ↦ (⟨y, x, a⟩ : (edges G).obj m))
      (congrFun ((G.dagger x y).naturality α) e)

@[simp] theorem dagger_involutive (G : DaggerSimplicialGraph.{u}) :
    dagger G ≫ dagger G = 𝟙 (edges G) := by
  ext n e
  rcases e with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨x, y, a⟩ : (edges G).obj n))
    (dagger_app_involutive G x y n e)

@[simp] theorem dagger_source (G : DaggerSimplicialGraph.{u}) :
    dagger G ≫ source G = target G := rfl

@[simp] theorem dagger_target (G : DaggerSimplicialGraph.{u}) :
    dagger G ≫ target G = source G := rfl

/-- Graph maps intertwine the involution on the same simplex degree. -/
def daggerNatural : edgeFunctor.{u} ⟶ edgeFunctor where
  app := dagger
  naturality {G H} k := by
    ext n e
    rcases e with ⟨x, y, e⟩
    exact congrArg (fun a ↦ (⟨k.obj y, k.obj x, a⟩ : (edges H).obj n))
      (congrArg (fun p ↦ p.app n e) (k.map_dagger x y))

/-- Recover the original typed edge space as the exact fiber of both endpoint maps. -/
def fiberEquiv (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) (n : SimplexCategoryᵒᵖ) :
    {e : (edges G).obj n // e.1 = x ∧ e.2.1 = y} ≃ (G.Hom x y).obj n where
  toFun e := Eq.mp (congrArg₂ (fun x y ↦ (G.Hom x y).obj n) e.2.1 e.2.2) e.1.2.2
  invFun e := ⟨⟨x, y, e⟩, rfl, rfl⟩
  left_inv e := by
    rcases e with ⟨⟨x', y', e⟩, hx, hy⟩
    dsimp only at hx hy
    subst hx
    subst hy
    rfl
  right_inv e := rfl

theorem fiberEquiv_naturality (G : DaggerSimplicialGraph.{u}) (x y : G.Obj)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (e : {e : (edges G).obj n // e.1 = x ∧ e.2.1 = y}) :
    fiberEquiv G x y m ⟨(edges G).map α e.1, e.2⟩ =
      (G.Hom x y).map α (fiberEquiv G x y n e) := by
  rcases e with ⟨⟨x', y', e⟩, hx, hy⟩
  dsimp only at hx hy
  subst hx
  subst hy
  rfl

end DaggerModels.DaggerSimplicialGraph.TotalSpace
