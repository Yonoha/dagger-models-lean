import DaggerModels.SimplicialColimitsFree

/-!
# Total simplicial edges of an ordinary simplicial graph

Both endpoints are retained in the total edge space.  The original Hom is
recovered as the fiber of the two endpoint maps.
-/

open CategoryTheory

universe u

namespace DaggerModels.SimplicialGraph.TotalSpace

/-- All edges in each simplicial degree, with both original endpoints. -/
def edges (G : SimplicialGraph.{u}) : SSet.{u} where
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

/-- A graph map acts on both endpoint labels and the original edge. -/
def edgeMap {G H : SimplicialGraph.{u}} (k : G ⟶ H) : edges G ⟶ edges H where
  app n e := ⟨k.obj e.1, k.obj e.2.1, (k.map e.1 e.2.1).app n e.2.2⟩
  naturality {n m} α := by
    funext e
    rcases e with ⟨x, y, e⟩
    exact congrArg (fun a ↦ (⟨k.obj x, k.obj y, a⟩ : (edges H).obj m))
      (congrFun ((k.map x y).naturality α) e)

/-- Total edges form a simplicial-set valued functor on ordinary graphs. -/
def edgeFunctor : SimplicialGraph.{u} ⥤ SSet.{u} where
  obj := edges
  map := edgeMap

/-- Object labels as a constant simplicial set. -/
def vertices (G : SimplicialGraph.{u}) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj G.Obj

/-- A graph map induces the constant simplicial-set map on vertices. -/
def vertexMap {G H : SimplicialGraph.{u}} (k : G ⟶ H) : vertices G ⟶ vertices H :=
  (Functor.const SimplexCategoryᵒᵖ).map k.obj

/-- Vertices form a constant simplicial-set valued functor. -/
def vertexFunctor : SimplicialGraph.{u} ⥤ SSet.{u} where
  obj := vertices
  map := vertexMap

/-- Source endpoint of a total edge. -/
def source (G : SimplicialGraph.{u}) : edges G ⟶ vertices G where
  app _ e := e.1

/-- Target endpoint of a total edge. -/
def target (G : SimplicialGraph.{u}) : edges G ⟶ vertices G where
  app _ e := e.2.1

/-- The source is natural in graph maps. -/
def sourceNatural : edgeFunctor.{u} ⟶ vertexFunctor where
  app := source

/-- The target is natural in graph maps. -/
def targetNatural : edgeFunctor.{u} ⟶ vertexFunctor where
  app := target

/-- Recover the original Hom degree as the exact endpoint fiber. -/
def fiberEquiv (G : SimplicialGraph.{u}) (x y : G.Obj) (n : SimplexCategoryᵒᵖ) :
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

theorem fiberEquiv_naturality (G : SimplicialGraph.{u}) (x y : G.Obj)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (e : {e : (edges G).obj n // e.1 = x ∧ e.2.1 = y}) :
    fiberEquiv G x y m ⟨(edges G).map α e.1, e.2⟩ =
      (G.Hom x y).map α (fiberEquiv G x y n e) := by
  rcases e with ⟨⟨x', y', e⟩, hx, hy⟩
  dsimp only at hx hy
  subst hx
  subst hy
  rfl

end DaggerModels.SimplicialGraph.TotalSpace
