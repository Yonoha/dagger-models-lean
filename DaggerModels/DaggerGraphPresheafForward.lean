import DaggerModels.DaggerGraphIndex
import DaggerModels.DaggerGraphTotalSpace

/-!
# From dagger simplicial graphs to index presheaves

The vertex value and total edge spaces define an actual functor. The index
involution acts by the original graph dagger, with ordinary simplex operators.
-/

open CategoryTheory Opposite

universe u

namespace DaggerModels.DaggerGraphPresheaf

open DaggerGraphIndex
open DaggerSimplicialGraph.TotalSpace

def value (G : DaggerSimplicialGraph.{u}) : Obj → Type u
  | .vertex => G.Obj
  | .edge n => (edges G).obj (op n)

def edgePull (G : DaggerSimplicialGraph.{u}) {n m : SimplexCategory} (α : n ⟶ m)
    (b : Bool) (e : (edges G).obj (op m)) : (edges G).obj (op n) :=
  if b then (dagger G).app (op n) ((edges G).map α.op e) else (edges G).map α.op e

def pull (G : DaggerSimplicialGraph.{u}) {X Y : Obj} (f : X ⟶ Y) : value G Y → value G X :=
  match X, Y, f with
  | .vertex, .vertex, _ => id
  | .vertex, .edge _, b => fun e ↦ if (show Bool from b) then e.2.1 else e.1
  | .edge _, .vertex, f => nomatch f
  | .edge _, .edge _, (α, b) => edgePull G α b

lemma map_dagger (G : DaggerSimplicialGraph.{u}) {n m : SimplexCategoryᵒᵖ}
    (α : n ⟶ m) (e : (edges G).obj n) :
    (edges G).map α ((dagger G).app n e) =
      (dagger G).app m ((edges G).map α e) :=
  (congrFun ((dagger G).naturality α) e).symm

@[simp] lemma dagger_dagger (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : (edges G).obj n) :
    (dagger G).app n ((dagger G).app n e) = e :=
  congrArg (fun k ↦ k.app n e) (dagger_involutive G)

lemma pull_identity (G : DaggerSimplicialGraph.{u}) (X : Obj) (e : value G X) :
    pull G (𝟙 X) e = e := by
  cases X with
  | vertex => rfl
  | edge n =>
    change edgePull G (𝟙 n) false e = e
    simp [edgePull]

lemma pull_comp (G : DaggerSimplicialGraph.{u}) {X Y Z : Obj} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : value G Z) : pull G (f ≫ g) e = pull G f (pull G g e) := by
  change pull G (DaggerGraphIndex.compose f g) e = _
  cases X <;> cases Y <;> cases Z
  all_goals cases f <;> cases g
  all_goals try casesm* Bool
  all_goals simp [pull, DaggerGraphIndex.compose, edgePull, map_dagger]
  all_goals simp [dagger, edges]

def presheaf (G : DaggerSimplicialGraph.{u}) : Objᵒᵖ ⥤ Type u where
  obj X := value G X.unop
  map f := pull G f.unop
  map_id X := by funext e; exact pull_identity G X.unop e
  map_comp f g := by funext e; exact pull_comp G g.unop f.unop e

def valueMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (X : Obj) :
    value G X → value H X :=
  match X with
  | .vertex => k.obj
  | .edge n => (edgeMap k).app (op n)

lemma edgeMap_pull {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    {n m : SimplexCategory} (α : n ⟶ m) (e : (edges G).obj (op m)) :
    (edgeMap k).app (op n) ((edges G).map α.op e) =
      (edges H).map α.op ((edgeMap k).app (op m) e) :=
  congrFun ((edgeMap k).naturality α.op) e

lemma edgeMap_dagger {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (e : (edges G).obj n) :
    (edgeMap k).app n ((dagger G).app n e) =
      (dagger H).app n ((edgeMap k).app n e) :=
  (congrArg (fun p ↦ p.app n e) (daggerNatural.naturality k)).symm

lemma valueMap_pull {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    {X Y : Obj} (f : X ⟶ Y) (e : value G Y) :
    valueMap k X (pull G f e) = pull H f (valueMap k Y e) := by
  cases X <;> cases Y
  all_goals cases f
  all_goals try casesm* Bool
  all_goals simp [valueMap, pull, edgePull, edgeMap_pull, edgeMap_dagger]
  all_goals simp [edgeMap]

def presheafMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) :
    presheaf G ⟶ presheaf H where
  app X := valueMap k X.unop
  naturality {X Y} f := by funext e; exact valueMap_pull k f.unop e

/-- Total edges and endpoints give an actual functor, at every value universe. -/
def functor : DaggerSimplicialGraph.{u} ⥤ (Objᵒᵖ ⥤ Type u) where
  obj := presheaf
  map := presheafMap
  map_id G := by
    ext X e
    cases X using Opposite.rec
    rename_i X
    cases X <;> rfl
  map_comp k l := by
    ext X e
    cases X using Opposite.rec
    rename_i X
    cases X <;> rfl


end DaggerModels.DaggerGraphPresheaf
