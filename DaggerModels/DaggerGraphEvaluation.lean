import DaggerModels.DaggerGraphPresentable
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Vertex and total-edge evaluations of dagger simplicial graphs

These are the actual graph evaluations. Their preservation of small limits and
colimits follows from the proved presheaf equivalence.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.DaggerGraphEvaluation

/-- The original vertex set, including the original vertex maps. -/
def vertices : DaggerSimplicialGraph.{u} ⥤ Type u where
  obj G := G.Obj
  map k := k.obj

/-- All original edge simplices in a degree, with both endpoint labels. -/
def edges (n : SimplexCategoryᵒᵖ) : DaggerSimplicialGraph.{u} ⥤ Type u where
  obj G := (DaggerSimplicialGraph.TotalSpace.edges G).obj n
  map k := (DaggerSimplicialGraph.TotalSpace.edgeMap k).app n

def verticesIso : vertices.{u} ≅ daggerGraphEquivalencePresheaf.functor ⋙
    (evaluation DaggerGraphIndex.Objᵒᵖ (Type u)).obj (op .vertex) := Iso.refl _

def edgesIso (n : SimplexCategoryᵒᵖ) : edges.{u} n ≅
    daggerGraphEquivalencePresheaf.functor ⋙
      (evaluation DaggerGraphIndex.Objᵒᵖ (Type u)).obj (op (.edge n.unop)) := Iso.refl _

theorem vertices_preservesLimits : PreservesLimitsOfSize.{u, u} vertices.{u} :=
  preservesLimits_of_natIso verticesIso.symm

theorem vertices_preservesColimits : PreservesColimitsOfSize.{u, u} vertices.{u} :=
  preservesColimits_of_natIso verticesIso.symm

theorem edges_preservesLimits (n : SimplexCategoryᵒᵖ) :
    PreservesLimitsOfSize.{u, u} (edges.{u} n) :=
  preservesLimits_of_natIso (edgesIso n).symm

theorem edges_preservesColimits (n : SimplexCategoryᵒᵖ) :
    PreservesColimitsOfSize.{u, u} (edges.{u} n) :=
  preservesColimits_of_natIso (edgesIso n).symm

def source (n : SimplexCategoryᵒᵖ) : edges.{u} n ⟶ vertices where
  app _ e := e.1

def target (n : SimplexCategoryᵒᵖ) : edges.{u} n ⟶ vertices where
  app _ e := e.2.1

end DaggerModels.DaggerGraphEvaluation
