import DaggerModels.TwoObjectDaggerGraph
import DaggerModels.FreeSimplicialMap

/-! The actual free two-object cells of Part I `bg.not.cells`, and both factors
of `bg.eq.A-univ`. The two objects may have the same image in any target. -/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.TwoObjectDaggerCell

noncomputable section

/-- The manuscript's cell is the original finite-path free category on `G_K`. -/
def cell (K : SSet.{u}) : DaggerSimplicialCat.{u, u} :=
  FreeDaggerSimplicialCategory.functor.obj (TwoObjectDaggerGraph.graph K)

/-- Simplicial maps act on the actual two-object free cells. -/
def functor : SSet.{u} ⥤ DaggerSimplicialCat.{u, u} :=
  TwoObjectDaggerGraph.functor ⋙ FreeDaggerSimplicialCategory.functor

/-- The generating forward edge, inserted as a singleton path. -/
def generator (K : SSet.{u}) :
    K ⟶ (DaggerSimplicialCat.underlyingGraph (cell K)).Hom
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right :=
  FreeSimplicialPaths.inclusion (TwoObjectDaggerGraph.graph K)
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- The first equivalence is the original free-category adjunction. -/
def graphHomEquiv (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    (cell K ⟶ C) ≃ (TwoObjectDaggerGraph.graph K ⟶ DaggerSimplicialCat.forgetGraph.obj C) :=
  FreeDaggerSimplicialCategory.adjunction.homEquiv _ _

/-- The exact unrestricted two-object universal property in `bg.eq.A-univ`. -/
def homEquiv (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    (cell K ⟶ C) ≃ (Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y))) :=
  (graphHomEquiv K C).trans
    (TwoObjectDaggerGraph.homEquiv K (DaggerSimplicialCat.forgetGraph.obj C))

/-- Classification reads both object images and restriction to the forward generator. -/
theorem homEquiv_apply (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (F : cell K ⟶ C) :
    homEquiv K C F = ⟨F.obj TwoObjectDaggerGraph.left,
      F.obj TwoObjectDaggerGraph.right, generator K ≫ F.map _ _⟩ := rfl

/-- Precomposition keeps the ordered object images and composes the generating edge. -/
theorem homEquiv_naturality_left {K L : SSet.{u}} (φ : K ⟶ L)
    (C : DaggerSimplicialCat.{u, u}) (F : cell L ⟶ C) :
    homEquiv K C (functor.map φ ≫ F) =
      ⟨(homEquiv L C F).1, (homEquiv L C F).2.1,
        φ ≫ (homEquiv L C F).2.2⟩ := by
  change TwoObjectDaggerGraph.homEquiv K (DaggerSimplicialCat.forgetGraph.obj C)
    (FreeDaggerSimplicialCategory.adjunction.homEquiv _ _
      (FreeDaggerSimplicialCategory.functor.map
        (TwoObjectDaggerGraph.functor.map φ) ≫ F)) = _
  rw [FreeDaggerSimplicialCategory.adjunction.homEquiv_naturality_left]
  rfl

/-- Postcomposition permits arbitrary target object maps and full enriched hom maps. -/
theorem homEquiv_naturality_right (K : SSet.{u})
    {C D : DaggerSimplicialCat.{u, u}} (F : cell K ⟶ C) (H : C ⟶ D) :
    homEquiv K D (F ≫ H) =
      ⟨H.obj (homEquiv K C F).1, H.obj (homEquiv K C F).2.1,
        (homEquiv K C F).2.2 ≫ H.map _ _⟩ := by
  change TwoObjectDaggerGraph.homEquiv K (DaggerSimplicialCat.forgetGraph.obj D)
    (FreeDaggerSimplicialCategory.adjunction.homEquiv _ _ (F ≫ H)) = _
  rw [FreeDaggerSimplicialCategory.adjunction.homEquiv_naturality_right]
  rfl

end
end DaggerModels.TwoObjectDaggerCell
