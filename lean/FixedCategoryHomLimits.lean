import FixedCategoryMonadicLimits
import FixedCategoryFilteredDomains
import FixedCategoryGenerators
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! One actual ordered Hom evaluation, retaining the original identity-object adapter
and endpoint transports, with full small-limit and filtered-colimit preservation. -/

open CategoryTheory Limits DaggerModels
open DaggerFixedGraph DaggerFixedGraphPlacements DaggerFixedGraphConnectedColimits

universe u

namespace DaggerFixedCategoryHomLimits

noncomputable section

variable (O : Type u)

abbrev homEval (x y : O) : FixedDaggerSimplicialCat O ⥤ SSet.{u} :=
  FixedDaggerSimplicialCat.forgetGraph O ⋙ DaggerFixedGraphPlacements.homEval O x y

theorem homEval_obj (C : FixedDaggerSimplicialCat O) (x y : O) :
    (homEval O x y).obj C = C.underlyingGraph.Hom x y := rfl

theorem homEval_map {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    (homEval O x y).map f = ((FixedDaggerSimplicialCat.forgetGraph O).map f).map x y := rfl

variable {O}

/-- The exact equality of the original target mapping objects induced by f.obj=id. -/
def endpointEq {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    D.underlyingGraph.Hom (f.val.obj x) (f.val.obj y) = D.underlyingGraph.Hom x y :=
  congrArg₂ D.underlyingGraph.Hom (congrFun f.property x) (congrFun f.property y)

theorem homEval_map_forward {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    (homEval O x y).map f = f.val.map x y ≫ eqToHom (endpointEq f x y) := by
  rcases f with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  rfl

theorem homEval_map_backward {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    f.val.map x y = (homEval O x y).map f ≫ eqToHom (endpointEq f x y).symm := by
  rcases f with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  rfl

def homArrowIso {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    Arrow.mk (f.val.map x y) ≅ Arrow.mk ((homEval O x y).map f) :=
  Arrow.isoMk (Iso.refl _) (eqToIso (endpointEq f x y)) (by
    simpa using homEval_map_forward f x y)

theorem original_hom_property_iff (P : MorphismProperty SSet.{u})
    {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    P ((homEval O x y).map f) ↔ P (f.val.map x y) :=
  DaggerFixedCategoryGenerators.original_hom_property_iff P f x y

variable (O)

instance graphHomPreservesSmallLimits (x y : O) :
    PreservesLimitsOfSize.{u, u} (DaggerFixedGraphPlacements.homEval O x y) := by
  letI := chosenLinearOrder O
  rcases lt_trichotomy x y with h | h | h
  · exact (upperAdjunction O ⟨(x, y), h⟩).rightAdjoint_preservesLimits
  · subst y
    exact (diagonalAdjunction O x).rightAdjoint_preservesLimits
  · letI := (upperAdjunction O ⟨(y, x), h⟩).rightAdjoint_preservesLimits
    exact preservesLimits_of_natIso (homDaggerIso O y x)

instance homEvalPreservesSmallLimits (x y : O) :
    PreservesLimitsOfSize.{u, u} (homEval O x y) := by
  dsimp only [homEval]
  infer_instance

def mappedConeIsLimit (x y : O) {J : Type u} [SmallCategory J]
    {K : J ⥤ FixedDaggerSimplicialCat O} {c : Cone K} (hc : IsLimit c) :
    IsLimit ((homEval O x y).mapCone c) := isLimitOfPreserves (homEval O x y) hc

theorem map_isPullback (x y : O) {A B C D : FixedDaggerSimplicialCat O}
    {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (sq : IsPullback p q f g) :
    IsPullback ((homEval O x y).map p) ((homEval O x y).map q)
      ((homEval O x y).map f) ((homEval O x y).map g) := by
  letI : PreservesLimitsOfSize.{0, 0} (homEval O x y) :=
    preservesSmallestLimits_of_preservesLimits (homEval O x y)
  exact sq.map (homEval O x y)

instance homEvalPreservesFilteredColimits (x y : O) (J : Type u)
    [SmallCategory J] [IsFiltered J] : PreservesColimitsOfShape J (homEval O x y) := by
  dsimp only [homEval]
  infer_instance

def mappedCoconeIsColimit (x y : O) {J : Type u} [SmallCategory J] [IsFiltered J]
    {K : J ⥤ FixedDaggerSimplicialCat O} {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((homEval O x y).mapCocone c) := isColimitOfPreserves (homEval O x y) hc

end

end DaggerFixedCategoryHomLimits
