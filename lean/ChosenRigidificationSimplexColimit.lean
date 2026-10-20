import DaggerModels.OrdinaryRigidification
import DaggerModels.RigidificationVertices
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

open CategoryTheory Functor Limits DaggerModels

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

abbrev C := OrdinaryRigidification.rigidification.{u}
abbrev T := OrdinaryRigidification.cosimplicialThickening.{u}
abbrev thickeningUnit := OrdinaryRigidification.RigidificationVertices.thickeningUnit.{u}
abbrev ρ := OrdinaryRigidification.rigidificationSimplexIso.{u}
abbrev RV := OrdinaryRigidification.RigidificationVertices.vertexEquiv.{u}

local instance : HasColimits.{u} SimplicialCat.{u, u} := simplicialCatHasColimits
local instance : HasColimitsOfSize.{0, u} SimplicialCat.{u, u} :=
  hasColimitsOfSizeShrink.{0, u} SimplicialCat.{u, u}

local instance : C.IsLeftKanExtension thickeningUnit := by
  dsimp [C, thickeningUnit, OrdinaryRigidification.rigidification,
    OrdinaryRigidification.RigidificationVertices.thickeningUnit]
  infer_instance

abbrev SimplexIndex (X : SSet.{u}) := CostructuredArrow uliftYoneda.{u} X

abbrev simplexDiagram (X : SSet.{u}) : SimplexIndex X ⥤ SimplicialCat.{u, u} :=
  CostructuredArrow.proj uliftYoneda X ⋙ T

/-- The actual chosen-C pointwise left-Kan cocone, with its original unit legs. -/
def simplexCocone (X : SSet.{u}) : Cocone (simplexDiagram X) :=
  (LeftExtension.mk C thickeningUnit).coconeAt X

@[simp] theorem simplexCocone_pt (X : SSet.{u}) : (simplexCocone X).pt = C.obj X := rfl

@[simp] theorem simplexCocone_leg (X : SSet.{u}) (σ : SimplexIndex X) :
    (simplexCocone X).ι.app σ = thickeningUnit.app σ.left ≫ C.map σ.hom := rfl

/-- Full UP of the same cocone, including arbitrary enriched target desc/fac/uniq. -/
def simplexCoconeIsColimit (X : SSet.{u}) : IsColimit (simplexCocone X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension C thickeningUnit X

/-- Retain the original complete enriched descent data. -/
def simplexDesc (X : SSet.{u}) (s : Cocone (simplexDiagram X)) : C.obj X ⟶ s.pt :=
  (simplexCoconeIsColimit X).desc s

@[reassoc] theorem simplexDesc_fac (X : SSet.{u}) (s : Cocone (simplexDiagram X))
    (σ : SimplexIndex X) : thickeningUnit.app σ.left ≫ C.map σ.hom ≫ simplexDesc X s = s.ι.app σ :=
  (simplexCoconeIsColimit X).fac s σ

theorem simplexDesc_uniq (X : SSet.{u}) (s : Cocone (simplexDiagram X))
    (F : C.obj X ⟶ s.pt) (hF : ∀ σ, thickeningUnit.app σ.left ≫ C.map σ.hom ≫ F = s.ι.app σ) :
    F = simplexDesc X s :=
  (simplexCoconeIsColimit X).uniq s F hF

/-- Representable comparison inverse is the same actual left-Kan unit. -/
theorem representable_inv (n : SimplexCategory) : (ρ.app n).inv = thickeningUnit.app n := rfl

theorem representable_unit_hom (n : SimplexCategory) :
    thickeningUnit.app n ≫ (ρ.app n).hom = 𝟙 (T.obj n) := (ρ.app n).inv_hom_id

theorem representable_hom_unit (n : SimplexCategory) :
    (ρ.app n).hom ≫ thickeningUnit.app n = 𝟙 (C.obj (uliftYoneda.obj n)) := (ρ.app n).hom_inv_id

end

end DaggerChosenRigidificationNecklace
