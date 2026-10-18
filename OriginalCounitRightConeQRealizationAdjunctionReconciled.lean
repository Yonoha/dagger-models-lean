import OriginalCounitRightConeQFunctorReconciled
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Realization and singular adjunction for the original right-cone Q

Use Mathlib's presheaf left Kan extension and restricted Yoneda adjunction for
the same cosimplicial Q. The pointwise colimit has the original Q maps as legs;
no replacement of the cosimplicial object or restriction of universes is made.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open DaggerOriginalCounitRightConeQFunctor

universe u

namespace DaggerOriginalCounitRightConeQRealizationAdjunction

noncomputable section

/-- Left Kan extension of the original Q along the universe-lifted Yoneda embedding. -/
def realization : SSet.{u} ⥤ SSet.{u} :=
  uliftYoneda.{u}.leftKanExtension QFunctor.{u}

/-- The original Q-valued singular simplicial set, with all original simplex operators. -/
def singular : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{u} QFunctor.{u}

/-- The actual left Kan extension unit on the original cosimplicial Q. -/
def realizationUnit : QFunctor.{u} ⟶ uliftYoneda.{u} ⋙ realization.{u} :=
  uliftYoneda.{u}.leftKanExtensionUnit QFunctor.{u}

instance realizationIsLeftKanExtension :
    realization.{u}.IsLeftKanExtension realizationUnit.{u} := by
  dsimp [realization, realizationUnit]
  infer_instance

/-- Mathlib's presheaf adjunction applied to the original Q and its actual Kan extension. -/
def realizationSingularAdjunction : realization.{u} ⊣ singular.{u} := by
  dsimp [realization, singular]
  exact Presheaf.uliftYonedaAdjunction.{u} (A := QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtension QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit QFunctor.{u})

/-- The actual realization preserves colimits of the size used for simplicial sets. -/
instance : PreservesColimitsOfSize.{u, u} realization.{u} := by
  dsimp [realization]
  exact Presheaf.preservesColimitsOfSize_of_isLeftKanExtension.{u} (A := QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtension QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit QFunctor.{u})

/-- The literal simplex index, retaining all simplices and all simplex operators. -/
abbrev SimplexIndex (X : SSet.{u}) := CostructuredArrow uliftYoneda.{u} X

/-- The actual original-Q diagram used in the pointwise Kan extension. -/
def simplexDiagram (X : SSet.{u}) : SimplexIndex X ⥤ SSet.{u} :=
  CostructuredArrow.proj uliftYoneda X ⋙ QFunctor.{u}

/-- The actual Kan extension cocone, retaining the original unit and simplex maps. -/
def simplexCocone (X : SSet.{u}) : Cocone (simplexDiagram X) :=
  (Functor.LeftExtension.mk realization.{u} realizationUnit.{u}).coconeAt X

theorem simplexCocone_leg (X : SSet.{u}) (σ : SimplexIndex X) :
    (simplexCocone X).ι.app σ =
      realizationUnit.app σ.left ≫ realization.map σ.hom := rfl

/-- The full pointwise universal property of realization, obtained from Mathlib. -/
def simplexCoconeIsColimit (X : SSet.{u}) : IsColimit (simplexCocone X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    realization.{u} realizationUnit.{u} X

/-- The canonical identification with the colimit of the literal original-Q diagram. -/
def realizationColimitIso (X : SSet.{u}) :
    realization.obj X ≅ colimit (simplexDiagram X) :=
  uliftYoneda.{u}.leftKanExtensionObjIsoColimit QFunctor.{u} X

end

end DaggerOriginalCounitRightConeQRealizationAdjunction
