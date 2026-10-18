import OriginalFixedObjectDaggerCotensorRepresentation
import OriginalFixedObjectStrictGroupoidCotensors
import OriginalFixedObjectEnrichedCotensorNaturality

/-!
# Cotensor representation for the actual strict dagger mapping object

Restrict the proved full ambient cotensor equivalence to the original full
subcategory. Parameter and source naturality concern the actual native enriched
precomposition map, rather than a replacement mapping simplicial set.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectDaggerCotensorRepresentation
universe u
namespace DaggerOriginalFixedObjectStrictDaggerCotensorRepresentation
noncomputable section

/-- The ambient equivalence is natural in the full original source dagger functor. -/
theorem ambientCotensorHomEquiv_source {O : Type u} {A B : FixedDaggerCategory O}
    (i : A ⟶ B) (D : FixedDaggerCategory O) (K : SSet.{u})
    (F : K ⟶ (B ⟶[SSet] D)) :
    cotensorHomEquiv A D K (F ≫ eHomWhiskerRight SSet i D) =
      i ≫ cotensorHomEquiv B D K F := by
  exact DaggerOriginalFixedObjectEnrichedCotensorNaturality.daggerCotensorHomEquiv_source K i F

/-- Full subcategory arrows into the original strict cotensor are unchanged ambient arrows. -/
def strictHomEquiv {O : Type u} (A D : FixedStrictDaggerGroupoids O) (K : SSet.{u}) :
    (A.obj ⟶ daggerCotensor K D.obj) ≃ (A ⟶ strictDaggerCotensor K D) where
  toFun F := ObjectProperty.homMk F
  invFun F := F.hom
  left_inv _ := rfl
  right_inv F := by cases F; rfl

/-- The actual strict native mapping object represents the same full original cotensor. -/
def strictCotensorHomEquiv {O : Type u} (A D : FixedStrictDaggerGroupoids O) (K : SSet.{u}) :
    (K ⟶ (A ⟶[SSet] D)) ≃ (A ⟶ strictDaggerCotensor K D) :=
  (cotensorHomEquiv A.obj D.obj K).trans (strictHomEquiv A D K)

/-- Native source precomposition is the full original strict cotensor precomposition. -/
theorem strictCotensorHomEquiv_source {O : Type u} {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) (D : FixedStrictDaggerGroupoids O) (K : SSet.{u})
    (F : K ⟶ (B ⟶[SSet] D)) :
    strictCotensorHomEquiv A D K (F ≫ eHomWhiskerRight SSet i D) =
      i ≫ strictCotensorHomEquiv B D K F := by
  apply ObjectProperty.hom_ext
  exact ambientCotensorHomEquiv_source i.hom D.obj K F

/-- Every actual parameter map gives the original restriction of strict cotensors. -/
theorem strictCotensorHomEquiv_parameter {O : Type u} (A D : FixedStrictDaggerGroupoids O)
    {K L : SSet.{u}} (j : K ⟶ L) (F : L ⟶ (A ⟶[SSet] D)) :
    strictCotensorHomEquiv A D K (j ≫ F) =
      strictCotensorHomEquiv A D L F ≫
        ((strictDaggerCotensorBifunctor O).map j.op).app D := by
  apply ObjectProperty.hom_ext
  exact cotensorHomEquiv_parameter A.obj D.obj j F

end
end DaggerOriginalFixedObjectStrictDaggerCotensorRepresentation
