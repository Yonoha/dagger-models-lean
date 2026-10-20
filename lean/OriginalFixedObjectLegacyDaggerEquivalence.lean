import OriginalFixedObjectDaggerCategories
import FixedCategoryModel

/-!
# Reuse of the original fixed-object dagger category

This equivalence retains exactly the object type, enrichment, dagger, and full Hom maps.
The legacy identity-object-function proof is eliminated before recovering a fixed Hom map.
It does not identify the strict groupoid subcategory with the ambient dagger category.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u
namespace DaggerOriginalFixedObjectLegacyDaggerEquivalence
noncomputable section

/-- Keep the original fixed enrichment and dagger in the legacy presentation. -/
def toLegacyObject {O : Type u} (C : FixedDaggerCategory O) : FixedDaggerSimplicialCat O :=
  ⟨C.underlying.enriched, C.dagger⟩

/-- Keep the original fixed enrichment and dagger in the current presentation. -/
def fromLegacyObject {O : Type u} (C : FixedDaggerSimplicialCat O) : FixedDaggerCategory O :=
  ⟨⟨C.enriched⟩, C.daggerStructure⟩

/-- The legacy arrow is exactly the original full dagger functor. -/
def toLegacyHom {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    toLegacyObject C ⟶ toLegacyObject D := ⟨originalDaggerHom F, rfl⟩

/-- Eliminate the identity-object-function equality, preserving every Hom map and law. -/
def fromLegacyHom {O : Type u} {C D : FixedDaggerSimplicialCat O} (F : C ⟶ D) :
    fromLegacyObject C ⟶ fromLegacyObject D := by
  rcases F with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  exact ⟨⟨map, map_id, map_comp⟩, map_dagger⟩

/-- The forward comparison retains the full original dagger functor. -/
def toLegacyFunctor (O : Type u) : FixedDaggerCategory O ⥤ FixedDaggerSimplicialCat O where
  obj := toLegacyObject
  map := toLegacyHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The reverse comparison eliminates only the object-function equality proof. -/
def fromLegacyFunctor (O : Type u) : FixedDaggerSimplicialCat O ⥤ FixedDaggerCategory O where
  obj := fromLegacyObject
  map := fromLegacyHom
  map_id _ := rfl
  map_comp F G := by
    rcases F with ⟨⟨⟨objF, mapF, idF, compF⟩, dagF⟩, hF⟩
    rcases G with ⟨⟨⟨objG, mapG, idG, compG⟩, dagG⟩, hG⟩
    cases hF
    cases hG
    rfl

/-- The two presentations are equivalent with identity object components. -/
def legacyDaggerEquivalence (O : Type u) :
    FixedDaggerCategory O ≌ FixedDaggerSimplicialCat O where
  functor := toLegacyFunctor O
  inverse := fromLegacyFunctor O
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro C D F
    rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro C D F
    rcases F with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
    cases h
    rfl)
  functor_unitIso_comp _ := rfl

end
end DaggerOriginalFixedObjectLegacyDaggerEquivalence
