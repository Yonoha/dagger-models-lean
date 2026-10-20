import ActualDaggerIsomorphismComponentMaps
import ActualIsomorphismPartLocalWeakInvariance
import NativeFixedDaggerCompletionWeakBridge

/-! The EXISTING all-isomorphism-component part, viewed on its SAME fixed object type.
Its maps retain the original enrichment, dagger, all objects and all Hom maps.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerNativeFixedDaggerCompletionWeakBridge
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeFixedDaggerIsomorphismPart
noncomputable section

def part {O : Type u} (C : FixedDaggerCategory O) : FixedDaggerCategory O :=
  fixedOfDagger (DaggerActualDaggerIsomorphismComponentPart.part (originalDagger C))

def map {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) : part C ⟶ part D where
  underlying :=
    { map := fun i j ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (originalDaggerHom F)).map i j
      map_id := fun i ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (originalDaggerHom F)).map_id i
      map_comp := fun i j k ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (originalDaggerHom F)).map_comp i j k }
  map_dagger := (DaggerActualDaggerIsomorphismComponentMaps.map (originalDaggerHom F)).map_dagger

def inclusion {O : Type u} (C : FixedDaggerCategory O) : part C ⟶ C where
  underlying :=
    { map := fun i j ↦ (DaggerActualDaggerIsomorphismComponentPart.inclusion
        (originalDagger C)).map i j
      map_id := fun i ↦ (DaggerActualDaggerIsomorphismComponentPart.inclusion
        (originalDagger C)).map_id i
      map_comp := fun i j k ↦ (DaggerActualDaggerIsomorphismComponentPart.inclusion
        (originalDagger C)).map_comp i j k }
  map_dagger := (DaggerActualDaggerIsomorphismComponentPart.inclusion
    (originalDagger C)).map_dagger

theorem map_hom {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) (i j : O) :
    (map F).underlying.map i j =
      (DaggerActualSimplicialIsomorphismComponentMaps.map
        (originalDaggerHom F).toEnrichedFunctor).map i j := rfl

theorem map_weak {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D)
    [WeakEquivalence F] : WeakEquivalence (map F) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  have hF := (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original F).mp
    inferInstance
  intro i j
  exact DaggerActualIsomorphismPartLocalWeakInvariance.hom_weak
    (originalDaggerHom F).toEnrichedFunctor hF i j

theorem inclusion_natural {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    map F ≫ inclusion D = inclusion C ≫ F := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  rfl

theorem map_id {O : Type u} (C : FixedDaggerCategory O) : map (𝟙 C) = 𝟙 (part C) := by
  apply originalDaggerHom_injective
  change DaggerActualDaggerIsomorphismComponentMaps.map (𝟙 (originalDagger C)) = 𝟙 _
  exact DaggerActualDaggerIsomorphismComponentMaps.map_id _

theorem map_comp {O : Type u} {C D E : FixedDaggerCategory O} (F : C ⟶ D) (G : D ⟶ E) :
    map (F ≫ G) = map F ≫ map G := by
  apply originalDaggerHom_injective
  change DaggerActualDaggerIsomorphismComponentMaps.map
    (originalDaggerHom F ≫ originalDaggerHom G) = _
  exact DaggerActualDaggerIsomorphismComponentMaps.map_comp _ _

def functor (O : Type u) : FixedDaggerCategory O ⥤ FixedDaggerCategory O where
  obj := part
  map := map
  map_id := map_id
  map_comp := map_comp

end
end DaggerNativeFixedDaggerIsomorphismPart
