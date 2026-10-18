import NativeOriginalFixedDaggerCofibrancy
import ActualCofibrantDaggerIntervalMappingComparison

/-! The ACTUAL ORIGINAL Interval record, with no extra cofibrancy or groupoid premise.
Its whole original C, j, p and native model classes are retained through the old equivalence.
The original p is followed only by the displayed native walking-interval/terminal ISO.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence DaggerOriginalFixedObjectGroupoidTerminals
open DaggerNativeOriginalFixedDaggerReplacement DaggerNativeOriginalFixedDaggerCofibrancy
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
attribute [local instance] DaggerFixedCategoryModel.modelCategory
universe u
namespace DaggerActualNativeDaggerIntervalPresentation
noncomputable section

def obj (H : DaggerUnitaryInterval.Interval.{u}) :
    FixedDaggerCategory DaggerUnitaryInterval.Vertex := fromLegacyObject H.C

theorem original_source_exact (H : DaggerUnitaryInterval.Interval.{u}) :
    toLegacyObject (obj H) = H.C := rfl

theorem legacy_cofibrant (H : DaggerUnitaryInterval.Interval.{u}) : IsCofibrant H.C := by
  have : Cofibration (initial.to DaggerUnitaryInterval.J) :=
    (isCofibrant_iff DaggerUnitaryInterval.J).mp inferInstance
  have : Cofibration H.j := H.cofibration
  have h : Cofibration (initial.to DaggerUnitaryInterval.J ≫ H.j) := inferInstance
  have he : initial.to H.C = initial.to DaggerUnitaryInterval.J ≫ H.j :=
    initialIsInitial.hom_ext _ _
  exact (isCofibrant_iff H.C).mpr (he.symm ▸ h)

theorem obj_cofibrant (H : DaggerUnitaryInterval.Interval.{u}) : IsCofibrant (obj H) := by
  have := legacy_cofibrant H
  exact fromLegacy_cofibrant H.C

theorem legacy_augmentation_weak (H : DaggerUnitaryInterval.Interval.{u}) :
    WeakEquivalence H.p := by
  have hlocal := H.localWeakEquivalence
  generalize H.p = F at hlocal ⊢
  rcases F with ⟨⟨⟨objectMap, homMap, homId, homComp⟩, homDagger⟩, h⟩
  cases h
  rw [weakEquivalence_iff]
  change ∀ i j, WeakEquivalence (homMap i j)
  intro i j
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (hlocal i j)

def terminalIso : fromLegacyObject DaggerUnitaryInterval.I.{u} ≅
    terminalFixedDagger DaggerUnitaryInterval.Vertex where
  hom := daggerToTerminal _
  inv :=
    { underlying :=
        { map := fun _ _ ↦ CartesianMonoidalCategory.toUnit _
          map_id := fun _ ↦ CartesianMonoidalCategory.toUnit_unique _ _
          map_comp := fun _ _ _ ↦ CartesianMonoidalCategory.toUnit_unique _ _ }
      map_dagger := fun _ _ ↦ CartesianMonoidalCategory.toUnit_unique _ _ }
  hom_inv_id := by
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro i j
    exact CartesianMonoidalCategory.toUnit_unique _ _
  inv_hom_id := by
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro i j
    exact CartesianMonoidalCategory.toUnit_unique _ _

def augmentation (H : DaggerUnitaryInterval.Interval.{u}) :
    obj H ⟶ terminalFixedDagger DaggerUnitaryInterval.Vertex :=
  fromLegacyHom H.p ≫ terminalIso.hom

theorem augmentation_original (H : DaggerUnitaryInterval.Interval.{u}) :
    augmentation H ≫ terminalIso.inv = fromLegacyHom H.p := by
  simp only [augmentation, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem augmentation_weak (H : DaggerUnitaryInterval.Interval.{u}) :
    WeakEquivalence (augmentation H) := by
  have := legacy_augmentation_weak H
  have : WeakEquivalence (fromLegacyHom H.p) := fromLegacy_weak H.p
  change WeakEquivalence (fromLegacyHom H.p ≫ terminalIso.hom)
  infer_instance

end
end DaggerActualNativeDaggerIntervalPresentation
