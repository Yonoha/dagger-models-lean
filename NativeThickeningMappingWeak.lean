import NativeOriginalMappingHomotopy
import NativeRawHomotopyWeakInvariance

/-! The SAME original thickening projection is weak on the FULL original mapping SSet. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalEnrichedCotensorMapping DaggerNativeOriginalMappingHomotopy
open DaggerNativeThickeningFullSection DaggerActualOrdinalRigidificationComparison
open DaggerNativeThickeningCotensorContraction DaggerNativeThickeningContractionEndpoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeThickeningMappingWeak
noncomputable section

/-- A raw homotopy of entire mapping-space maps, including all original object functions. -/
def retractionHomotopy (n : SimplexCategory) (C : SimplicialCat.{u, u}) :
    SSet.Homotopy (𝟙 (mapping (cosimplicialThickening.obj n) C))
      (pre (thickeningProjection n.len ≫ fullSection n) C) :=
  (homotopy (contractionFunctor n) C).congr
    (by rw [DaggerNativeThickeningContractionEndpoints.zero,
      DaggerOriginalEnrichedCotensorMapping.pre_id])
    (by rw [DaggerNativeThickeningContractionEndpoints.one])

/-- No Kan, groupoid, or injectivity premise is imposed on the original target C. -/
theorem projection_pre_weak (n : SimplexCategory) (C : SimplicialCat.{u, u}) :
    WeakEquivalence (pre (thickeningProjection.{u} n.len) C) := by
  let f := pre (thickeningProjection.{u} n.len) C
  let g := pre (fullSection.{u} n) C
  have hfg : f ≫ g = 𝟙 _ := by
    dsimp [f, g]
    rw [← DaggerOriginalEnrichedCotensorMapping.pre_comp, fullSection_projection,
      DaggerOriginalEnrichedCotensorMapping.pre_id]
  have hgf : g ≫ f = pre (thickeningProjection n.len ≫ fullSection n) C :=
    (DaggerOriginalEnrichedCotensorMapping.pre_comp _ _ C).symm
  have : WeakEquivalence (g ≫ f) := by
    rw [hgf]
    exact (DaggerNativeRawHomotopyWeakInvariance.weakEquivalence_iff_homotopy
      (retractionHomotopy n C)).1 inferInstance
  let r : RetractArrow f (g ≫ f) :=
    { i := Arrow.homMk f (𝟙 _) (by
        change f ≫ (g ≫ f) = f ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, hfg, Category.id_comp])
      r := Arrow.homMk g (𝟙 _) (by
        change g ≫ f = (g ≫ f) ≫ 𝟙 _
        exact (Category.comp_id _).symm)
      retract := by ext <;> simp [hfg] }
  exact ⟨MorphismProperty.of_retract r (mem_weakEquivalences (g ≫ f))⟩

end
end DaggerNativeThickeningMappingWeak
