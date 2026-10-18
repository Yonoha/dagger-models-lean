import ActualOriginalCoreEnrichedMappingZigzag

/-! The SAME original Kan localization and the SAME actual Yoneda point maps. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerNativeOriginalRReplacedMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalKanLocalizedPointIso
noncomputable section

/-- A proved native weak map gives its actual isomorphism in the ORIGINAL localization. -/
def mapIso {A B : SSet.{u}} (f : A ⟶ B) (hf : WeakEquivalence f) :
    kanWeak.Q.obj A ≅ kanWeak.Q.obj B := by
  have : IsIso (kanWeak.Q.map f) :=
    Localization.inverts kanWeak.Q kanWeak f ((weakEquivalence_iff f).mp hf)
  exact asIso (kanWeak.Q.map f)

/-- The forward localization map retains the SAME actual original point. -/
theorem point_hom {A B : SSet.{u}} (f : A ⟶ B) (hf : WeakEquivalence f)
    (a : A _⦋0⦌) (b : B _⦋0⦌) (hab : f.app (op ⦋0⦌) a = b) :
    kanWeak.Q.map (SSet.yonedaEquiv.symm a) ≫ (mapIso f hf).hom =
      kanWeak.Q.map (SSet.yonedaEquiv.symm b) := by
  change kanWeak.Q.map (SSet.yonedaEquiv.symm a) ≫ kanWeak.Q.map f = _
  rw [← kanWeak.Q.map_comp]
  apply congrArg (fun g : (Δ[0] : SSet.{u}) ⟶ B ↦ kanWeak.Q.map g)
  rw [SSet.yonedaEquiv_symm_comp, hab]

/-- Its inverse retains the SAME actual point, rather than choosing a new representative. -/
theorem point_inv {A B : SSet.{u}} (f : A ⟶ B) (hf : WeakEquivalence f)
    (a : A _⦋0⦌) (b : B _⦋0⦌) (hab : f.app (op ⦋0⦌) a = b) :
    kanWeak.Q.map (SSet.yonedaEquiv.symm b) ≫ (mapIso f hf).inv =
      kanWeak.Q.map (SSet.yonedaEquiv.symm a) := by
  rw [← point_hom f hf a b hab]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end
end DaggerNativeOriginalKanLocalizedPointIso
