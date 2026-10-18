import ActualQWeightedResolutionCells

/-! The literal original Q-weighted replacement is functorial in the entire simplicial set. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerActualQWeightedResolutionCells DaggerNativeSimplicialReplacement
open DaggerSSetGluing DaggerActualQWeightedResolutionCofibrations
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedResolutionFunctor
noncomputable section

/-- Use the unchanged weighted replacement objects and the unchanged whole chain maps. -/
def functor : SSet.{u} ⥤ SSet.{u} where
  obj X := DaggerBisimplicialDiagonal.diag (replacement
    (DaggerActualQWeightedResolutionNaturality.weights X))
  map f := DaggerActualQWeightedResolutionNaturality.map f
  map_id X := by
    apply NatTrans.ext
    funext q x
    apply (flatEquiv X q q).injective
    simpa [flatMap] using flatEquiv_naturality (𝟙 X) q q x
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext q x
    apply (flatEquiv Z q q).injective
    have hfg := flatEquiv_naturality (f ≫ g) q q x
    have hf := flatEquiv_naturality f q q x
    have hg := flatEquiv_naturality g q q
      ((DaggerActualQWeightedResolutionNaturality.map f).app q x)
    change flatEquiv Y q q ((DaggerActualQWeightedResolutionNaturality.map f).app q x) =
      flatMap f q q (flatEquiv X q q x) at hf
    rw [hf] at hg
    have hm : flatMap (f ≫ g) q q (flatEquiv X q q x) =
        flatMap g q q (flatMap f q q (flatEquiv X q q x)) := rfl
    exact hfg.trans (hm.trans hg.symm)

/-- The augmentation is the exact old simplexCocone map on the entire Q parameter. -/
def augmentation : functor.{u} ⟶ realization.{u} where
  app X := DaggerActualQWeightedResolutionNaturality.toRealization X
  naturality {_X _Y} f := DaggerActualQWeightedResolutionNaturality.augmentation_square f

/-- The original full functor preserves the geometric weak class. -/
theorem map_GW {X Y : SSet.{u}} (f : X ⟶ Y) (hf : GW f) : GW (functor.map f) :=
  DaggerActualQWeightedResolutionNaturality.map_GW f hf

instance preservesCofibrations : functor.{u}.PreservesCofibrations where
  cofibration_map f := map_cofibration f

instance preservesTrivialCofibrations : functor.{u}.PreservesTrivialCofibrations where
  trivialCofibrations_le := by
    intro X Y f hf
    rw [mem_trivialCofibrations_iff] at hf
    have : Cofibration f := hf.1
    have : WeakEquivalence f := hf.2
    have : Cofibration (functor.map f) := inferInstance
    have : WeakEquivalence (functor.map f) := (weakEquivalence_iff_GW _).mpr
      (map_GW f ((weakEquivalence_iff_GW _).mp inferInstance))
    exact mem_trivialCofibrations _

end
end DaggerActualQWeightedResolutionFunctor
