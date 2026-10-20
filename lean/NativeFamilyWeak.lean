import OriginalSSetFamilySigmaReconciledRecovered
import ActualQWeightedAugmentationCoproducts

/-! The literal pointwise family map is weak when all original component maps are weak. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFamilyWeak
noncomputable section

def familyMap {J : Type u} {X Y : J → SSet.{u}} (f : ∀ j, X j ⟶ Y j) :
    familySSet X ⟶ familySSet Y where
  app n a := ⟨a.1, (f a.1).app n a.2⟩
  naturality n m α := by
    funext a
    refine Sigma.ext rfl ?_
    exact heq_of_eq (congrFun ((f a.1).naturality α) a.2)

theorem familyMap_inclusion {J : Type u} {X Y : J → SSet.{u}}
    (f : ∀ j, X j ⟶ Y j) (j : J) :
    familyInclusion X j ≫ familyMap f = f j ≫ familyInclusion Y j := by
  apply NatTrans.ext
  rfl

theorem familyMap_coproduct_square {J : Type u} {X Y : J → SSet.{u}}
    (f : ∀ j, X j ⟶ Y j) :
    (familySigmaIso X).hom ≫ familyMap f = Limits.Sigma.map f ≫ (familySigmaIso Y).hom := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [← Category.assoc, familySigmaIso_ι, familyMap_inclusion]
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, familySigmaIso_ι]

theorem familyMap_weak {J : Type u} {X Y : J → SSet.{u}} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, WeakEquivalence (f j)) : WeakEquivalence (familyMap f) := by
  have : WeakEquivalence (Limits.Sigma.map f) := (weakEquivalence_iff_GW _).mpr
    (DaggerOriginalFlagFlankification.sigmaMap_GW f
      (fun j ↦ (weakEquivalence_iff_GW _).mp (hf j)))
  have : WeakEquivalence (Limits.Sigma.map f ≫ (familySigmaIso Y).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (familyMap_coproduct_square f)

end
end DaggerNativeFamilyWeak
