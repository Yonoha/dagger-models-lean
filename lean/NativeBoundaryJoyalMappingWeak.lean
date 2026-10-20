import NativeBoundaryCategoricalCylinder
import NativeRelativeTrivialFibrationCylinder
import NativeJoyalMappingTest

/-!
# Full boundary right lifting implies the exact Joyal mapping weak test

Native Kan trivial fibrations lift against all monomorphisms. Build a whole
walking-isomorphism interval homotopy of a section/retraction, then use the
previously verified exact internal-Hom precomposition equivalence.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open DaggerModels
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeBoundaryCategoricalCylinder
open DaggerNativeWalkingRetractionMappingEquivalence
open DaggerNativeJoyalMappingTest
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBoundaryJoyalMappingWeak
noncomputable section

/-- The literal native boundary family detects the native Kan trivial-fibration class. -/
theorem boundary_rlp_iff_trivialFibration {X Y : SSet.{u}} (f : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι f) ↔
      trivialFibrations SSet.{u} f := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  constructor
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact h n
  · intro h n
    exact h _ ⟨n⟩

/-- The entire full boundary lifting class also lifts against every native monomorphism. -/
theorem boundary_rlp_monomorphisms {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι f) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp f := by
  obtain ⟨hfi, hwe⟩ := (mem_trivialFibrations_iff f).1
    ((boundary_rlp_iff_trivialFibration f).1 hf)
  have : Fibration f := hfi
  have : WeakEquivalence f := hwe
  intro A B i hi
  have : Mono i := hi
  have : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff i).2 inferInstance
  infer_instance

/-- Full monomorphism lifting supplies an exact section of the original map. -/
theorem exists_section {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y := by
  let E := (⊥ : Y.Subcomplex)
  let a : E.toSSet ⟶ X :=
    { app := fun q x ↦ False.elim (show False from x.property)
      naturality := by
        intro q k α
        funext x
        exact False.elim (show False from x.property) }
  have : HasLiftingProperty E.ι f := hf _ (show Mono E.ι from inferInstance)
  let sq : CommSq a E.ι f (𝟙 Y) := ⟨by ext⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- Native precomposition along the entire original boundary-right map is an equivalence. -/
theorem boundary_rlp_pre_isEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι f) (Z : SSet.{u}) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z)).toFunctor.IsEquivalence := by
  have hm := boundary_rlp_monomorphisms f hf
  obtain ⟨s, hs⟩ := exists_section f hm
  have hr : (f ≫ s) ≫ f = f := by rw [Category.assoc, hs, Category.comp_id]
  obtain ⟨H, h₀, h₁, _⟩ := exists_cylinder f hm (f ≫ s) hr
  exact show (mappingEquivalence s f hs H h₀ h₁ Z).symm.functor.IsEquivalence by
    infer_instance

/-- The conclusion is the fixed original mapping-category weak predicate. -/
theorem boundary_rlp_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι f) :
    weakCategoricalEquivalences f :=
  fun Z _ ↦ boundary_rlp_pre_isEquivalence f hf Z

end
end DaggerNativeBoundaryJoyalMappingWeak
