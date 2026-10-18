import NativeInnerJoyalMappingWeak
import ActualAntiInnerHornFactorization
import ActualFreeAntiJoyalMappingWeak
import OriginalHornReversal

/-!
# Actual anti-inner-left maps satisfy exactly the underlying Joyal mapping weak test

The entire actual free inner-horn map forgets to the coproduct of an original horn and
its genuine opposite, transported through the original two-copy and freeAnti isomorphisms.
The cofree adjunction then proves that every actual anti-inner-left map forgets to a
native inner-left map. The proved full native mapping weak test applies to these exact maps.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveFreePair
open DaggerActualAntiForgetAdjointTriple
open DaggerOriginalHornReversal DaggerOriginalStandardSimplexReversal
universe u
namespace DaggerActualAntiInnerJoyalMappingWeak
noncomputable section

/-- The actual opposite of each original inner horn is still in the full native inner-left class. -/
theorem opposite_horn_inner (a : DaggerNativeInnerHornFactorization.Index) :
    DaggerNativeInnerHornFactorization.innerAnodyne
      (SSet.opFunctor.map (DaggerNativeInnerHornFactorization.generator.{u} a)) := by
  haveI : DaggerNativeInnerHornFactorization.innerAnodyne.{u}.RespectsIso := by
    unfold DaggerNativeInnerHornFactorization.innerAnodyne
    infer_instance
  have h0 : 0 < a.2.1.rev := by
    have h := a.2.2
    simp only [Fin.lt_def, Fin.val_rev, Fin.val_zero, Fin.val_last] at h ⊢
    omega
  have hn : a.2.1.rev < Fin.last (a.1 + 2) := by
    have h := a.2.2
    simp only [Fin.lt_def, Fin.val_rev, Fin.val_zero, Fin.val_last] at h ⊢
    omega
  let e : Arrow.mk (SSet.opFunctor.map (DaggerNativeInnerHornFactorization.generator a)) ≅
      Arrow.mk (SSet.horn (a.1 + 2) a.2.1.rev).ι :=
    Arrow.isoMk (hornReversalIso _ _) (standardSimplexReversalIso _)
      (hornReversalHom_comp_ι _ _)
  exact (DaggerNativeInnerHornFactorization.innerAnodyne.arrow_mk_iso_iff e).2
    (DaggerNativeInnerPairing.horn_innerAnodyne _ h0 hn)

/-- Whole binary coproduct maps of original inner-left inputs remain inner-left. -/
theorem coproduct_inner {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D)
    (hi : DaggerNativeInnerHornFactorization.innerAnodyne i)
    (hj : DaggerNativeInnerHornFactorization.innerAnodyne j) :
    DaggerNativeInnerHornFactorization.innerAnodyne (coprod.map i j) := by
  intro E T p hp
  haveI : HasLiftingProperty i p := hi p hp
  haveI : HasLiftingProperty j p := hj p hp
  constructor
  intro u v sq
  let sq₁ : CommSq ((coprod.inl : A ⟶ A ⨿ C) ≫ u) i p
      ((coprod.inl : B ⟶ B ⨿ D) ≫ v) := ⟨by
    simpa only [Category.assoc, coprod.inl_map_assoc] using
      congrArg (fun k ↦ (coprod.inl : A ⟶ A ⨿ C) ≫ k) sq.w⟩
  let sq₂ : CommSq ((coprod.inr : C ⟶ A ⨿ C) ≫ u) j p
      ((coprod.inr : D ⟶ B ⨿ D) ≫ v) := ⟨by
    simpa only [Category.assoc, coprod.inr_map_assoc] using
      congrArg (fun k ↦ (coprod.inr : C ⟶ A ⨿ C) ≫ k) sq.w⟩
  refine ⟨coprod.desc sq₁.lift sq₂.lift, ?_, ?_⟩
  · apply coprod.hom_ext
    · simpa only [Category.assoc, coprod.inl_map_assoc, coprod.inl_desc] using sq₁.fac_left
    · simpa only [Category.assoc, coprod.inr_map_assoc, coprod.inr_desc] using sq₂.fac_left
  · apply coprod.hom_ext
    · simpa only [coprod.inl_desc_assoc] using sq₁.fac_right
    · simpa only [coprod.inr_desc_assoc] using sq₂.fac_right

/-- The entire underlying actual free inner-horn generator is native inner-left. -/
theorem free_generator_underlying_inner (a : DaggerNativeInnerHornFactorization.Index) :
    DaggerNativeInnerHornFactorization.innerAnodyne
      (freeAnti.map (DaggerNativeInnerHornFactorization.generator.{u} a)).hom := by
  haveI : DaggerNativeInnerHornFactorization.innerAnodyne.{u}.RespectsIso := by
    unfold DaggerNativeInnerHornFactorization.innerAnodyne
    infer_instance
  let i := DaggerNativeInnerHornFactorization.generator.{u} a
  have hi : DaggerNativeInnerHornFactorization.innerAnodyne i :=
    DaggerNativeInnerPairing.horn_innerAnodyne _ a.2.2.1 a.2.2.2
  let e₁ : Arrow.mk (coprod.map i (SSet.opFunctor.map i)) ≅ Arrow.mk (pairMap i).hom :=
    Arrow.isoMk (DaggerActualFreeAntiJoyalMappingWeak.coproductPairIso _)
      (DaggerActualFreeAntiJoyalMappingWeak.coproductPairIso _)
      (DaggerActualFreeAntiJoyalMappingWeak.coproductPairIso_natural i).symm
  let e₂ : Arrow.mk (pairMap i).hom ≅ Arrow.mk (freeAnti.map i).hom :=
    Arrow.isoMk (DaggerOriginalFreeAntiSimplicialHomotopyEquivalence.underlyingPairIso _)
      (DaggerOriginalFreeAntiSimplicialHomotopyEquivalence.underlyingPairIso _)
      (congrArg AntiInvolutiveSSet.Hom.hom (pairIsoFreeAnti.hom.naturality i)).symm
  exact (DaggerNativeInnerHornFactorization.innerAnodyne.arrow_mk_iso_iff (e₁ ≪≫ e₂)).1
    (coproduct_inner i (SSet.opFunctor.map i) hi (opposite_horn_inner a))

/-- The actual cofree object preserves native inner-right maps. -/
theorem cofree_inner {A B : SSet.{u}} (p : A ⟶ B)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p) :
    DaggerActualAntiInnerHornFactorization.innerFibrations (cofreeAnti.map p) := by
  intro X Y i hi
  obtain ⟨a⟩ := hi
  exact (cofreeAntiAdjunction.hasLiftingProperty_iff _ p).1
    (free_generator_underlying_inner a p hp)

/-- Every actual anti-inner-left map forgets to the entire native inner-left class. -/
theorem underlying_inner {X Y : AntiInvolutiveSSet.{u}} (i : X ⟶ Y)
    (hi : DaggerActualAntiInnerHornFactorization.innerAnodyne i) :
    DaggerNativeInnerHornFactorization.innerAnodyne i.hom := by
  intro A B p hp
  exact (cofreeAntiAdjunction.hasLiftingProperty_iff i p).2
    (hi (cofreeAnti.map p) (cofree_inner p hp))

/-- The unchanged underlying actual anti-inner-left map passes every original target test. -/
theorem anti_inner_weak {X Y : AntiInvolutiveSSet.{u}} (i : X ⟶ Y)
    (hi : DaggerActualAntiInnerHornFactorization.innerAnodyne i) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences i.hom :=
  DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _ (underlying_inner i hi)

/-- The actual original anti-involutive quasi-category replacement unit is mapping weak. -/
theorem unit_weak (X : AntiInvolutiveSSet.{u}) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (DaggerActualAntiInnerHornFactorization.unit.app X).hom :=
  anti_inner_weak _ (DaggerActualAntiInnerHornFactorization.unit_innerAnodyne X)

end
end DaggerActualAntiInnerJoyalMappingWeak
