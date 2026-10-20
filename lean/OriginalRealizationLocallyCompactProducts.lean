import OriginalRealizationMonomorphismCofibrations
import OriginalEC2GeneratorLifting
import TopCatModelCategory.TopCat.ToTopProducts

/-!
# Actual realization products with the original locally compact parameter

The existing product comparison is an isomorphism whenever the realization of
the parameter is locally compact. Naturality retains the original product map.
The resulting underlying cofibration assertion does not substitute for the
remaining Borel action cofibration assertion.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerOriginalRealizationMonomorphismCofibrations
open scoped TopCat.modelCategory SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalRealizationLocallyCompactProducts

noncomputable section

/-- The original realization preserves this product with a locally compact realized parameter. -/
instance realization_preserves_pair (X K : SSet.{u}) [LocallyCompactSpace (SSet.toTop.obj K)] :
    PreservesLimit (pair X K) SSet.toTop := by
  infer_instance

/-- The actual native comparison identifies realization of the product with the ordinary product. -/
def realizationProductIso (X K : SSet.{u}) [LocallyCompactSpace (SSet.toTop.obj K)] :
    SSet.toTop.obj (X ⊗ K) ≅ SSet.toTop.obj X ⊗ SSet.toTop.obj K :=
  asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X K)

/-- The comparison retains the original first projection. -/
theorem realizationProductIso_hom_fst (X K : SSet.{u})
    [LocallyCompactSpace (SSet.toTop.obj K)] :
    (realizationProductIso X K).hom ≫ fst _ _ = SSet.toTop.map (fst X K) :=
  CartesianMonoidalCategory.prodComparison_fst SSet.toTop X K

/-- The comparison retains the original second projection. -/
theorem realizationProductIso_hom_snd (X K : SSet.{u})
    [LocallyCompactSpace (SSet.toTop.obj K)] :
    (realizationProductIso X K).hom ≫ snd _ _ = SSet.toTop.map (snd X K) :=
  CartesianMonoidalCategory.prodComparison_snd SSet.toTop X K

/-- Naturality compares exactly the original simplicial and topological product arrows. -/
theorem realizationProductIso_naturality {X Y K L : SSet.{u}}
    [LocallyCompactSpace (SSet.toTop.obj K)] [LocallyCompactSpace (SSet.toTop.obj L)]
    (f : X ⟶ Y) (i : K ⟶ L) :
    SSet.toTop.map (f ⊗ₘ i) ≫ (realizationProductIso Y L).hom =
      (realizationProductIso X K).hom ≫ (SSet.toTop.map f ⊗ₘ SSet.toTop.map i) :=
  CartesianMonoidalCategory.prodComparison_natural SSet.toTop f i

/-- The original right-factor arrow is identified by an actual arrow isomorphism. -/
def realizationRightProductArrowIso (X : SSet.{u}) {K L : SSet.{u}}
    [LocallyCompactSpace (SSet.toTop.obj K)] [LocallyCompactSpace (SSet.toTop.obj L)]
    (i : K ⟶ L) :
    Arrow.mk (SSet.toTop.map (X ◁ i)) ≅ Arrow.mk (SSet.toTop.obj X ◁ SSet.toTop.map i) :=
  Arrow.isoMk (realizationProductIso X K) (realizationProductIso X L) (by
    simpa using (realizationProductIso_naturality (𝟙 X) i).symm)

/-- The original right product of a simplicial monomorphism is still a monomorphism. -/
theorem rightProduct_mono (X : SSet.{u}) {K L : SSet.{u}} (i : K ⟶ L) [Mono i] :
    Mono (X ◁ i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  rintro ⟨x, k⟩ ⟨y, l⟩ h
  change (x, i.app n k) = (y, i.app n l) at h
  have hx : x = y := congrArg (fun p : X.obj n × L.obj n ↦ p.1) h
  have hk : i.app n k = i.app n l := congrArg (fun p : X.obj n × L.obj n ↦ p.2) h
  exact Prod.ext hx (((CategoryTheory.mono_iff_injective (i.app n)).1 inferInstance) hk)

/-- The original right product of a simplicial monomorphism realizes to an underlying cofibration.
-/
theorem realization_rightProduct_cofibration (X : SSet.{u}) {K L : SSet.{u}}
    [LocallyCompactSpace (SSet.toTop.obj K)] [LocallyCompactSpace (SSet.toTop.obj L)]
    (i : K ⟶ L) [Mono i] : Cofibration (SSet.toTop.obj X ◁ SSet.toTop.map i) := by
  have : Mono (X ◁ i) := rightProduct_mono X i
  have h : Cofibration (SSet.toTop.map (X ◁ i)) := realization_map_mono_cofibration _
  rw [HomotopicalAlgebra.cofibration_iff] at h ⊢
  exact (MorphismProperty.arrow_mk_iso_iff _ (realizationRightProductArrowIso X i)).1 h

end

end DaggerOriginalRealizationLocallyCompactProducts
