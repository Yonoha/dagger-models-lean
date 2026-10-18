import OriginalLocallyCompactActionTensorAdjunction
import OriginalBorelModelCategory

/-!
# Relative function maps for the original realized inclusions

The existing realized union product proves the actual pushout-tensor
cofibration. The native parametrized lifting equivalence then proves that the
relative function map of an original trivial fibration is again a trivial
fibration. This uses only local compactness of the original parameter and its
subcomplex, and applies in every universe.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalRealizedPushoutTensorCofibrations
open DaggerOriginalLocallyCompactTensorAdjunction
open DaggerOriginalLocallyCompactActionTensorAdjunction DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action

universe u

namespace DaggerOriginalRealizedRelativeFunctionTrivialFibrations

noncomputable section

/-- Braiding retains an actual native TopCat pushout tensor with the factors interchanged. -/
@[simps]
def flipTensor {A B K L : TopCat.{u}} {i : A ⟶ B} {j : K ⟶ L}
    (h : Functor.PushoutObjObj (curriedTensor TopCat) i j) :
    Functor.PushoutObjObj (curriedTensor TopCat) j i where
  pt := h.pt
  inl := (β_ _ _).hom ≫ h.inr
  inr := (β_ _ _).hom ≫ h.inl
  isPushout := h.isPushout.flip.of_iso (β_ _ _) (β_ _ _) (β_ _ _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- The braided pushout arrow is the original arrow followed by its native braiding. -/
theorem flipTensor_ι {A B K L : TopCat.{u}} {i : A ⟶ B} {j : K ⟶ L}
    (h : Functor.PushoutObjObj (curriedTensor TopCat) i j) :
    (flipTensor h).ι = h.ι ≫ (β_ _ _).hom := by
  apply (flipTensor h).isPushout.hom_ext
  · rw [Functor.PushoutObjObj.inl_ι]
    simp
  · rw [Functor.PushoutObjObj.inr_ι]
    simp

variable {Y : SSet.{u}} (B : Y.Subcomplex)
variable [LocallyCompactSpace (SSet.toTop.obj Y)]
  [LocallyCompactSpace (SSet.toTop.obj B.toSSet)]

/-- The original realization, bundled only with its already proved local compactness. -/
def realizedParameterTarget : LocallyCompactTopCat.{u} :=
  ⟨SSet.toTop.obj Y, by
    change LocallyCompactSpace (SSet.toTop.obj Y)
    infer_instance⟩

/-- The original subcomplex realization, bundled with its already proved local compactness. -/
def realizedParameterSource : LocallyCompactTopCat.{u} :=
  ⟨SSet.toTop.obj B.toSSet, by
    change LocallyCompactSpace (SSet.toTop.obj B.toSSet)
    infer_instance⟩

/-- The parameter-category arrow is literally the original realized subcomplex inclusion. -/
def realizedParameterInclusion : realizedParameterSource B ⟶ realizedParameterTarget (Y := Y) :=
  ⟨SSet.toTop.map B.ι⟩

/-- The actual braided realized union supplies the restricted native tensor pushout. -/
def locallyCompactRealizedUnionProd {X : SSet.{u}} (A : X.Subcomplex) :
    Functor.PushoutObjObj locallyCompactTensor (realizedParameterInclusion B)
      (SSet.toTop.map A.ι) where
  pt := (flipTensor (realizedUnionProd A B)).pt
  inl := (flipTensor (realizedUnionProd A B)).inl
  inr := (flipTensor (realizedUnionProd A B)).inr
  isPushout := (flipTensor (realizedUnionProd A B)).isPushout

/-- Its native arrow is the literal original realized union arrow followed by the braiding. -/
theorem locallyCompactRealizedUnionProd_ι {X : SSet.{u}} (A : X.Subcomplex) :
    (locallyCompactRealizedUnionProd B A).ι =
      (realizedUnionProd A B).ι ≫ (β_ _ _).hom :=
  flipTensor_ι (realizedUnionProd A B)

/-- The actual tensor pushout arrow is a native cofibration. -/
theorem locallyCompactRealizedUnionProd_cofibration {X : SSet.{u}} (A : X.Subcomplex) :
    Cofibration (locallyCompactRealizedUnionProd B A).ι := by
  rw [locallyCompactRealizedUnionProd_ι]
  have : Cofibration (realizedUnionProd A B).ι := realizedUnionProd_cofibration A B
  infer_instance

/-- Relative function maps preserve the native trivial-fibration class at these parameters. -/
theorem relativeFunction_trivialFibration {X Z : TopCat.{u}} (p : X ⟶ Z)
    [Fibration p] [WeakEquivalence p]
    (r : Functor.PullbackObjObj locallyCompactIhom (realizedParameterInclusion B) p) :
    trivialFibrations TopCat.{u} r.π := by
  have hp : TopCat.modelCategory.I.rlp r.π := by
    rintro _ _ _ ⟨n⟩
    have : Cofibration (locallyCompactRealizedUnionProd B (SSet.boundary n)).ι :=
      locallyCompactRealizedUnionProd_cofibration B _
    exact (locallyCompactAdjunction.hasLiftingProperty_iff
      (locallyCompactRealizedUnionProd B (SSet.boundary n)) r).1 inferInstance
  have h : TopCat.modelCategory.I.rlp = trivialFibrations TopCat.{u} :=
    TopCat.modelCategory.packageTopCat.I_rlp_eq_trivialFibrations
  exact h ▸ hp

/-- The same relative function map is a trivial fibration in the literal Borel action model. -/
theorem relativeActionFunction_trivialFibration {X Z : Action TopCat.{u} C2.{u}}
    (p : X ⟶ Z) [Fibration p] [WeakEquivalence p]
    (r : Functor.PullbackObjObj locallyCompactActionIhom (realizedParameterInclusion B) p) :
    trivialFibrations (Action TopCat.{u} C2.{u}) r.π := by
  have : Fibration p.hom := (fibration_iff_underlying p).1 inferInstance
  have : WeakEquivalence p.hom := (weakEquivalence_iff_underlying p).1 inferInstance
  have h := relativeFunction_trivialFibration B p.hom
    (underlyingActionPullback _ p r)
  rw [underlyingActionPullback_π] at h
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 h
  exact (mem_trivialFibrations_iff _).2
    ⟨(fibration_iff_underlying _).2 hf, (weakEquivalence_iff_underlying _).2 hw⟩

end

end DaggerOriginalRealizedRelativeFunctionTrivialFibrations
