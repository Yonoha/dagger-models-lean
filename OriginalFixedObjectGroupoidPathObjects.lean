import OriginalFixedObjectGroupoidClasses

/-!
# Native good path objects of the original fixed-object strict groupoids

The original interval diagram is a Mathlib PathObject with the exact Homwise
weak class. Its paired map to Mathlib's categorical product is a fibration in
the exact Homwise fibration class. The product comparison retains both full
original projections. All Kan and interval factorization premises were proved
on the original strict groupoids; no ModelCategory existence is assumed here.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectGroupoidInterval DaggerOriginalFixedObjectProducts
open DaggerOriginalFixedObjectDaggerProducts DaggerOriginalFixedObjectProductLimits
open DaggerOriginalFixedObjectGroupoidClasses
open DaggerOriginalFixedObjectGroupoidHomPathFactorization
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u

namespace DaggerOriginalFixedObjectGroupoidPathObjects

noncomputable section

/-- The paired original endpoints are an actual functor to the same-O categorical product. -/
def strictPathPair {O : Type u} (C : FixedStrictGroupoids O) :
    strictCotensor Δ[1] C ⟶ strictProduct C C :=
  strictLift (strictEvaluation (intervalPoint 0) C) (strictEvaluation (intervalPoint 1) C)

/-- Pairing the actual endpoints gives a fibration in the exact original Homwise class. -/
theorem strictPathPair_fibration {O : Type u} (C : FixedStrictGroupoids O) :
    Fibration (strictPathPair C) := by
  apply (strict_fibration_iff _).2
  intro x y
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact endpointPair_fibration (C.obj.enriched.Hom x y)

/-- The original natural interval diagram is a native PathObject in the unchanged category. -/
def strictPath {O : Type u} (C : FixedStrictGroupoids O) : PathObject C where
  P := strictCotensor Δ[1] C
  p₀ := strictEvaluation (intervalPoint 0) C
  p₁ := strictEvaluation (intervalPoint 1) C
  ι := strictConstant Δ[1] C
  ι_p₀ := strictConstant_evaluation (intervalPoint 0) C
  ι_p₁ := strictConstant_evaluation (intervalPoint 1) C
  weakEquivalence_ι := (strict_weakEquivalence_iff _).2
    (fun x y ↦ strictConstant_hom_weakEquivalence C x y)

/-- The full original interval pair factors the actual categorical diagonal. -/
theorem strictConstant_pathPair {O : Type u} (C : FixedStrictGroupoids O) :
    strictConstant Δ[1] C ≫ strictPathPair C = strictDiagonal C := by
  apply ObjectProperty.hom_ext
  apply fixedHom_ext
  intro x y
  exact constant_endpointPair (C.obj.enriched.Hom x y)

/-- Mathlib's paired path map is the original endpoint pair followed by the product comparison. -/
theorem strictPath_p {O : Type u} (C : FixedStrictGroupoids O) :
    (strictPath C).p = strictPathPair C ≫ (strictProductIso C C).inv := by
  have h : (strictPath C).p ≫ (strictProductIso C C).hom = strictPathPair C := by
    apply BinaryFan.IsLimit.hom_ext (strictProductIsLimit C C)
    · change ((strictPath C).p ≫ (strictProductIso C C).hom) ≫ strictFst C C =
        strictPathPair C ≫ strictFst C C
      rw [Category.assoc, strictProductIso_hom_fst]
      change prod.lift (strictEvaluation (intervalPoint 0) C)
          (strictEvaluation (intervalPoint 1) C) ≫ prod.fst =
        strictLift (strictEvaluation (intervalPoint 0) C)
          (strictEvaluation (intervalPoint 1) C) ≫ strictFst C C
      rw [prod.lift_fst, strictLift_fst]
    · change ((strictPath C).p ≫ (strictProductIso C C).hom) ≫ strictSnd C C =
        strictPathPair C ≫ strictSnd C C
      rw [Category.assoc, strictProductIso_hom_snd]
      change prod.lift (strictEvaluation (intervalPoint 0) C)
          (strictEvaluation (intervalPoint 1) C) ≫ prod.snd =
        strictLift (strictEvaluation (intervalPoint 0) C)
          (strictEvaluation (intervalPoint 1) C) ≫ strictSnd C C
      rw [prod.lift_snd, strictLift_snd]
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The native path object is good for the exact original Homwise fibration class. -/
instance strictPath_isGood {O : Type u} (C : FixedStrictGroupoids O) :
    (strictPath C).IsGood where
  fibration_p := by
    rw [strictPath_p]
    apply (strict_fibration_iff _).2
    intro x y
    have : Fibration ((strictPathPair C).hom.map x y) :=
      (strict_fibration_iff _).1 (strictPathPair_fibration C) x y
    have : Fibration ((strictProductIso C C).inv.hom.map x y) := by
      change Fibration ((strictHomEvaluation O x y).map (strictProductIso C C).inv)
      infer_instance
    change Fibration ((strictPathPair C).hom.map x y ≫
      (strictProductIso C C).inv.hom.map x y)
    infer_instance

/-- Pair both original dagger endpoints as an actual strict dagger functor. -/
def strictDaggerPathPair {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    strictDaggerCotensor Δ[1] C ⟶ strictDaggerProduct C C :=
  strictDaggerLift (strictDaggerEvaluation (intervalPoint 0) C)
    (strictDaggerEvaluation (intervalPoint 1) C)

/-- The actual dagger endpoint pair is a fibration in the exact original Homwise class. -/
theorem strictDaggerPathPair_fibration {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    Fibration (strictDaggerPathPair C) := by
  apply (strictDagger_fibration_iff _).2
  intro x y
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact endpointPair_fibration (C.obj.underlying.enriched.Hom x y)

/-- The actual strict dagger interval diagram is a native PathObject on the same fixed O. -/
def strictDaggerPath {O : Type u} (C : FixedStrictDaggerGroupoids O) : PathObject C where
  P := strictDaggerCotensor Δ[1] C
  p₀ := strictDaggerEvaluation (intervalPoint 0) C
  p₁ := strictDaggerEvaluation (intervalPoint 1) C
  ι := strictDaggerConstant Δ[1] C
  ι_p₀ := strictDaggerConstant_evaluation (intervalPoint 0) C
  ι_p₁ := strictDaggerConstant_evaluation (intervalPoint 1) C
  weakEquivalence_ι := (strictDagger_weakEquivalence_iff _).2
    (fun x y ↦ strictDaggerConstant_hom_weakEquivalence C x y)

/-- The complete dagger interval diagram factors the original categorical diagonal. -/
theorem strictDaggerConstant_pathPair {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    strictDaggerConstant Δ[1] C ≫ strictDaggerPathPair C = strictDaggerDiagonal C := by
  apply ObjectProperty.hom_ext
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro x y
  exact constant_endpointPair (C.obj.underlying.enriched.Hom x y)

/-- Mathlib's dagger path pair retains both full original projections under the comparison. -/
theorem strictDaggerPath_p {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    (strictDaggerPath C).p = strictDaggerPathPair C ≫ (strictDaggerProductIso C C).inv := by
  have h : (strictDaggerPath C).p ≫ (strictDaggerProductIso C C).hom =
      strictDaggerPathPair C := by
    apply BinaryFan.IsLimit.hom_ext (strictDaggerProductIsLimit C C)
    · change ((strictDaggerPath C).p ≫ (strictDaggerProductIso C C).hom) ≫
          strictDaggerFst C C = strictDaggerPathPair C ≫ strictDaggerFst C C
      rw [Category.assoc, strictDaggerProductIso_hom_fst]
      change prod.lift (strictDaggerEvaluation (intervalPoint 0) C)
          (strictDaggerEvaluation (intervalPoint 1) C) ≫ prod.fst =
        strictDaggerLift (strictDaggerEvaluation (intervalPoint 0) C)
          (strictDaggerEvaluation (intervalPoint 1) C) ≫ strictDaggerFst C C
      rw [prod.lift_fst, strictDaggerLift_fst]
    · change ((strictDaggerPath C).p ≫ (strictDaggerProductIso C C).hom) ≫
          strictDaggerSnd C C = strictDaggerPathPair C ≫ strictDaggerSnd C C
      rw [Category.assoc, strictDaggerProductIso_hom_snd]
      change prod.lift (strictDaggerEvaluation (intervalPoint 0) C)
          (strictDaggerEvaluation (intervalPoint 1) C) ≫ prod.snd =
        strictDaggerLift (strictDaggerEvaluation (intervalPoint 0) C)
          (strictDaggerEvaluation (intervalPoint 1) C) ≫ strictDaggerSnd C C
      rw [prod.lift_snd, strictDaggerLift_snd]
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual native dagger path object is good for the original Homwise fibrations. -/
instance strictDaggerPath_isGood {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    (strictDaggerPath C).IsGood where
  fibration_p := by
    rw [strictDaggerPath_p]
    apply (strictDagger_fibration_iff _).2
    intro x y
    have : Fibration ((strictDaggerPathPair C).hom.underlying.map x y) :=
      (strictDagger_fibration_iff _).1 (strictDaggerPathPair_fibration C) x y
    have : Fibration ((strictDaggerProductIso C C).inv.hom.underlying.map x y) := by
      change Fibration ((strictDaggerHomEvaluation O x y).map
        (strictDaggerProductIso C C).inv)
      infer_instance
    change Fibration ((strictDaggerPathPair C).hom.underlying.map x y ≫
      (strictDaggerProductIso C C).inv.hom.underlying.map x y)
    infer_instance

end

end DaggerOriginalFixedObjectGroupoidPathObjects
