import NativeWalkingRetractionMappingEquivalence
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Whole categorical interval cylinders from full monomorphism lifting

The interval is the existing walking-isomorphism nerve J. The endpoint subcomplex
contains both whole endpoint copies and uses every original simplicial operator.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualFreeAntiWalkingCategoricalCylinder
universe u
namespace DaggerNativeBoundaryCategoricalCylinder
noncomputable section
attribute [local instance] Classical.propDecidable

def time (q : SimplexCategoryᵒᵖ) (b : Bool) : J.{u}.obj q :=
  (SSet.const (ComposableArrows.mk₀ (parameterObject b)) : (Δ[0] : SSet.{u}) ⟶ J).app q
    (SSet.stdSimplex.const 0 0 q)

theorem time_map {q k : SimplexCategoryᵒᵖ} (α : q ⟶ k) (b : Bool) :
    J.{u}.map α (time q b) = time k b := rfl

theorem time_ne (q : SimplexCategoryᵒᵖ) : time.{u} q false ≠ time q true := by
  intro h
  have h01 := congrArg (fun t : J.{u}.obj q ↦ (ULift.down (t.obj 0)).as) h
  exact Bool.false_ne_true h01

def endpointSubcomplex (X : SSet.{u}) : (X ⊗ J.{u}).Subcomplex where
  obj q := {p | p.2 = time q false ∨ p.2 = time q true}
  map {q k} α := by
    intro p hp
    change J.map α p.2 = time k false ∨ J.map α p.2 = time k true
    rcases hp with h | h
    · exact Or.inl (by rw [h, time_map])
    · exact Or.inr (by rw [h, time_map])

def endpointMap {X : SSet.{u}} (r : X ⟶ X) : (endpointSubcomplex X).toSSet ⟶ X where
  app q p := if p.val.2 = time q false then r.app q p.val.1 else p.val.1
  naturality q k α := by
    funext p
    by_cases h : p.val.2 = time q false
    · have hm : J.map α p.val.2 = time k false := by rw [h, time_map]
      change (if J.map α p.val.2 = time k false
        then r.app k (X.map α p.val.1) else X.map α p.val.1) =
        X.map α (if p.val.2 = time q false then r.app q p.val.1 else p.val.1)
      rw [if_pos h, if_pos hm]
      exact congrFun (r.naturality α) p.val.1
    · have ht : p.val.2 = time q true := p.property.resolve_left h
      have hm : J.map α p.val.2 ≠ time k false := by
        rw [ht, time_map]
        exact (time_ne k).symm
      change (if J.map α p.val.2 = time k false
        then r.app k (X.map α p.val.1) else X.map α p.val.1) =
        X.map α (if p.val.2 = time q false then r.app q p.val.1 else p.val.1)
      rw [if_neg h, if_neg hm]

def endpointInclusion (X : SSet.{u}) (b : Bool) : X ⟶ (endpointSubcomplex X).toSSet where
  app q x := ⟨(x, time q b), by
    change time q b = time q false ∨ time q b = time q true
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl⟩
  naturality _ _ _ := rfl

theorem endpointInclusion_ι (X : SSet.{u}) (b : Bool) :
    endpointInclusion X b ≫ (endpointSubcomplex X).ι = intervalEndpoint X b := rfl

theorem endpointInclusion_zero {X : SSet.{u}} (r : X ⟶ X) :
    endpointInclusion X false ≫ endpointMap r = r := by
  ext q x
  change (if time q false = time q false then r.app q x else x) = r.app q x
  exact if_pos rfl

theorem endpointInclusion_one {X : SSet.{u}} (r : X ⟶ X) :
    endpointInclusion X true ≫ endpointMap r = 𝟙 X := by
  ext q x
  change (if time q true = time q false then r.app q x else x) = x
  exact if_neg (time_ne q).symm

theorem endpointMap_over {X Y : SSet.{u}} (f : X ⟶ Y) (r : X ⟶ X)
    (hr : r ≫ f = f) :
    endpointMap r ≫ f = (endpointSubcomplex X).ι ≫ fst X J ≫ f := by
  ext q p
  change f.app q (if p.val.2 = time q false then r.app q p.val.1 else p.val.1) =
    f.app q p.val.1
  split_ifs
  · exact congrFun (NatTrans.congr_app hr q) p.val.1
  · rfl

/-- Full monomorphism RLP gives the actual J-cylinder, including its exact projection. -/
theorem exists_cylinder {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f)
    (r : X ⟶ X) (hr : r ≫ f = f) :
    ∃ H : X ⊗ J.{u} ⟶ X,
      intervalEndpoint X false ≫ H = r ∧ intervalEndpoint X true ≫ H = 𝟙 X ∧
      H ≫ f = fst X J ≫ f := by
  have : HasLiftingProperty (endpointSubcomplex X).ι f := hf _ (show Mono (endpointSubcomplex X).ι from inferInstance)
  let sq : CommSq (endpointMap r) (endpointSubcomplex X).ι f (fst X J ≫ f) :=
    ⟨endpointMap_over f r hr⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← endpointInclusion_ι, Category.assoc, sq.fac_left, endpointInclusion_zero]
  · rw [← endpointInclusion_ι, Category.assoc, sq.fac_left, endpointInclusion_one]

end
end DaggerNativeBoundaryCategoricalCylinder
