import OriginalFixedObjectModelProperties

/-!
# Exact original trivial fibrations under pullbacks and binary products

The original Hom evaluations take every pullback to a simplicial pullback. Native
simplicial trivial-fibration base change therefore applies without assuming an
ordinary model structure. Binary products use the two native product pullback squares.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectPullbackEvaluation
open scoped DaggerOriginalFixedObjectGroupoidClasses SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalFixedObjectTrivialFibrationProducts
noncomputable section

/-- Exact original trivial fibrations are detected on all unchanged Hom maps. -/
theorem strict_trivialFibration_iff {O : Type u} {C D : FixedStrictGroupoids O}
    (F : C ⟶ D) : trivialFibrations (FixedStrictGroupoids O) F ↔
      ∀ x y : O, trivialFibrations SSet.{u} (F.hom.map x y) := by
  rw [mem_trivialFibrations_iff, strict_fibration_iff, strict_weakEquivalence_iff]
  constructor
  · rintro ⟨hf, hw⟩ x y
    exact (mem_trivialFibrations_iff _).2 ⟨hf x y, hw x y⟩
  · intro h
    exact ⟨fun x y ↦ ((mem_trivialFibrations_iff _).1 (h x y)).1,
      fun x y ↦ ((mem_trivialFibrations_iff _).1 (h x y)).2⟩

/-- Every actual original pullback preserves the entire original trivial-fibration class. -/
instance strictTrivialFibBaseChange (O : Type u) :
    (trivialFibrations (FixedStrictGroupoids O)).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    apply (strict_trivialFibration_iff _).2
    intro x y
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (strict_map_isPullback x y sq) ((strict_trivialFibration_iff _).1 hg x y)

/-- Composition and identities retain the exact original trivial-fibration class. -/
instance strictTrivialFibMultiplicative (O : Type u) :
    (trivialFibrations (FixedStrictGroupoids O)).IsMultiplicative := by
  change (strictFibrations O ⊓ strictWeakEquivalences O).IsMultiplicative
  unfold strictFibrations strictWeakEquivalences
  infer_instance

/-- The actual native binary product map preserves both original Homwise conditions. -/
theorem strict_prodMap_trivialFibration {O : Type u} {A B C D : FixedStrictGroupoids O}
    (F : A ⟶ B) (G : C ⟶ D)
    (hF : trivialFibrations (FixedStrictGroupoids O) F)
    (hG : trivialFibrations (FixedStrictGroupoids O) G) :
    trivialFibrations (FixedStrictGroupoids O) (prod.map F G) := by
  let P := trivialFibrations (FixedStrictGroupoids O)
  have h₁ : P (prod.map F (𝟙 C)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id F C) hF
  have hs : P (prod.map G (𝟙 B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id G B) hG
  have h₂ : P (prod.map (𝟙 B) G) := by
    have h := P.comp_mem _ _
      (P.comp_mem _ _ (P.of_isIso (prod.braiding B C).hom) hs)
      (P.of_isIso (prod.braiding D B).hom)
    convert h using 1
    apply prod.hom_ext <;> simp
  have h := P.comp_mem _ _ h₁ h₂
  convert h using 1
  apply prod.hom_ext <;> simp

end
end DaggerOriginalFixedObjectTrivialFibrationProducts
