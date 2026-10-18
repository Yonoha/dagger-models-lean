import OriginalFixedObjectPullbackEvaluation

/-!
# Native model-recognition properties of the exact original Homwise classes

Every original pullback is detected on the unchanged Hom maps. Reuse SSet
base change, composition and retracts and expose the exact native classes.
No ModelCategory instance on the original categories is assumed.
-/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectPullbackEvaluation
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u
namespace DaggerOriginalFixedObjectModelProperties
noncomputable section

/-- Native two-out-of-three for the exact original ordinary weak class. -/
instance strictWeakTwoOut (O : Type u) :
    (weakEquivalences (FixedStrictGroupoids O)).HasTwoOutOfThreeProperty := by
  change (strictWeakEquivalences O).HasTwoOutOfThreeProperty
  infer_instance

/-- Native retract stability for the exact original ordinary weak class. -/
instance strictWeakRetracts (O : Type u) :
    (weakEquivalences (FixedStrictGroupoids O)).IsStableUnderRetracts := by
  change (strictWeakEquivalences O).IsStableUnderRetracts
  infer_instance

/-- Native composition and identity for the exact original ordinary fibration class. -/
instance strictFibMultiplicative (O : Type u) :
    (fibrations (FixedStrictGroupoids O)).IsMultiplicative := by
  change (strictFibrations O).IsMultiplicative
  infer_instance

/-- Native retract stability for the exact original ordinary fibration class. -/
instance strictFibRetracts (O : Type u) :
    (fibrations (FixedStrictGroupoids O)).IsStableUnderRetracts := by
  change (strictFibrations O).IsStableUnderRetracts
  unfold strictFibrations
  infer_instance

/-- Every actual ordinary pullback retains the exact original fibration class. -/
instance strictFibBaseChange (O : Type u) :
    (fibrations (FixedStrictGroupoids O)).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    apply (fibration_iff g').1
    apply (strict_fibration_iff g').2
    intro x y
    have hh : Fibration (g.hom.map x y) :=
      (strict_fibration_iff g).1 ((fibration_iff g).2 hg) x y
    exact (fibration_iff _).2 (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (strict_map_isPullback x y sq) ((fibration_iff (g.hom.map x y)).1 hh))

/-- Native two-out-of-three for the exact original dagger weak class. -/
instance strictDaggerWeakTwoOut (O : Type u) :
    (weakEquivalences (FixedStrictDaggerGroupoids O)).HasTwoOutOfThreeProperty := by
  change (strictDaggerWeakEquivalences O).HasTwoOutOfThreeProperty
  infer_instance

/-- Native retract stability for the exact original dagger weak class. -/
instance strictDaggerWeakRetracts (O : Type u) :
    (weakEquivalences (FixedStrictDaggerGroupoids O)).IsStableUnderRetracts := by
  change (strictDaggerWeakEquivalences O).IsStableUnderRetracts
  infer_instance

/-- Native composition and identity for the exact original dagger fibration class. -/
instance strictDaggerFibMultiplicative (O : Type u) :
    (fibrations (FixedStrictDaggerGroupoids O)).IsMultiplicative := by
  change (strictDaggerFibrations O).IsMultiplicative
  infer_instance

/-- Native retract stability for the exact original dagger fibration class. -/
instance strictDaggerFibRetracts (O : Type u) :
    (fibrations (FixedStrictDaggerGroupoids O)).IsStableUnderRetracts := by
  change (strictDaggerFibrations O).IsStableUnderRetracts
  unfold strictDaggerFibrations
  infer_instance

/-- Every actual dagger pullback retains the exact unchanged Homwise fibration class. -/
instance strictDaggerFibBaseChange (O : Type u) :
    (fibrations (FixedStrictDaggerGroupoids O)).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    apply (fibration_iff g').1
    apply (strictDagger_fibration_iff g').2
    intro x y
    have hh : Fibration (g.hom.underlying.map x y) :=
      (strictDagger_fibration_iff g).1 ((fibration_iff g).2 hg) x y
    exact (fibration_iff _).2 (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (strictDagger_map_isPullback x y sq) ((fibration_iff (g.hom.underlying.map x y)).1 hh))

end
end DaggerOriginalFixedObjectModelProperties
