import OriginalFixedObjectDaggerPullbacks

/-!
# Actual Homwise fibrations and trivial fibrations of the original pullbacks

Reuse native SSet model base change through exact four-leg IsPullback witnesses.
No model structure on either original fixed-object groupoid category is assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalSimplicialPullbackPairs DaggerOriginalFixedObjectGroupoidClasses
open DaggerOriginalFixedObjectStrictPullbacks DaggerOriginalFixedObjectDaggerPullbacks
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u
namespace DaggerOriginalFixedObjectPullbackFibrations
noncomputable section

/-- Native SSet fibrations pull back along any unchanged full simplicial map. -/
theorem pairedFst_fibration {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Fibration g] :
    Fibration (pairedFst f g) :=
  (fibration_iff _).2 (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (pairedIsPullback f g).flip ((fibration_iff g).1 inferInstance))

/-- Native trivial fibrations retain both exact model classes in the full pair pullback. -/
theorem pairedFst_trivialFibration {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Fibration g] [WeakEquivalence g] :
    Fibration (pairedFst f g) ∧ WeakEquivalence (pairedFst f g) :=
  (mem_trivialFibrations_iff _).1
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (pairedIsPullback f g).flip
      ((mem_trivialFibrations_iff g).2 ⟨inferInstance, inferInstance⟩))

/-- The actual ordinary strict first pullback projection is a Homwise fibration. -/
theorem strictFst_fibration {O : Type u} {C D E : FixedStrictGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) [Fibration G] : Fibration (strictFst F G) := by
  apply (strict_fibration_iff _).2
  intro x y
  have : Fibration (G.hom.map x y) := (strict_fibration_iff G).1 inferInstance x y
  exact pairedFst_fibration (F.hom.map x y) (G.hom.map x y)

/-- Both original strict model classes are retained by the same full first projection. -/
theorem strictFst_trivialFibration {O : Type u} {C D E : FixedStrictGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) [Fibration G] [WeakEquivalence G] :
    Fibration (strictFst F G) ∧ WeakEquivalence (strictFst F G) := by
  refine ⟨strictFst_fibration F G, (strict_weakEquivalence_iff _).2 ?_⟩
  intro x y
  have : Fibration (G.hom.map x y) := (strict_fibration_iff G).1 inferInstance x y
  have : WeakEquivalence (G.hom.map x y) :=
    (strict_weakEquivalence_iff G).1 inferInstance x y
  exact (pairedFst_trivialFibration (F.hom.map x y) (G.hom.map x y)).2

/-- The original dagger pullback projection is a fibration on each unchanged Hom. -/
theorem strictDaggerFst_fibration {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) [Fibration G] : Fibration (strictDaggerFst F G) := by
  apply (strictDagger_fibration_iff _).2
  intro x y
  have : Fibration (G.hom.underlying.map x y) :=
    (strictDagger_fibration_iff G).1 inferInstance x y
  exact pairedFst_fibration (F.hom.underlying.map x y) (G.hom.underlying.map x y)

/-- The original strict dagger pullback also retains both exact trivial-fibration classes. -/
theorem strictDaggerFst_trivialFibration {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) [Fibration G] [WeakEquivalence G] :
    Fibration (strictDaggerFst F G) ∧ WeakEquivalence (strictDaggerFst F G) := by
  refine ⟨strictDaggerFst_fibration F G, (strictDagger_weakEquivalence_iff _).2 ?_⟩
  intro x y
  have : Fibration (G.hom.underlying.map x y) :=
    (strictDagger_fibration_iff G).1 inferInstance x y
  have : WeakEquivalence (G.hom.underlying.map x y) :=
    (strictDagger_weakEquivalence_iff G).1 inferInstance x y
  exact (pairedFst_trivialFibration (F.hom.underlying.map x y)
    (G.hom.underlying.map x y)).2

end
end DaggerOriginalFixedObjectPullbackFibrations
