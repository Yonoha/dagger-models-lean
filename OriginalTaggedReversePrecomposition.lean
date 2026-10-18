import OriginalTaggedReverseQuotient
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Opposites

/-!
# Precomposition along the actual tagged-reversal quotient

The tagged quotient is full and bijective on objects, but is not faithful.
Nevertheless its opposite induces a fully faithful functor on diagrams with
arbitrary categorical values. The inverse on natural transformations is
constructed from the actual components, rather than a replacement quotient.
-/

set_option autoImplicit false

open CategoryTheory Opposite

universe u v

namespace DaggerModels.OriginalTaggedReversePrecomposition

open DaggerModels.OriginalTaggedReverseSimplex
open TaggedReverseSimplex

/-- Every actual monotone-or-antitone map has a tagged representative. -/
instance qTag_full : qTag.Full where
  map_surjective := by
    intro X Y f
    exact qMap_surjective X Y f

/-- Restrict a diagram along the opposite of the actual `qTag`. -/
def precomposition (C : Type u) [Category.{v} C] :
    (ReverseSimplexᵒᵖ ⥤ C) ⥤ (TaggedReverseSimplexᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj qTag.op

variable {C : Type u} [Category.{v} C]

/-- Lift a natural transformation by its components on the same finite ordinals. -/
noncomputable def natLift {F G : ReverseSimplexᵒᵖ ⥤ C}
    (α : qTag.op ⋙ F ⟶ qTag.op ⋙ G) : F ⟶ G where
  app X := α.app (op (TaggedReverseSimplex.mk X.unop.len))
  naturality X Y f := by
    cases X with
    | op x =>
      cases Y with
      | op y =>
        let g : (op (TaggedReverseSimplex.mk x.len) : TaggedReverseSimplexᵒᵖ) ⟶
            (op (TaggedReverseSimplex.mk y.len) : TaggedReverseSimplexᵒᵖ) :=
          qTag.op.preimage f
        have hg : qTag.op.map g = f := qTag.op.map_preimage
          (X := op (TaggedReverseSimplex.mk x.len))
          (Y := op (TaggedReverseSimplex.mk y.len)) f
        have hn := α.naturality g
        simpa only [Functor.comp_map, hg] using hn

/-- Restricting the lifted transformation recovers every original component. -/
theorem natLift_fac {F G : ReverseSimplexᵒᵖ ⥤ C}
    (α : qTag.op ⋙ F ⟶ qTag.op ⋙ G) :
    (precomposition C).map (natLift α) = α := by
  ext X
  cases X with
  | op x =>
    rfl

/-- A transformation on the target is determined by its tagged restriction. -/
theorem natLift_whisker {F G : ReverseSimplexᵒᵖ ⥤ C} (τ : F ⟶ G) :
    natLift ((precomposition C).map τ) = τ := by
  ext X
  cases X with
  | op x =>
    rfl

/-- Every transformation between restricted diagrams descends. -/
instance precomposition_full : (precomposition C).Full where
  map_surjective α := ⟨natLift α, natLift_fac α⟩

/-- The components after restriction determine a transformation uniquely. -/
instance precomposition_faithful : (precomposition C).Faithful where
  map_injective := by
    intro F G τ σ h
    calc
      τ = natLift ((precomposition C).map τ) := (natLift_whisker τ).symm
      _ = natLift ((precomposition C).map σ) := congrArg natLift h
      _ = σ := natLift_whisker σ

/-- Precomposition is fully faithful for every target category. -/
noncomputable def precomposition_fullyFaithful :
    (precomposition C).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (precomposition C)

end DaggerModels.OriginalTaggedReversePrecomposition
