import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.Limits

/-! A small family with finitely presentable domains permits the actual Mathlib
small object argument in a locally small category with the required small colimits.
The auxiliary universe is independent of the category and hom universes. -/

open CategoryTheory Limits Opposite MorphismProperty

universe w v u

namespace DaggerModels.SmallObjectFiniteDomains

attribute [local instance] Cardinal.fact_isRegular_aleph0

noncomputable local instance aleph0OrdOrderBot : OrderBot Cardinal.aleph0.{w}.ord.ToType :=
  Cardinal.toTypeOrderBot Cardinal.aleph0_ne_zero

variable {C : Type u} [Category.{v} C]

/-- Two small classes form a small union, without closing under isomorphisms. -/
theorem isSmall_sup (I J : MorphismProperty C)
    [MorphismProperty.IsSmall.{w} I] [MorphismProperty.IsSmall.{w} J] :
    MorphismProperty.IsSmall.{w} (I ⊔ J) := by
  let φ : I.toSet ⊕ J.toSet → (I ⊔ J).toSet := Sum.elim
    (fun i ↦ ⟨i.val, Or.inl i.property⟩) (fun j ↦ ⟨j.val, Or.inr j.property⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨f, hf⟩
    rcases hf with hf | hf
    · exact ⟨Sum.inl ⟨f, hf⟩, rfl⟩
    · exact ⟨Sum.inr ⟨f, hf⟩, rfl⟩
  exact ⟨small_of_surjective hφ⟩

/-- An initial object is finitely presentable relative to any locally-small universe. -/
theorem initial_isFinitelyPresentable [LocallySmall.{w} C] {A : C} (hA : IsInitial A) :
    IsFinitelyPresentable.{w} A := by
  have (j : Discrete PEmpty) :
      IsCardinalPresentable ((Functor.empty C).obj j) Cardinal.aleph0.{w} := j.as.elim
  exact isCardinalPresentable_of_isColimit (asEmptyCocone A) hA Cardinal.aleph0
    (hasCardinalLT_of_finite _ Cardinal.aleph0 le_rfl)

/-- At ℵ₀, finitely presentable domains satisfy the actual relative-cell colimit condition. -/
theorem isCardinalForSmallObjectArgument_aleph0
    [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{w} I]
    (hfp : ∀ {A B : C} (i : A ⟶ B), I i → IsFinitelyPresentable.{w} A) :
    I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w} where
  preservesColimit {A B X Y} i hi f hf := by
    have := hfp i hi
    have := preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0.{w}
      Cardinal.aleph0.{w}.ord.ToType
    infer_instance

/-- The small object argument has no extra cardinal or presentability premise after this bridge. -/
theorem hasSmallObjectArgument [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{w} I]
    (hfp : ∀ {A B : C} (i : A ⟶ B), I i → IsFinitelyPresentable.{w} A) :
    MorphismProperty.HasSmallObjectArgument.{w} I :=
  ⟨⟨Cardinal.aleph0, inferInstance, inferInstance,
    isCardinalForSmallObjectArgument_aleph0 I hfp⟩⟩

end DaggerModels.SmallObjectFiniteDomains
