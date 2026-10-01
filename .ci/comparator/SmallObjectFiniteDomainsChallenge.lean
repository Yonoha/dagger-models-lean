import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Presentable.Finite

/-! The finite-domain small object argument used for Part I's actual I-dagger.
All category, hom and smallness universes remain independent in this statement. -/
set_option warningAsError false

open CategoryTheory Limits MorphismProperty

universe w v u

namespace DaggerModels.SmallObjectFiniteDomains

variable {C : Type u} [Category.{v} C]

theorem hasSmallObjectArgument [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{w} I]
    (hfp : ∀ {A B : C} (i : A ⟶ B), I i → IsFinitelyPresentable.{w} A) :
    MorphismProperty.HasSmallObjectArgument.{w} I := by sorry

end DaggerModels.SmallObjectFiniteDomains
