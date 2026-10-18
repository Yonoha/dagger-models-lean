import WholeWitnessHomStageLifts
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Whole inverse witnesses are cardinal-presentable under full source bounds

Surjectivity lifts every original arrow factorization with all chosen data.
Injectivity is reflected to the original arrow category by the faithful
projection. This is object presentability, not a small generator theorem.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
universe u v w
namespace DaggerWholeWitnessPresentability
noncomputable section

variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

def homIsColimit {J : Type u} [SmallCategory J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c)
    (X : Witness R) [IsCardinalPresentable X.arrow κ]
    [IsCardinalPresentable (R.obj X.arrow.right) κ]
    (hX : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ) :
    IsColimit ((coyoneda.obj (op X)).mapCocone c) := by
  apply Types.FilteredColimit.isColimitOf
  · intro h
    obtain ⟨j, f, hf⟩ := DaggerWholeWitnessHomStageLifts.hom_factors_of_isColimit
      R κ hc X hX h
    exact ⟨j, f, hf.symm⟩
  · intro i j f g hfg
    have he := congrArg (fun t : X ⟶ c.pt ↦ t.square) hfg
    obtain ⟨k, s, t, ht⟩ := IsCardinalPresentable.exists_eq_of_isColimit κ
      (isColimitOfPreserves (forget R) hc) f.square g.square he
    exact ⟨k, s, t, Hom.ext R ht⟩

theorem witness_presentable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits C κ] [R.IsCardinalAccessible κ]
    (X : Witness R) [IsCardinalPresentable X.arrow κ]
    [IsCardinalPresentable (R.obj X.arrow.right) κ]
    (hX : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ) : IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ := by
    have : PreservesColimitsOfShape J R :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible R κ J
    exact ⟨preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit _) (homIsColimit R κ (colimit.isColimit _) X hX)⟩

end
end DaggerWholeWitnessPresentability
