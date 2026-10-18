import CountableCrossedWholeWitnessTarget
import OriginalBaseRankCountableLadder

/-! Every presentable source square factors through a genuine bounded whole inverse witness. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse DaggerSimplexInverseWitnessCategory
open DaggerRelativeInverseLadderData
universe u v w
namespace DaggerBoundedWitnessPresentationFactorization
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable {C : Type w} [Category.{v} C] [HasTerminal C] [HasColimitsOfSize.{u, u} C]
  [LocallySmall.{u} (Arrow C)] (R : C ⥤ SSet.{u})
  [R.IsCardinalAccessible Cardinal.aleph0.{u}]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
  (hω : Cardinal.aleph0 < κ)
  (hR : ∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ)
  {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ Arrow C} (c : Cocone F) (hc : IsColimit c)
  (d : SimplexInverseData (R.map c.pt.hom))
  (hF : ∀ j, IsCardinalPresentable (F.obj j) κ)

include hc hF hR hω

theorem factor (A : Arrow C) [IsCardinalPresentable A κ] (φ : A ⟶ c.pt) :
    ∃ Y : Witness R, IsCardinalPresentable Y.arrow κ ∧
      ∃ (a : A ⟶ Y.arrow) (b : Y ⟶ (⟨c.pt, d⟩ : Witness R)), a ≫ b.square = φ := by
  obtain ⟨i, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc φ
  obtain ⟨index, hi, e, he, hE⟩ :=
    DaggerOriginalBaseRankCountableLadder.exists_ladder R κ hR c hc d hF i
  have : HasColimitsOfShape ℕ C := HasColimitsOfShape.of_small C ℕ
  have : PreservesColimitsOfShape ℕ R := DaggerCountableReplacementPreservation.preserves R
  let D := index ⋙ F
  let q := colimit.cocone D
  let hq := colimit.isColimit D
  let Y := DaggerCountableCrossedWholeWitnessTarget.witness R q e hq
  have hY : IsCardinalPresentable Y.arrow κ := by
    letI (n : ℕ) : IsCardinalPresentable (D.obj n) κ := hE n
    exact DaggerCountableArrowPresentability.colimit_presentable q hq κ hω
  let b := DaggerCountableCrossedWholeWitnessTarget.target R q e hq (c.whisker index) d he
  have hι : eqToHom (congrArg F.obj hi.symm) ≫ c.ι.app (index.obj 0) = c.ι.app i := by
    cases hi
    simp
  refine ⟨Y, hY, a ≫ eqToHom (congrArg F.obj hi.symm) ≫ q.ι.app 0, b, ?_⟩
  change (a ≫ eqToHom (congrArg F.obj hi.symm) ≫ q.ι.app 0) ≫ hq.desc (c.whisker index) = φ
  rw [Category.assoc, Category.assoc, hq.fac]
  exact (congrArg (fun f ↦ a ≫ f) hι).trans ha

end
end DaggerBoundedWitnessPresentationFactorization
