import RelativeInverseLadderRealization
import RelativeInverseBasePresentability
import CountableArrowPresentability
import CountableReplacementPreservation

/-! Original presentable base stages yield an exact whole-witness countable ladder at that rank. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseLadderData
universe u v w
namespace DaggerOriginalBaseRankCountableLadder

variable {C : Type w} [Category.{v} C] [HasTerminal C] [HasColimitsOfSize.{u, u} C]
  (R : C ⥤ SSet.{u}) (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
  (hR : ∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ)
  {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ Arrow C} (c : Cocone F) (hc : IsColimit c)
  (d : SimplexInverseData (R.map c.pt.hom))
  (hF : ∀ j, IsCardinalPresentable (F.obj j) κ)

include hR hc hF
theorem exists_ladder (i : J) :
    ∃ (index : ℕ ⥤ J), index.obj 0 = i ∧
      ∃ e : Ladder R (index ⋙ F), Over R (index ⋙ F) e (c.whisker index) d ∧
        ∀ n, IsCardinalPresentable ((index ⋙ F).obj n) κ := by
  have : PreservesColimitsOfShape J R := R.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have hX : ∀ j, IsCardinalPresentable (R.obj (F.obj j).left) κ ∧
      IsCardinalPresentable (R.obj (F.obj j).right) κ := by
    intro j
    have : IsCardinalPresentable (F.obj j) κ := hF j
    exact ⟨hR _ (DaggerArrowEndpointPresentability.left_presentable C κ (F.obj j)),
      hR _ (DaggerArrowEndpointPresentability.right_presentable C κ (F.obj j))⟩
  exact ⟨DaggerRelativeInverseCountableLadder.index R c d κ hc hX i,
    DaggerRelativeInverseCountableLadder.index_zero R c d κ hc hX i,
    DaggerRelativeInverseLadderRealization.ladder R c d κ hc hX i,
    DaggerRelativeInverseLadderRealization.over R c d κ hc hX i,
    fun n ↦ hF _⟩

end DaggerOriginalBaseRankCountableLadder
