import TopCatModelCategory.SSet.Pseudofunctor
import TopCatModelCategory.PseudoFunctor.MorphismProperty
import TopCatModelCategory.SSet.KanComplexW

universe u

open CategoryTheory HomotopicalAlgebra Simplicial SSet.modelCategoryQuillen Simplicial

namespace SSet

namespace KanComplex

open MorphismProperty

section

variable {X X' Y Y' : SSet.{u}} [IsFibrant X] [IsFibrant X'] [IsFibrant Y] [IsFibrant Y']
  {f : X ⟶ X'} {g : Y ⟶ Y'} (r : RetractArrow f g)

include r

lemma isEquivalence_mapFundamentalGroupoid_of_retract
    [(mapFundamentalGroupoid g).IsEquivalence] :
    (mapFundamentalGroupoid f).IsEquivalence := by
  let W := MorphismProperty.ofPseudofunctor FundamentalGroupoid.pseudofunctor.{u}
  let f' : KanComplexCat.mk X ⟶ KanComplexCat.mk X' := ObjectProperty.homMk f
  let g' : KanComplexCat.mk Y ⟶ KanComplexCat.mk Y' := ObjectProperty.homMk g
  have hg' : W g' := by assumption
  change W f'
  exact of_retract (g := g')
    { i := Arrow.homMk (ObjectProperty.homMk r.left.i) (ObjectProperty.homMk r.right.i)
        (by apply ObjectProperty.hom_ext; exact r.i.w)
      r := Arrow.homMk (ObjectProperty.homMk r.left.r) (ObjectProperty.homMk r.right.r)
        (by apply ObjectProperty.hom_ext; exact r.r.w)
      retract := by
        apply Arrow.hom_ext
        · apply ObjectProperty.hom_ext
          exact r.left.retract
        · apply ObjectProperty.hom_ext
          exact r.right.retract } hg'
end

instance : W.{u}.IsStableUnderRetracts where
  of_retract {X X' Y Y' f g} r hg := by
    have := hg.isFibrant_src
    have := hg.isFibrant_tgt
    have := isFibrant_of_retract r.left
    have := isFibrant_of_retract r.right
    refine W.mk _ ?_ ?_
    · have := hg.isEquivalence
      exact isEquivalence_mapFundamentalGroupoid_of_retract r
    · intro n x x' h
      rw [← isIso_iff_bijective]
      apply of_retract (P := isomorphisms (Type u))
        (retractArrowMapπ r n x x' h _ _ rfl rfl)
      simp only [isomorphisms.iff]
      rw [isIso_iff_bijective]
      apply hg.bijective

end KanComplex

end SSet
