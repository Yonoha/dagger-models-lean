import NativeCoproductConnectedFactor
import NativeConnectedHornsAndSimplex
import NativeFinitePiKan

/-! The actual native coproduct is Kan when every unchanged summand is Kan. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeCoproductConnectedFactor DaggerNativeSSetCoproductSummandFibration
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalNativeKanFromHornFillers
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductKan
noncomputable section

instance coproduct_fibrant {I : Type u} (X : I → SSet.{u}) [∀ i, IsFibrant (X i)] :
    IsFibrant (∐ X) := by
  apply kanComplex_of_hornFillers
  intro n k a
  obtain ⟨v⟩ := hornVertex_nonempty n k
  obtain ⟨⟨i, t⟩, ht⟩ := (coproductDegreeEquiv X (op ⦋0⦌)).surjective
    (a.app (op ⦋0⦌) v)
  obtain ⟨g, hg⟩ := connected_factor_fixed_summand X i a v t ht.symm
  obtain ⟨l, hl⟩ := SSet.KanComplex.hornFilling g
  refine ⟨l ≫ Sigma.ι X i, ?_⟩
  rw [← Category.assoc, ← hl]
  exact hg.symm

end
end DaggerNativeCoproductKan
