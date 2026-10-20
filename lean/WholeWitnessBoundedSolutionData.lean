import BoundedWholeWitnessFactorization
import WholeSolutionStrongCommonRanks
import OriginalSmithSolutionsRecovered

/-! Exact original Smith solution squares cover every weak arrow through bounded whole witnesses. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWholeWitnessBoundedSolutionData
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type w} [Category.{v} C] [HasTerminal C] [HasColimitsOfSize.{u, u} C]
  (R : C ⥤ SSet.{u}) [R.IsCardinalAccessible Cardinal.aleph0.{u}]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
  [IsCardinalLocallyPresentable.{u} (Arrow C) κ]
  (hω : Cardinal.aleph0 < κ)
  (hR : ∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ)
  (I W : MorphismProperty C) (K : Type u) (G : K → Witness R)
  (hG : ∀ X : Witness R, IsCardinalPresentable X.arrow κ → ∃ k, Nonempty (X ≅ G k))
  (hweak : ∀ X : Witness R, W X.arrow.hom)
  (hcover : ∀ f : Arrow C, W f.hom → ∃ X : Witness R, X.arrow = f)
  (hI : ∀ i : I.toSet, IsCardinalPresentable i.val κ)

def atRank : DaggerSmithSolutionSet.SolutionData.{u} I W where
  index _ := K
  arrow _ k := (G k).arrow
  weak _ k := hweak (G k)
  factor i f hf φ := by
    obtain ⟨X, rfl⟩ := hcover f hf
    have : IsCardinalPresentable i.val κ := hI i
    obtain ⟨Y, hY, a, b, hab⟩ :=
      DaggerBoundedWholeWitnessFactorization.factor R κ hω hR X i.val φ
    obtain ⟨k, ⟨e⟩⟩ := hG Y hY
    let ea := (forget R).mapIso e
    refine ⟨k, a ≫ ea.hom, ea.inv ≫ b.square, ?_⟩
    rw [Category.assoc, ea.hom_inv_id_assoc]
    exact hab

end
end DaggerWholeWitnessBoundedSolutionData
