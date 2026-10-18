import ActualInnerIteratedConeFibreComparison
import NativeCommaSecondNerveComparison

/-! The actual second-projection comma compares to the literal positive gadget mapping index. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualInnerIteratedGadgetData DaggerActualInnerIteratedRightConeIndex
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualInnerIteratedConeFibreData DaggerActualInnerIteratedConeFibreEquivalence
open DaggerNativeSmallHomNerveLift DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerIteratedSecondConeProjection
noncomputable section

variable (Z : SSet.{u}) (a b : Z.obj (op ⦋0⦌))
variable (P : BaseCode) (k : ℕ) (σ : spaceAt.{u} P (k + 1) ⟶ Z)
variable (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
variable (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b)

def target : DaggerActualInnerIteratedGadgetShift.FibrantOver Z a b :=
  ⟨targetOver Z a b P k σ ha hb, Nat.succ_pos k⟩

abbrev Source := CostructuredArrow (toPositive Z a b) (target Z a b P k σ ha hb)

def toActualFibre : Source Z a b P k σ ha hb ⥤ Fibre Z a b P k σ ha hb :=
  DaggerNativeCommaSecondCostructuredArrowRetractSmallOperators.toFibre (index Z a b)
    (DaggerActualInnerIteratedGadgetShift.inclusion Z a b) (target Z a b P k σ ha hb)

/-- First use the original second-projection comma triangle, then its full mapping simplex. -/
def toMapping : Source Z a b P k σ ha hb ⥤ MappingIndex P k :=
  toActualFibre Z a b P k σ ha hb ⋙ toMappingIndex Z a b P k σ ha hb

/-- The original degree is retained. -/
theorem toMapping_degree (A : Source Z a b P k σ ha hb) :
    ((toMapping Z a b P k σ ha hb).obj A).left = A.left.left.left := rfl

/-- The full cone map is the literal composite of both original comma arrows. -/
theorem toMapping_wholeMap (A : Source Z a b P k σ ha hb) :
    (uliftYonedaEquiv ((toMapping Z a b P k σ ha hb).obj A).hom).val =
      A.left.hom.hom.map ≫ A.hom.hom.hom.map :=
  toMapping_obj_map Z a b P k σ ha hb ((toActualFibre Z a b P k σ ha hb).obj A)

/-- Every original simplex operator survives the comparison unchanged. -/
theorem toMapping_operator {A B : Source Z a b P k σ ha hb} (f : A ⟶ B) :
    ((toMapping Z a b P k σ ha hb).map f).left = f.left.left.left := rfl

/-- The nerve map uses the whole original chains, with the original small operator universe. -/
theorem toMapping_GW : GW (mixedMap (toMapping Z a b P k σ ha hb)) := by
  have : WeakEquivalence (mixedMap (toActualFibre Z a b P k σ ha hb)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeCommaSecondNerveComparison.toFibre_GW (index Z a b)
        (DaggerActualInnerIteratedGadgetShift.inclusion Z a b) (target Z a b P k σ ha hb))
  have : WeakEquivalence (nerveMap (toMappingIndex Z a b P k σ ha hb)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualInnerIteratedConeFibreComparison.toMapping_GW Z a b P k σ ha hb)
  have he : mixedMap (toMapping Z a b P k σ ha hb) =
      mixedMap (toActualFibre Z a b P k σ ha hb) ≫
        nerveMap (toMappingIndex Z a b P k σ ha hb) := rfl
  apply (weakEquivalence_iff_GW _).mp
  rw [he]
  infer_instance

/-- Every object of the actual positive subcategory has such a comparison to an actual
Kan and weakly contractible right-cone mapping space. This does not yet identify its index nerve. -/
theorem all_positive_comparisons (Q : DaggerActualInnerIteratedGadgetShift.FibrantOver Z a b) :
    ∃ X : SSet.{u}, X.KanComplex ∧ GW (toUnit X) ∧
      ∃ G : CostructuredArrow (toPositive Z a b) Q ⥤ SimplexIndex X,
        GW (mixedMap G) := by
  rcases Q with ⟨⟨⟨P, l⟩, σ, ha, hb⟩, h⟩
  cases l with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ k =>
    exact ⟨MappingSpace P k, DaggerActualInnerIteratedGadgetProperties.positive_mapping_kan P k,
      (weakEquivalence_iff_GW _).mp
        (DaggerActualInnerIteratedGadgetProperties.positive_mapping_toUnit_weak P k),
      toMapping Z a b P k σ ha hb, toMapping_GW Z a b P k σ ha hb⟩

end
end DaggerActualInnerIteratedSecondConeProjection
