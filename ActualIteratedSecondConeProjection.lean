import NativeCommaSecondNerveComparison

/-! The actual second-projection comma compares to the literal positive gadget mapping index. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData DaggerActualIteratedRightConeIndex
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualIteratedConeFibreData DaggerActualIteratedConeFibreEquivalence
open DaggerNativeSmallHomNerveLift DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedSecondConeProjection
noncomputable section

variable (D : SimplicialCat.{u, u}) (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
variable (P : BaseCode) (k : ℕ) (σ : spaceAt.{u} P (k + 1) ⟶ coherentNerve.obj D)
variable (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
variable (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b)

def target : DaggerActualIteratedGadgetShift.FibrantOver D a b :=
  ⟨targetOver D a b P k σ ha hb, Nat.succ_pos k⟩

abbrev Source := CostructuredArrow (toPositive D a b) (target D a b P k σ ha hb)

def toActualFibre : Source D a b P k σ ha hb ⥤ Fibre D a b P k σ ha hb :=
  DaggerNativeCommaSecondCostructuredArrowRetractSmallOperators.toFibre (index D a b)
    (DaggerActualIteratedGadgetShift.inclusion D a b) (target D a b P k σ ha hb)

/-- First use the original second-projection comma triangle, then its full mapping simplex. -/
def toMapping : Source D a b P k σ ha hb ⥤ MappingIndex P k :=
  toActualFibre D a b P k σ ha hb ⋙ toMappingIndex D a b P k σ ha hb

/-- The original degree is retained. -/
theorem toMapping_degree (A : Source D a b P k σ ha hb) :
    ((toMapping D a b P k σ ha hb).obj A).left = A.left.left.left := rfl

/-- The full cone map is the literal composite of both original comma arrows. -/
theorem toMapping_wholeMap (A : Source D a b P k σ ha hb) :
    (uliftYonedaEquiv ((toMapping D a b P k σ ha hb).obj A).hom).val =
      A.left.hom.hom.map ≫ A.hom.hom.hom.map :=
  toMapping_obj_map D a b P k σ ha hb ((toActualFibre D a b P k σ ha hb).obj A)

/-- Every original simplex operator survives the comparison unchanged. -/
theorem toMapping_operator {A B : Source D a b P k σ ha hb} (f : A ⟶ B) :
    ((toMapping D a b P k σ ha hb).map f).left = f.left.left.left := rfl

/-- The nerve map uses the whole original chains, with the original small operator universe. -/
theorem toMapping_GW : GW (mixedMap (toMapping D a b P k σ ha hb)) := by
  have : WeakEquivalence (mixedMap (toActualFibre D a b P k σ ha hb)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNativeCommaSecondNerveComparison.toFibre_GW (index D a b)
        (DaggerActualIteratedGadgetShift.inclusion D a b) (target D a b P k σ ha hb))
  have : WeakEquivalence (nerveMap (toMappingIndex D a b P k σ ha hb)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedConeFibreComparison.toMapping_GW D a b P k σ ha hb)
  have he : mixedMap (toMapping D a b P k σ ha hb) =
      mixedMap (toActualFibre D a b P k σ ha hb) ≫
        nerveMap (toMappingIndex D a b P k σ ha hb) := rfl
  apply (weakEquivalence_iff_GW _).mp
  rw [he]
  infer_instance

/-- Every object of the actual positive subcategory has such a comparison to an actual
Kan and weakly contractible right-cone mapping space. This does not yet identify its index nerve. -/
theorem all_positive_comparisons (Q : DaggerActualIteratedGadgetShift.FibrantOver D a b) :
    ∃ X : SSet.{u}, X.KanComplex ∧ GW (toUnit X) ∧
      ∃ G : CostructuredArrow (toPositive D a b) Q ⥤ SimplexIndex X,
        GW (mixedMap G) := by
  rcases Q with ⟨⟨⟨P, l⟩, σ, ha, hb⟩, h⟩
  cases l with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ k =>
    exact ⟨MappingSpace P k, DaggerActualIteratedGadgetRightMapping.rightCone_Kan P k,
      DaggerActualIteratedGadgetRightMapping.rightCone_toUnit_GW P k,
      toMapping D a b P k σ ha hb, toMapping_GW D a b P k σ ha hb⟩

end
end DaggerActualIteratedSecondConeProjection
