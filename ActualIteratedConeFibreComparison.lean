import ActualIteratedConeFibreEquivalence
import NativeCommaFirstStructuredArrowRetractSmallOperators

/-! The actual cone fibre comparison is weak, and every structured comma of the first projection
is contractible. The final cone-index GW is not asserted here. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData DaggerActualIteratedRightConeIndex
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualIteratedConeFibreData DaggerActualIteratedConeFibreEquivalence
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedConeFibreComparison
noncomputable section

/-- The exact fibre-to-mapping-simplex functor is weak at every positive level. -/
theorem toMapping_GW (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) (P : BaseCode) (k : ℕ)
    (σ : spaceAt.{u} P (k + 1) ⟶ coherentNerve.obj D)
    (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
    (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b) :
    GW (nerveMap (toMappingIndex D a b P k σ ha hb)) :=
  nerveMap_geometricW (toMappingIndex D a b P k σ ha hb)
    (fromMappingIndex D a b P k σ ha hb)
    (Relation.EqvGen.rel _ _ ⟨(fibreRoundtrip D a b P k σ ha hb).hom⟩)
    (Relation.EqvGen.rel _ _ ⟨(mappingRoundtrip D a b P k σ ha hb).hom⟩)

/-- This is the structured-arrow comma of the actual projection to the original cone index. -/
theorem first_projection_under_point_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (τ : SimplexIndex (rightConeSimplices D a b)) :
    GW (pointMap (nerve (StructuredArrow τ (toCones D a b)))) :=
  DaggerNativeCommaFirstStructuredArrowRetractSmallOperators.source_point_GW (index D a b)
    (DaggerActualIteratedGadgetShift.inclusion D a b) τ
    (DaggerActualIteratedFibrantStructuredArrows.point_GW D hD a b ((index D a b).obj τ))

/-- The same assertion uses the exact native terminal map, with no fibre-weakness premise. -/
theorem first_projection_under_toUnit_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (τ : SimplexIndex (rightConeSimplices D a b)) :
    GW (toUnit (nerve (StructuredArrow τ (toCones D a b)))) := by
  let X := nerve (StructuredArrow τ (toCones D a b))
  let e := pointIsTerminal.{u}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : IsIso e.hom := e.isIso_hom
  have : WeakEquivalence (pointMap X) :=
    (weakEquivalence_iff_GW _).mpr (first_projection_under_point_GW D hD a b τ)
  have he : pointMap X ≫ e.hom = toUnit X := isTerminalTensorUnit.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerActualIteratedConeFibreComparison
