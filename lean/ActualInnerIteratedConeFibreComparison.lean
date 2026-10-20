import ActualInnerIteratedConeFibreEquivalence
import ActualInnerPositiveGadgetCofinality
import NativeCommaFirstStructuredArrowRetractSmallOperators

/-! The full native cone fibre equivalence and first-projection comma contraction for ALL quasi X.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerActualInnerIteratedGadgetData DaggerActualInnerIteratedRightConeIndex
open DaggerActualInnerIteratedConeFibreData DaggerActualInnerIteratedConeFibreEquivalence
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
universe u
namespace DaggerActualInnerIteratedConeFibreComparison
noncomputable section

theorem toMapping_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (P : BaseCode) (k : ℕ)
    (σ : spaceAt.{u} P (k + 1) ⟶ X)
    (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
    (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b) :
    GW (nerveMap (toMappingIndex X a b P k σ ha hb)) :=
  nerveMap_geometricW (toMappingIndex X a b P k σ ha hb)
    (fromMappingIndex X a b P k σ ha hb)
    (Relation.EqvGen.rel _ _ ⟨(fibreRoundtrip X a b P k σ ha hb).hom⟩)
    (Relation.EqvGen.rel _ _ ⟨(mappingRoundtrip X a b P k σ ha hb).hom⟩)

theorem first_projection_under_point_GW (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌))
    (τ : SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b)) :
    GW (pointMap (nerve (StructuredArrow τ (toCones X a b)))) :=
  DaggerNativeCommaFirstStructuredArrowRetractSmallOperators.source_point_GW (index X a b)
    (DaggerActualInnerIteratedGadgetShift.inclusion X a b) τ
    (DaggerActualInnerPositiveGadgetCofinality.structured_point_GW X a b ((index X a b).obj τ))

end
end DaggerActualInnerIteratedConeFibreComparison
