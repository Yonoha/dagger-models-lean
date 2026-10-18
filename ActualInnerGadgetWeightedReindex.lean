import ActualInnerGadgetHomAugmentation
import ActualInnerConeIndexWeakness

/-! Reuse the original weighted reindexing maps for the NEW native family and ALL quasi X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerActualInnerGadgetHomAugmentation DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementReindex DaggerSSetGluing
universe u
namespace DaggerActualInnerGadgetWeightedReindex
noncomputable section

def necklaceMap (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :=
  diagonalReindex (DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b)
    (diagram X a b)

theorem necklaceMap_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : GW (necklaceMap X a b) :=
  diagonalReindex_GW (DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b)
    (diagram X a b) (DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion_GW X a b)
    (diagram_point_GW X a b)

def coneMap (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :=
  diagonalReindex (DaggerActualInnerConeIndexWeakness.raisedIndex X a b) (diagram X a b)

theorem coneMap_GW (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    GW (coneMap X a b) :=
  diagonalReindex_GW (DaggerActualInnerConeIndexWeakness.raisedIndex X a b)
    (diagram X a b) (DaggerActualInnerConeIndexWeakness.raised_index_GW X a b)
    (diagram_point_GW X a b)

end
end DaggerActualInnerGadgetWeightedReindex
