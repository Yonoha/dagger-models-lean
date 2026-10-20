import ActualIteratedGadgetHomAugmentation

/-! Both actual index maps induce weak comparisons of the exact original Hom-weighted replacements. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedRightConeIndex DaggerActualIteratedGadgetHomAugmentation
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementReindex
open DaggerSSetGluing
universe u
namespace DaggerActualIteratedGadgetWeightedReindex
noncomputable section

/-- Reindex all original necklace chains, retaining their whole original C(T) Hom simplex. -/
def necklaceMap (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :=
  diagonalReindex (DaggerActualIteratedGadgetNecklaceComparison.inclusion X a b)
    (diagram X a b)

/-- The literal necklace-weighted map is weak by the proved inclusion and exact Hom weights. -/
theorem necklaceMap_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (necklaceMap X a b) :=
  diagonalReindex_GW (DaggerActualIteratedGadgetNecklaceComparison.inclusion X a b)
    (diagram X a b) (DaggerActualIteratedGadgetNecklaceComparison.inclusion_GW X a b)
    (diagram_point_GW X a b)

/-- The exact original cone chain, with only its small hom universe raised, keeps its whole Q weight. -/
def coneMap (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :=
  diagonalReindex (DaggerActualIteratedConeIndexWeakness.raisedIndex D a b)
    (diagram (coherentNerve.obj D) a b)

/-- The cone-weighted map is weak under only the actual original local Kan hypothesis. -/
theorem coneMap_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) : GW (coneMap D a b) :=
  diagonalReindex_GW (DaggerActualIteratedConeIndexWeakness.raisedIndex D a b)
    (diagram (coherentNerve.obj D) a b)
    (DaggerActualIteratedConeIndexWeakness.raised_index_GW D hD a b)
    (diagram_point_GW (coherentNerve.obj D) a b)

end
end DaggerActualIteratedGadgetWeightedReindex
