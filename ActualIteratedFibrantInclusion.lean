import ActualIteratedGadgetShift
import ActualIteratedGadgetNecklaceComparison

/-! Restricting to positive levels of the actual small family preserves its index nerve up to GW. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerNerveHomotopy DaggerSSetGluing
open DaggerActualIteratedGadgetData DaggerActualIteratedGadgetShift
universe u

namespace DaggerActualIteratedFibrantInclusion
noncomputable section

variable (D : SimplicialCat.{u, u}) (r : OriginalOrdinaryLocalKanReplacement.replacement.obj D ⟶ D)
variable (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D)
variable (a b : (coherentNerve.obj D).obj (op ⦋0⦌))

include r hr

/-- The full positive-level inclusion is weak by the two literal unit natural transformations. -/
theorem inclusion_GW : GW (nerveMap (DaggerActualIteratedGadgetShift.inclusion D a b)) :=
  nerveMap_geometricW (DaggerActualIteratedGadgetShift.inclusion D a b)
    (toFibrant D r hr a b)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨fibrantUnit D r hr a b⟩))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨allUnit D r hr a b⟩))

/-- The actual full-map extension to positive levels is itself weak on index nerves. -/
theorem toFibrant_GW : GW (nerveMap (toFibrant D r hr a b)) :=
  nerveMap_geometricW (toFibrant D r hr a b)
    (DaggerActualIteratedGadgetShift.inclusion D a b)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨allUnit D r hr a b⟩))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨fibrantUnit D r hr a b⟩))

/-- The original necklace category maps weakly into the same small positive-level comparison. -/
theorem necklace_toFibrant_GW : GW (nerveMap
    (DaggerActualIteratedGadgetNecklaceComparison.inclusion (coherentNerve.obj D) a b ⋙
      toFibrant D r hr a b)) := by
  have : HomotopicalAlgebra.WeakEquivalence
      (nerveMap (DaggerActualIteratedGadgetNecklaceComparison.inclusion
        (coherentNerve.obj D) a b)) := (weakEquivalence_iff_GW _).mpr
    (DaggerActualIteratedGadgetNecklaceComparison.inclusion_GW _ _ _)
  have : HomotopicalAlgebra.WeakEquivalence (nerveMap (toFibrant D r hr a b)) :=
    (weakEquivalence_iff_GW _).mpr (toFibrant_GW D r hr a b)
  have he : nerveMap
      (DaggerActualIteratedGadgetNecklaceComparison.inclusion (coherentNerve.obj D) a b ⋙
        toFibrant D r hr a b) =
      nerveMap (DaggerActualIteratedGadgetNecklaceComparison.inclusion
        (coherentNerve.obj D) a b) ≫ nerveMap (toFibrant D r hr a b) := rfl
  apply (weakEquivalence_iff_GW _).mp
  rw [he]
  infer_instance

end
end DaggerActualIteratedFibrantInclusion
