import OriginalFreeCofibrationGeneration
import OriginalActualWeakSolutionsRecovered

set_option autoImplicit false
open CategoryTheory MorphismProperty DaggerModels
universe u

namespace DaggerOriginalJoyalModel

/-- The literal free boundaries generate the whole original free-cofibration class. -/
theorem originalID_rlp_llp_eq_freeCofibrations :
    DaggerActualWeakAccessibility.originalID.{u}.rlp.llp = DaggerSSet.freeCofibrations.{u} :=
  DaggerOriginalFreeCofibrationGeneration.boundary_rlp_llp_eq_freeCof

/-- Its right lifting class is the right lifting class of all free cofibrations. -/
theorem originalID_rlp_eq_freeCofibrations_rlp :
    DaggerActualWeakAccessibility.originalID.{u}.rlp = DaggerSSet.freeCofibrations.{u}.rlp := by
  rw [← originalID_rlp_llp_eq_freeCofibrations, rlp_llp_rlp]

end DaggerOriginalJoyalModel
