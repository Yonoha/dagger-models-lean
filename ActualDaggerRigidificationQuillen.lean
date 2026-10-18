import OriginalActualDaggerModelConstruction
import OriginalGlobalModelDataRecovered
import OriginalDaggerAdjunctionWitnessRecovered
import TopCatModelCategory.QuillenAdjunction

/-! The literal rigidification–nerve adjunction between the two constructed standard models. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.DaggerRigidification
open DaggerModels.OrdinaryRigidification.DaggerNerve
universe u

namespace DaggerActualRigidificationQuillen

abbrev D := DaggerSSet.{u}
abbrev G := DaggerSimplicialCat.{u, u}
noncomputable abbrev modelD : ModelCategory D.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory.{u}
noncomputable abbrev modelG : ModelCategory G.{u} := DaggerGlobalModel.standardModelCategory.{u}
noncomputable abbrev adjunction : daggerRigidification.{u} ⊣ daggerCoherentNerve.{u} :=
  daggerRigidificationLiftWitness.{u}.adjunction

noncomputable section
local instance : ModelCategory D.{u} := modelD.{u}
local instance : ModelCategory G.{u} := modelG.{u}

theorem source_cof : cofibrations D.{u} = DaggerSSet.freeCofibrations.{u} :=
  DaggerOriginalJoyalModel.standard_model_cof

theorem source_weak : weakEquivalences D.{u} =
    DaggerJoyalWeakProperties.standardJoyalWeakEquivalences.{u} :=
  DaggerOriginalJoyalModel.standard_model_weak

theorem target_cof : cofibrations G.{u} = DaggerGeneratingCofibrations.generators.{u}.rlp.llp := by
  exact congrArg (fun data : CategoryWithCofibrations G.{u} ↦ data.cofibrations)
    (DaggerGlobalModel.model_cofibrationStructure DaggerUnitaryInvariance.standardReplacement)

theorem target_weak : weakEquivalences G.{u} =
    DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement.{u} := by
  exact congrArg (fun data : CategoryWithWeakEquivalences G.{u} ↦ data.weakEquivalences)
    (DaggerGlobalModel.model_weakStructure DaggerUnitaryInvariance.standardReplacement)

theorem preservesCofibrations : daggerRigidification.{u}.PreservesCofibrations where
  cofibration_map i := by
    intro hi
    apply (cofibration_iff _).2
    rw [target_cof]
    have hc := (cofibration_iff i).1 hi
    rw [source_cof] at hc
    exact DaggerRigidificationCofBridge.rigidification_preserves_cofibrations i hc

theorem preservesTrivialCofibrations : daggerRigidification.{u}.PreservesTrivialCofibrations where
  trivialCofibrations_le := by
    intro X Y i hi
    change (cofibrations D ⊓ weakEquivalences D) i at hi
    change (cofibrations G ⊓ weakEquivalences G) (daggerRigidification.map i)
    rw [source_cof, source_weak] at hi
    rw [target_cof, target_weak]
    exact ⟨DaggerRigidificationCofBridge.rigidification_preserves_cofibrations i hi.1, hi.2⟩

theorem isQuillen : adjunction.{u}.IsQuillenAdjunction := by
  have : daggerRigidification.{u}.PreservesCofibrations := preservesCofibrations
  have : daggerRigidification.{u}.PreservesTrivialCofibrations := preservesTrivialCofibrations
  have : daggerCoherentNerve.{u}.PreservesFibrations :=
    adjunction.preservesTrivialCofibrations_iff_preservesFibrations.1 inferInstance
  exact ⟨⟩

end
end DaggerActualRigidificationQuillen
