import ActualOrdinaryRigidificationLocalization
import OriginalOrdinaryCoreKan

/-! The actual original ordinary core inherits the fixed-object rigidification results. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerActualOrdinaryRigidificationFixedCofibrancy
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryCoreKan
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerActualOrdinaryCoreRigidificationLocalization
noncomputable section

theorem core_fixed_isCofibrant (X : SSet.{u}) :
    IsCofibrant (fixed (ordinaryCoreCandidate X : SSet.{u})) :=
  fixed_isCofibrant _

theorem core_diagonalLocalization_weak (X : SSet.{u}) :
    WeakEquivalence
      (diagonalLocalization (rigidification.obj (ordinaryCoreCandidate X : SSet.{u}))) :=
  DaggerActualOrdinaryRigidificationLocalization.diagonalLocalization_weak _

theorem core_localizationHom_weak_iff_componentGroupoid (X : SSet.{u}) :
    (∀ x y : (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})).Obj,
      WeakEquivalence
        (localizationHom (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})) x y)) ↔
      HasActualComponentGroupoid
        (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})) :=
  DaggerActualOrdinaryRigidificationLocalization.localizationHom_weak_iff_componentGroupoid _

/-- Kan status and actual fixed-object cofibrancy hold simultaneously for the original core. -/
theorem core_kan_and_fixed_isCofibrant (X : SSet.{u}) (hX : innerHornFillers X) :
    (ordinaryCoreCandidate X : SSet.{u}).KanComplex ∧
      IsCofibrant (fixed (ordinaryCoreCandidate X : SSet.{u})) :=
  ⟨ordinaryCoreCandidate_kan X hX, core_fixed_isCofibrant X⟩

end
end DaggerActualOrdinaryCoreRigidificationLocalization
