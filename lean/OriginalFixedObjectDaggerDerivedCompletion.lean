import OriginalFixedObjectDaggerCompletionQuillen
import OriginalCofibrantBrownPreservationChallengeProof

/-!
# Preservation needed for original derived dagger completion

The actual completion preserves cofibrant objects and weak equivalences between
cofibrant objects. The actual inclusion preserves fibrant objects. These statements
retain the full original enriched categories and the proved exact model classes.
They do not assert a Quillen equivalence or an equivalence for every localization unit.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectDaggerCompletionQuillen
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictDaggerModel DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalFixedObjectDaggerDerivedCompletion
noncomputable section

/-- The actual full completion sends original cofibrant objects to original cofibrant objects. -/
theorem completion_isCofibrant {O : Type u} (C : FixedDaggerCategory O) [IsCofibrant C] :
    IsCofibrant ((fixedDaggerCompletion O).obj C) := by
  letI : (fixedDaggerCompletion O).IsLeftAdjoint :=
    (fixedDaggerCompletionInclusionAdjunction O).isLeftAdjoint
  have : Cofibration (initial.to C) := (isCofibrant_iff C).1 inferInstance
  exact (isCofibrant_iff_of_isInitial ((fixedDaggerCompletion O).map (initial.to C))
    (IsInitial.isInitialObj (fixedDaggerCompletion O) _ initialIsInitial)).2
      (completion_cofibration (initial.to C))

/-- The actual unchanged inclusion sends original fibrant objects to original fibrant objects. -/
theorem inclusion_isFibrant {O : Type u} (D : FixedStrictDaggerGroupoids O) [IsFibrant D] :
    IsFibrant ((fixedDaggerInclusion O).obj D) := by
  letI : (fixedDaggerInclusion O).IsRightAdjoint :=
    (fixedDaggerCompletionInclusionAdjunction O).isRightAdjoint
  have hp : Fibration (terminal.from D) := (isFibrant_iff D).1 inferInstance
  exact (isFibrant_iff_of_isTerminal ((fixedDaggerInclusion O).map (terminal.from D))
    (IsTerminal.isTerminalObj (fixedDaggerInclusion O) _ terminalIsTerminal)).2
      ((inclusion_fibration_iff (terminal.from D)).2 hp)

/-- Brown's native factorization applies to completion with the cofibrancy hypotheses explicit. -/
theorem completion_weakEquivalence {O : Type u} {C D : FixedDaggerCategory O}
    (F : C ⟶ D) [IsCofibrant C] [IsCofibrant D] [WeakEquivalence F] :
    WeakEquivalence ((fixedDaggerCompletion O).map F) := by
  apply DaggerOriginalCofibrantBrownPreservationChallengeProof.challengeProof
    (FixedDaggerCategory O) (FixedStrictDaggerGroupoids O) (fixedDaggerCompletion O)
    ?_ inferInstance inferInstance F inferInstance
  intro X Y i hi hw
  exact ((mem_trivialCofibrations_iff _).1
    (completion_trivialCofibration i ((mem_trivialCofibrations_iff _).2 ⟨hi, hw⟩))).2

end
end DaggerOriginalFixedObjectDaggerDerivedCompletion
