import OriginalCodiscreteNerveInjective
import OriginalFixedObjectFreeDaggerGroupoidQuillen

/-!
# The actual free EC2 dagger groupoid compared with the free point

The original codiscrete nerve projection has lifting against all simplicial
monomorphisms. Thus its original equivariant terminal projection is a native
projective trivial fibration. The actual free dagger groupoid preserves its weak
equivalence, and its EC2 source is cofibrant. Identifying the free point with the
paper's separately chosen dagger interval and the enriched RMap remains separate.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
  DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalFreeEC2DaggerGroupoidComparison
noncomputable section

/-- The full underlying original EC2 terminal projection is a native trivial fibration. -/
theorem augmentation_underlying_trivialFibration :
    trivialFibrations SSet.{u} (terminal.from simplicialAction.{u}).hom := by
  have ht : IsTerminal ((⊤_ (Action SSet.{u} C2.{u})).V) :=
    IsTerminal.isTerminalObj (Action.forget SSet.{u} C2.{u}) _ terminalIsTerminal
  have : Nonempty regularAction.V := ⟨(1 : C2.{u})⟩
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration _ ht

/-- The original equivariant EC2 terminal projection is a native projective trivial fibration. -/
theorem augmentation_trivialFibration :
    trivialFibrations (Action SSet.{u} C2.{u}) (terminal.from simplicialAction.{u}) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 augmentation_underlying_trivialFibration
  exact (mem_trivialFibrations_iff _).2
    ⟨(DaggerOriginalSimplicialActionModelCategory.fibration_iff_underlying _).2 hf,
      (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).2 hw⟩

/-- Native fibrancy of the literal original EC2 action, without a Kan premise. -/
theorem originalEC2_isFibrant : IsFibrant simplicialAction.{u} :=
  (isFibrant_iff _).2 ((mem_trivialFibrations_iff _).1 augmentation_trivialFibration).1

/-- The unchanged original codiscrete nerve is a native Kan complex. -/
theorem originalEC2_kan : simplicialEC2.{u}.KanComplex :=
  (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).1 originalEC2_isFibrant

/-- The actual free dagger groupoid on the original EC2 with its original regular action. -/
def freeEC2 : FixedStrictDaggerGroupoids TwoObjects.{u} :=
  freeDaggerGroupoid.obj simplicialAction

/-- The actual free dagger groupoid on the terminal original simplicial action. -/
def freePoint : FixedStrictDaggerGroupoids TwoObjects.{u} :=
  freeDaggerGroupoid.obj (⊤_ (Action SSet.{u} C2.{u}))

/-- The comparison is precisely the actual free functor applied to the original augmentation. -/
def comparison : freeEC2.{u} ⟶ freePoint :=
  freeDaggerGroupoid.map (terminal.from simplicialAction)

/-- The actual original free EC2 source is cofibrant in the proved dagger groupoid model. -/
theorem freeEC2_isCofibrant : IsCofibrant freeEC2.{u} := freeOriginalEC2_isCofibrant

/-- The actual augmentation-induced free dagger groupoid map is a native weak equivalence. -/
theorem comparison_weakEquivalence : WeakEquivalence comparison.{u} := by
  have : WeakEquivalence (terminal.from simplicialAction.{u}) :=
    ((mem_trivialFibrations_iff _).1 augmentation_trivialFibration).2
  exact freeDaggerGroupoid_weakEquivalence (terminal.from simplicialAction)

end
end DaggerOriginalFreeEC2DaggerGroupoidComparison
