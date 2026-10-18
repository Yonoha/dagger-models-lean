import OriginalInitialCategoryCompletionThin
import OriginalFreeEC2DaggerGroupoidComparison
import OriginalFixedObjectGroupoidTerminals

/-!
# The actual free point is the original walking unitary interval

Reuse the existing indiscrete two-object dagger groupoid: its four Hom objects
are literally the simplicial unit and its dagger is the unique inverse. In each
degree the original one-arrow category has an initial left vertex. Mathlib's
native localization contraction makes its completed Hom sets singletons. Thus
the actual free point is terminal, yielding a full fixed-object dagger isomorphism
to the original interval. The actual free EC2 augmentation is a trivial fibration
with cofibrant source, without a projectively cofibrant point assumption.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectOrdinaryCellAdjunction DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
open DaggerOriginalFixedObjectDaggerActionEquivalence
open DaggerOriginalFreeEC2DaggerGroupoidComparison DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalInitialCategoryCompletionThin
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
  DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalFixedObjectFreePointInterval
noncomputable section

/-- The paper's walking unitary interval, reusing the original singleton-Hom dagger groupoid. -/
abbrev unitaryInterval : FixedStrictDaggerGroupoids TwoObjects.{u} :=
  strictDaggerTerminal TwoObjects

/-- Every original interval Hom is literally the native simplicial point. -/
theorem unitaryInterval_hom (x y : TwoObjects.{u}) :
    unitaryInterval.obj.underlying.enriched.Hom x y = 𝟙_ SSet.{u} := rfl

/-- The original interval dagger is the identity between its literal singleton Hom objects. -/
theorem unitaryInterval_dagger (x y : TwoObjects.{u}) :
    unitaryInterval.obj.dagger.dagger x y = 𝟙 (𝟙_ SSet.{u}) := rfl

/-- The terminal original simplicial action's unchanged underlying parameter. -/
abbrev pointParameter : SSet.{u} := (⊤_ (Action SSet.{u} C2.{u})).V

/-- Native forgetting preserves the actual terminal point, rather than replacing its universe. -/
def pointParameterIsTerminal : IsTerminal pointParameter.{u} :=
  IsTerminal.isTerminalObj (Action.forget SSet.{u} C2.{u}) _ terminalIsTerminal

/-- Every original degree of the terminal parameter has precisely one simplex. -/
def pointDegreeUnique (n : SimplexCategoryᵒᵖ) : Unique (pointParameter.{u}.obj n) :=
  Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n) _
      pointParameterIsTerminal)

/-- The original left endpoint is initial in each actual one-arrow point-cell degree. -/
def pointCellDegreeInitial (n : SimplexCategoryᵒᵖ) :
    @IsInitial (degreeObjects (original TwoObjects (cell pointParameter.{u})) n)
      (degreeCategory (original TwoObjects (cell pointParameter.{u})) n)
      TwoObjectDaggerGraph.left := by
  letI := degreeCategory (original TwoObjects (cell pointParameter.{u})) n
  letI := pointDegreeUnique.{u} n
  refine IsInitial.ofUniqueHom (fun x ↦ ?_) ?_
  · rcases x with ⟨b⟩
    cases b
    · change PUnit.{u + 1}
      exact PUnit.unit
    · change pointParameter.{u}.obj n
      exact default
  · intro x f
    rcases x with ⟨b⟩
    cases b
    · exact Subsingleton.elim (α := PUnit.{u + 1}) f _
    · exact Subsingleton.elim (α := pointParameter.{u}.obj n) f _

/-- The actual completed original point-cell has a single Hom simplex in every degree. -/
instance completedPointHomUnique (n : SimplexCategoryᵒᵖ) (x y : TwoObjects.{u}) :
    Unique (((freeGroupoid.obj pointParameter).obj.enriched.Hom x y).obj n) := by
  let C := degreeObjects (original TwoObjects (cell pointParameter.{u})) n
  letI : Category.{u} C := degreeCategory (original TwoObjects (cell pointParameter.{u})) n
  let hc := pointCellDegreeInitial.{u} n
  let hthin := @completionIsThin C
    (degreeCategory (original TwoObjects (cell pointParameter.{u})) n)
    TwoObjectDaggerGraph.left hc
  exact
    { default := Classical.choice (@completionHomNonempty C
        (degreeCategory (original TwoObjects (cell pointParameter.{u})) n)
        TwoObjectDaggerGraph.left hc
        (completedObject (original TwoObjects (cell pointParameter)) n x)
        (completedObject (original TwoObjects (cell pointParameter)) n y))
      uniq := fun f ↦ (hthin _ _).elim _ _ }

/-- The entire unique strict groupoid functor into the actual original free point. -/
def toOrdinaryFreePoint (C : FixedStrictGroupoids TwoObjects.{u}) :
    C ⟶ freeGroupoid.obj pointParameter := ObjectProperty.homMk
  { map := fun x y ↦
      { app := fun _ _ ↦ default
        naturality := by
          intro n m i
          funext f
          exact Subsingleton.elim _ _ }
    map_id := by
      intro x
      apply NatTrans.ext
      funext n f
      exact Subsingleton.elim _ _
    map_comp := by
      intro x y z
      apply NatTrans.ext
      funext n f
      exact Subsingleton.elim _ _ }

/-- The actual original ordinary free point has the full native terminal universal property. -/
def ordinaryFreePointIsTerminal : IsTerminal (freeGroupoid.obj pointParameter.{u}) :=
  IsTerminal.ofUniqueHom toOrdinaryFreePoint (by
    intro C F
    apply ObjectProperty.hom_ext
    apply fixedHom_ext
    intro x y
    apply NatTrans.ext
    funext n f
    exact Subsingleton.elim _ _)

/-- The actual entire free point action is terminal, including every original action element. -/
def freePointActionIsTerminal :
    IsTerminal (freeActionGroupoid.obj (⊤_ (Action SSet.{u} C2.{u}))) :=
  IsTerminal.ofUniqueHom
    (fun A ↦
      { hom := ordinaryFreePointIsTerminal.from A.V
        comm := fun g ↦ ordinaryFreePointIsTerminal.hom_ext _ _ })
    (by intro A F; exact Action.Hom.ext (ordinaryFreePointIsTerminal.hom_ext _ _))

/-- The full inverse equivalence preserves terminality of the actual original free point. -/
def freePointIsTerminal : IsTerminal freePoint.{u} :=
  IsTerminal.isTerminalObj (fixedDaggerActionEquivalence TwoObjects).inverse _
    freePointActionIsTerminal

/-- A full fixed-object dagger isomorphism identifies the actual free point with the interval. -/
def freePointIntervalIso : freePoint.{u} ≅ unitaryInterval :=
  freePointIsTerminal.uniqueUpToIso (strictDaggerTerminalIsTerminal TwoObjects)

/-- The original generator is the actual adjunction unit on the actual terminal parameter. -/
def freePointGenerator : pointParameter.{u} ⟶
    freePoint.obj.underlying.enriched.Hom TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right :=
  (freeDaggerGroupoidAdjunction.unit.app (⊤_ (Action SSet.{u} C2.{u}))).hom

/-- The full interval isomorphism sends that exact generator to the unique interval arrow. -/
theorem freePointIntervalIso_generator :
    freePointGenerator.{u} ≫ freePointIntervalIso.hom.hom.underlying.map
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right =
        CartesianMonoidalCategory.toUnit pointParameter :=
  CartesianMonoidalCategory.toUnit_unique _ _

/-- The augmentation is the previously proved actual free map followed by this full interval iso. -/
def augmentation : freeEC2.{u} ⟶ unitaryInterval := comparison ≫ freePointIntervalIso.hom

/-- The actual augmentation to the original walking unitary interval is a weak equivalence. -/
theorem augmentation_weakEquivalence : WeakEquivalence augmentation.{u} := by
  have : WeakEquivalence comparison.{u} := comparison_weakEquivalence
  change WeakEquivalence (comparison ≫ freePointIntervalIso.hom)
  infer_instance

/-- All strict groupoids are fibrant, so this actual map to the interval is a fibration. -/
theorem augmentation_fibration : Fibration augmentation.{u} :=
  (isFibrant_iff_of_isTerminal augmentation
    (strictDaggerTerminalIsTerminal TwoObjects)).1 inferInstance

/-- The actual original EC2 free groupoid gives a trivial-fibration approximation
of the interval. -/
theorem augmentation_trivialFibration :
    trivialFibrations (FixedStrictDaggerGroupoids TwoObjects.{u}) augmentation :=
  (mem_trivialFibrations_iff _).2 ⟨augmentation_fibration, augmentation_weakEquivalence⟩

/-- The source of that exact original interval approximation is genuinely cofibrant. -/
theorem augmentation_source_isCofibrant : IsCofibrant freeEC2.{u} := freeEC2_isCofibrant

end
end DaggerOriginalFixedObjectFreePointInterval
