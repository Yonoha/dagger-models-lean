import OriginalFixedObjectGroupoidPathObjects

/-!
# Terminal original fixed-object groupoids and actual fibrancy

The indiscrete enrichment on exactly O has the native simplicial unit as each
Hom. Its original product-free operations, dagger and strict inverses satisfy
all laws. The whole original terminal universal property gives HasTerminal.
Every original strict groupoid is fibrant in the specified Homwise class,
because each unchanged original Hom is already Kan. No model is assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u

namespace DaggerOriginalFixedObjectGroupoidTerminals

noncomputable section

/-- The original terminal enrichment has exactly O and a single arrow in every Hom degree. -/
def terminalFixed (O : Type u) : FixedSimplicialCategory O where
  enriched :=
    { Hom _ _ := 𝟙_ SSet.{u}
      id _ := 𝟙 _
      comp _ _ _ := CartesianMonoidalCategory.toUnit _
      id_comp _ _ := CartesianMonoidalCategory.toUnit_unique _ _
      comp_id _ _ := CartesianMonoidalCategory.toUnit_unique _ _
      assoc _ _ _ _ := CartesianMonoidalCategory.toUnit_unique _ _ }

/-- The unique original functor to the terminal object keeps every object of O fixed. -/
def toTerminal {O : Type u} (C : FixedSimplicialCategory O) : C ⟶ terminalFixed O where
  map x y := CartesianMonoidalCategory.toUnit (C.enriched.Hom x y)
  map_id _ := CartesianMonoidalCategory.toUnit_unique _ _
  map_comp _ _ _ := CartesianMonoidalCategory.toUnit_unique _ _

/-- Every original terminal arrow is its own inverse in the actual original degree category. -/
theorem terminal_strict (O : Type u) : IsStrictFixed (terminalFixed O) := by
  intro n x y f
  refine ⟨⟨PUnit.unit, ?_, ?_⟩⟩ <;> rfl

/-- The original same-O terminal object is an actual strict simplicial groupoid. -/
def strictTerminal (O : Type u) : FixedStrictGroupoids O :=
  ⟨terminalFixed O, terminal_strict O⟩

/-- The entire unique original strict groupoid functor to the same-O terminal. -/
def strictToTerminal {O : Type u} (C : FixedStrictGroupoids O) : C ⟶ strictTerminal O :=
  ObjectProperty.homMk (toTerminal C.obj)

/-- The full native terminal universal property in the actual original strict category. -/
def strictTerminalIsTerminal (O : Type u) : IsTerminal (strictTerminal O) :=
  IsTerminal.ofUniqueHom strictToTerminal (by
    intro C F
    apply ObjectProperty.hom_ext
    apply fixedHom_ext
    intro x y
    exact CartesianMonoidalCategory.toUnit_unique _ _)

/-- Native terminal existence follows from that exact original terminal cone. -/
instance strictHasTerminal (O : Type u) : HasTerminal (FixedStrictGroupoids O) :=
  (strictTerminalIsTerminal O).hasTerminal

/-- The exact original terminal dagger fixes its unique native Hom arrow. -/
def terminalDagger (O : Type u) : @DaggerSimplicialStructure O (terminalFixed O).enriched := by
  letI := (terminalFixed O).enriched
  exact
    { dagger := fun _ _ ↦ 𝟙 _
      dagger_involutive := fun _ _ ↦ CartesianMonoidalCategory.toUnit_unique _ _
      dagger_id := fun _ ↦ CartesianMonoidalCategory.toUnit_unique _ _
      dagger_comp := fun _ _ _ ↦ CartesianMonoidalCategory.toUnit_unique _ _ }

/-- The actual same-O terminal enrichment with its original dagger. -/
def terminalFixedDagger (O : Type u) : FixedDaggerCategory O :=
  ⟨terminalFixed O, terminalDagger O⟩

/-- The full original functor to the same-O terminal also preserves its dagger. -/
def daggerToTerminal {O : Type u} (C : FixedDaggerCategory O) : C ⟶ terminalFixedDagger O where
  underlying := toTerminal C.underlying
  map_dagger _ _ := CartesianMonoidalCategory.toUnit_unique _ _

/-- The original terminal dagger groupoid is strict in the same original degree categories. -/
def strictDaggerTerminal (O : Type u) : FixedStrictDaggerGroupoids O :=
  ⟨terminalFixedDagger O, terminal_strict O⟩

/-- The entire unique original strict dagger functor to the actual terminal. -/
def strictDaggerToTerminal {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    C ⟶ strictDaggerTerminal O := ObjectProperty.homMk (daggerToTerminal C.obj)

/-- The full native terminal universal property retains the exact original dagger category. -/
def strictDaggerTerminalIsTerminal (O : Type u) : IsTerminal (strictDaggerTerminal O) :=
  IsTerminal.ofUniqueHom strictDaggerToTerminal (by
    intro C F
    apply ObjectProperty.hom_ext
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro x y
    exact CartesianMonoidalCategory.toUnit_unique _ _)

/-- Native terminal existence holds in the unchanged original strict dagger category. -/
instance strictDaggerHasTerminal (O : Type u) : HasTerminal (FixedStrictDaggerGroupoids O) :=
  (strictDaggerTerminalIsTerminal O).hasTerminal

/-- The original strict terminal map is a fibration in the exact Homwise class. -/
theorem strictToTerminal_fibration {O : Type u} (C : FixedStrictGroupoids O) :
    Fibration (strictToTerminal C) := by
  apply (strict_fibration_iff _).2
  intro x y
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact (isFibrant_iff_of_isTerminal (CartesianMonoidalCategory.toUnit _)
    CartesianMonoidalCategory.isTerminalTensorUnit).1 inferInstance

/-- Every actual original strict groupoid is fibrant for the specified Homwise fibrations. -/
instance strictIsFibrant {O : Type u} (C : FixedStrictGroupoids O) : IsFibrant C := by
  letI : (fibrations (FixedStrictGroupoids O)).RespectsIso := by
    change (strictFibrations O).RespectsIso
    unfold strictFibrations
    infer_instance
  exact (isFibrant_iff_of_isTerminal (strictToTerminal C) (strictTerminalIsTerminal O)).2
    (strictToTerminal_fibration C)

/-- The actual strict dagger terminal map is a fibration on every unchanged original Hom. -/
theorem strictDaggerToTerminal_fibration {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    Fibration (strictDaggerToTerminal C) := by
  apply (strictDagger_fibration_iff _).2
  intro x y
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact (isFibrant_iff_of_isTerminal (CartesianMonoidalCategory.toUnit _)
    CartesianMonoidalCategory.isTerminalTensorUnit).1 inferInstance

/-- Every actual original strict dagger groupoid is fibrant in the exact Homwise class. -/
instance strictDaggerIsFibrant {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    IsFibrant C := by
  letI : (fibrations (FixedStrictDaggerGroupoids O)).RespectsIso := by
    change (strictDaggerFibrations O).RespectsIso
    unfold strictDaggerFibrations
    infer_instance
  exact (isFibrant_iff_of_isTerminal (strictDaggerToTerminal C)
    (strictDaggerTerminalIsTerminal O)).2 (strictDaggerToTerminal_fibration C)

end

end DaggerOriginalFixedObjectGroupoidTerminals
