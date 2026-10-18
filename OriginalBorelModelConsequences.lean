import OriginalBorelModelCategory

/-!
# Native consequences of the actual Borel model structure

The original realized EC₂ action is cofibrant, and every topological C₂ action
is fibrant. The free/forgetful adjunction preserves the native cofibration and
fibration classes required for its Quillen behavior. No mapping-space weak
equivalence preservation theorem is assumed here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2CanonicalBorelCofibrancy DaggerOriginalEC2BorelModelCompatibility
open DaggerOriginalActionFreeForgetAdjunction DaggerOriginalBorelFreeGenerators
open DaggerOriginalBorelModelCategory DaggerOriginalBorelGeneratorAcyclicity
open DaggerOriginalBorelUnderlyingCofibrations

universe u

namespace DaggerOriginalBorelModelConsequences

noncomputable section

/-- The literal original realized EC₂ is cofibrant in the constructed Borel model structure. -/
theorem actualRealizedEC2_isCofibrant : IsCofibrant realizedEC2Action.{u} := by
  rw [isCofibrant_iff, cofibration_iff_original]
  exact actualRealizedEC2_canonicalBorelCofibrant

/-- Every literal topological C₂ action is fibrant in the constructed model structure. -/
theorem everyAction_isFibrant (X : Action TopCat.{u} C2.{u}) : IsFibrant X := by
  let ht : IsTerminal ((Action.forget TopCat C2).obj (⊤_ (Action TopCat.{u} C2.{u}))) :=
    IsTerminal.isTerminalObj (Action.forget TopCat.{u} C2.{u}) _ terminalIsTerminal
  rw [isFibrant_iff, fibration_iff_underlying]
  exact (isFibrant_iff_of_isTerminal (terminal.from X).hom ht).1 inferInstance

/-- The literal forgetful functor preserves native fibrations. -/
theorem forget_map_fibration {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    [Fibration p] : Fibration ((Action.forget TopCat C2).map p) :=
  (fibration_iff_underlying p).1 inferInstance

/-- The literal forgetful functor preserves native trivial fibrations. -/
theorem forget_map_trivialFibration {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    trivialFibrations TopCat.{u} ((Action.forget TopCat C2).map p) :=
  (mem_trivialFibrations_iff p.hom).2
    ⟨forget_map_fibration p, (weakEquivalence_iff_underlying p).1 inferInstance⟩

/-- The actual free-action functor preserves native cofibrations. -/
theorem free_map_cofibration {A B : TopCat.{u}} (i : A ⟶ B) [Cofibration i] :
    Cofibration (free.map i) := by
  rw [cofibration_iff_original]
  intro X Y p hp
  rw [freeAction_lifting_iff TopCat C2]
  have h := (borelTrivialFibrations_iff p).1 hp
  have : Fibration p.hom := h.1
  have : WeakEquivalence p.hom := h.2
  exact inferInstance

/-- The actual free-action functor preserves native trivial cofibrations. -/
theorem free_map_trivialCofibration {A B : TopCat.{u}} (i : A ⟶ B)
    [Cofibration i] [WeakEquivalence i] :
    trivialCofibrations (Action TopCat.{u} C2.{u}) (free.map i) := by
  have hi : J.rlp.llp (free.map i) := by
    intro X Y p hp
    rw [freeAction_lifting_iff TopCat C2]
    have : Fibration p.hom := (J_rlp_iff_fibration p).1 hp
    exact inferInstance
  apply (mem_trivialCofibrations_iff (free.map i)).2
  exact ⟨free_map_cofibration i,
    (weakEquivalence_iff_underlying (free.map i)).2
      (J_rlp_llp_underlying_weakEquivalence (free.map i) hi)⟩

/-- The literal forgetful functor also preserves native cofibrations. -/
theorem forget_map_cofibration {X Y : Action TopCat.{u} C2.{u}} (i : X ⟶ Y)
    [Cofibration i] : Cofibration ((Action.forget TopCat C2).map i) :=
  borelCofibration_underlying i ((cofibration_iff_original i).1 inferInstance)

/-- The literal forgetful functor also preserves native trivial cofibrations. -/
theorem forget_map_trivialCofibration {X Y : Action TopCat.{u} C2.{u}} (i : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] :
    trivialCofibrations TopCat.{u} ((Action.forget TopCat C2).map i) :=
  (mem_trivialCofibrations_iff i.hom).2
    ⟨forget_map_cofibration i, (weakEquivalence_iff_underlying i).1 inferInstance⟩

end

end DaggerOriginalBorelModelConsequences
