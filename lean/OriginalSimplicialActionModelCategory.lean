import OriginalSimplicialActionFreeGenerators
import OriginalActionFreeCoyoneda
import TopCatModelCategory.TopPackage
import TopCatModelCategory.SSet.SmallObject

/-!
# The projective model structure on original C₂-simplicial actions

Weak equivalences and fibrations are detected on the unchanged underlying simplicial map.
The original free simplicial boundaries and horns supply the generators. Native finite
simplicial presentability, the free Hom adjunction and the action forgetful functor give the
small-object condition. Cofree product lifting gives acyclicity. The native model package
then supplies both factorization systems and all model-category axioms for the literal action
category, with no projective-model existence assumption.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra Opposite
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalSimplicialActionFreeGenerators
open DaggerOriginalActionFreeCoyoneda
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalSimplicialActionModelCategory

noncomputable section

/-- Projective weak equivalences are literal weak equivalences of the underlying simplicial map.
-/
def projectiveWeakEquivalences : MorphismProperty (Action SSet.{u} C2.{u}) :=
  (weakEquivalences SSet.{u}).inverseImage (Action.forget SSet.{u} C2.{u})

instance weakTwoOutOfThree : projectiveWeakEquivalences.{u}.HasTwoOutOfThreeProperty := by
  unfold projectiveWeakEquivalences
  infer_instance

instance weakStableUnderRetracts : projectiveWeakEquivalences.{u}.IsStableUnderRetracts := by
  unfold projectiveWeakEquivalences
  infer_instance

/-- Native weak-equivalence data with exactly the original underlying weak class. -/
scoped instance weakStructure : CategoryWithWeakEquivalences (Action SSet.{u} C2.{u}) where
  weakEquivalences := projectiveWeakEquivalences

/-- Native cofibrations use left lifting against original free-boundary right lifting. -/
scoped instance cofStructure : CategoryWithCofibrations (Action SSet.{u} C2.{u}) where
  cofibrations := I.rlp.llp

/-- Native fibrations use original free-horn right lifting. -/
scoped instance fibStructure : CategoryWithFibrations (Action SSet.{u} C2.{u}) where
  fibrations := J.rlp

open scoped DaggerOriginalSimplicialActionModelCategory

/-- The native action weak class is precisely the original underlying weak class. -/
theorem weakEquivalence_iff_underlying {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    WeakEquivalence p ↔ WeakEquivalence p.hom := by
  rw [weakEquivalence_iff]
  exact (weakEquivalence_iff p.hom).symm

/-- Free-boundary lifting in the free-horn right class is exactly original weak equivalence. -/
theorem fibration_is_trivial_iff {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y)
    (hp : J.rlp p) : I.rlp p ↔ WeakEquivalence p := by
  rw [I_rlp_iff_trivialFibration, weakEquivalence_iff_underlying]
  exact and_iff_right ((J_rlp_iff_fibration p).1 hp)

/-- The original free-horn left class is acyclic in the unchanged projective weak class. -/
theorem J_rlp_llp_le_weakEquivalences : J.{u}.rlp.llp ≤ weakEquivalences (Action SSet.{u} C2.{u}) :=
  fun _ _ i hi ↦ (weakEquivalence_iff i).1
    ((weakEquivalence_iff_underlying i).2 (J_rlp_llp_underlying_weakEquivalence i hi))

/-- The required countable free-horn cell composites are original projective weak equivalences.
-/
theorem infiniteCompositions_J_le_weakEquivalences :
    (coproducts.{u} J.{u}).pushouts.transfiniteCompositionsOfShape ℕ ≤
      weakEquivalences (Action SSet.{u} C2.{u}) := by
  have h : (coproducts.{u} J.{u}).pushouts ≤ J.{u}.rlp.llp :=
    (pushouts_monotone J.coproducts_le_llp_rlp).trans (MorphismProperty.pushouts_le)
  intro X Y f hf
  obtain ⟨hf⟩ := hf
  apply J_rlp_llp_le_weakEquivalences
  exact (J.rlp.llp.transfiniteCompositionsOfShape_le ℕ) f ⟨hf.ofLE h⟩

/-- Original finite free simplicial sources preserve every required countable cell colimit. -/
theorem finiteFreeSource_preservesColimit (T : SSet.{u}) [SSet.IsFinite T]
    {X Y : Action SSet.{u} C2.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u} (fun (_ : ℕ) ↦ (I.{u} ⊔ J.{u}).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (op (free.obj T))) := by
  have : PreservesColimit (hf.F ⋙ Action.forget SSet.{u} C2.{u}) (coyoneda.obj (op T)) :=
    inferInstance
  have : PreservesColimit hf.F
      (Action.forget SSet.{u} C2.{u} ⋙ coyoneda.obj (op T)) := inferInstance
  exact preservesColimit_of_natIso hf.F (freeCoyonedaIso SSet.{u} C2.{u} T).symm

/-- The full native package has original free simplicial generators and proved smallness. -/
def packageProjective : TopPackage.{u} (Action SSet.{u} C2.{u}) where
  I' := I
  J' := J
  S' := Set.range (fun (T : {T : SSet.{u} | SSet.IsFinite T}) ↦ free.obj T.val)
  hasTwoOutOfThreeProperty := inferInstanceAs projectiveWeakEquivalences.HasTwoOutOfThreeProperty
  isStableUnderRetracts := inferInstanceAs projectiveWeakEquivalences.IsStableUnderRetracts
  rlp_I'_le_rlp_J' := I_rlp_le_J_rlp
  fibration_is_trivial_iff' := fibration_is_trivial_iff
  src_I_le_S' := by
    rintro A B i ⟨n⟩
    exact ⟨⟨SSet.boundary n, by
      change SSet.IsFinite (SSet.boundary n : SSet.{u})
      infer_instance⟩, rfl⟩
  src_J_le_S' := by
    intro A B i hi
    simp only [J, iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    exact ⟨⟨SSet.horn (n + 1) k, by
      change SSet.IsFinite (SSet.horn (n + 1) k : SSet.{u})
      infer_instance⟩, rfl⟩
  infiniteCompositions_le_W' := infiniteCompositions_J_le_weakEquivalences
  preservesColimit' := by
    rintro A ⟨⟨T, hT⟩, rfl⟩ X Y f hf
    have : SSet.IsFinite T := hT
    exact finiteFreeSource_preservesColimit T f hf

/-- The actual projective model structure on the literal original C₂-simplicial action category.
-/
scoped instance modelStructure : ModelCategory (Action SSet.{u} C2.{u}) :=
  packageProjective.modelCategory rfl rfl

/-- Native projective action fibrations are precisely underlying native simplicial fibrations.
-/
theorem fibration_iff_underlying {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    Fibration p ↔ Fibration p.hom := by
  rw [fibration_iff]
  exact J_rlp_iff_fibration p

/-- Native projective cofibrations are exactly the original free-boundary lifting class. -/
theorem cofibration_iff_original {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    Cofibration p ↔ I.rlp.llp p := by
  rw [cofibration_iff]
  rfl

/-- The same projective action is fibrant exactly when its unchanged underlying object is. -/
theorem isFibrant_iff_underlying (X : Action SSet.{u} C2.{u}) :
    IsFibrant X ↔ IsFibrant X.V := by
  let ht : IsTerminal ((Action.forget SSet.{u} C2.{u}).obj (⊤_ (Action SSet.{u} C2.{u}))) :=
    IsTerminal.isTerminalObj (Action.forget SSet.{u} C2.{u}) _ terminalIsTerminal
  rw [isFibrant_iff, fibration_iff_underlying]
  exact (isFibrant_iff_of_isTerminal (terminal.from X).hom ht).symm

end

end DaggerOriginalSimplicialActionModelCategory
