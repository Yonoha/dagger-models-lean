import OriginalActionFreeForgetAdjunction
import OriginalEC2BorelModelCompatibility

/-!
# Native free boundary and horn generators for the Borel classes

These are free actions on the original realized simplicial boundaries and horns.
Their right lifting classes are identified with the literal inverse images of
TopCat's generating right lifting classes. This supplies generator recognition;
it does not assert the remaining small-object or acyclicity conditions.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalActionFreeForgetAdjunction DaggerOriginalEC2BorelCofibrancy
open DaggerOriginalEC2BorelModelCompatibility

universe u v

namespace DaggerOriginalBorelFreeGenerators

noncomputable section

/-- The native regular free topological C₂ action functor. -/
abbrev free : TopCat.{u} ⥤ Action TopCat.{u} C2.{u} :=
  freeActionFunctor TopCat.{u} C2.{u}

/-- Free realized boundary inclusions. -/
def I : MorphismProperty (Action TopCat.{u} C2.{u}) :=
  ofHoms (fun n ↦ free.map (SSet.toTop.map (SSet.boundary.{u} n).ι))

/-- Free realized horn inclusions in positive dimensions. -/
def J : MorphismProperty (Action TopCat.{u} C2.{u}) :=
  ⨆ n, ofHoms (fun i ↦ free.map (SSet.toTop.map (SSet.horn.{u} (n + 1) i).ι))

instance : IsSmall.{v} I.{u} := by dsimp [I]; infer_instance
instance : IsSmall.{v} J.{u} := by dsimp [J]; infer_instance

/-- Right lifting against free boundaries is underlying right lifting against boundaries. -/
theorem I_rlp_iff {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    I.rlp p ↔ TopCat.modelCategory.I.rlp p.hom := by
  constructor
  · rintro hp _ _ _ ⟨n⟩
    rw [← freeAction_lifting_iff TopCat C2]
    exact hp _ ⟨n⟩
  · rintro hp _ _ _ ⟨n⟩
    rw [freeAction_lifting_iff TopCat C2]
    exact hp _ ⟨n⟩

/-- Right lifting against free horns is underlying right lifting against horns. -/
theorem J_rlp_iff {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    J.rlp p ↔ TopCat.modelCategory.J.rlp p.hom := by
  constructor
  · intro hp _ _ _ h
    simp only [TopCat.modelCategory.J, iSup_iff] at h
    obtain ⟨n, ⟨i⟩⟩ := h
    rw [← freeAction_lifting_iff TopCat C2]
    apply hp
    simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩
  · intro hp _ _ _ h
    simp only [J, iSup_iff] at h
    obtain ⟨n, ⟨i⟩⟩ := h
    rw [freeAction_lifting_iff TopCat C2]
    apply hp
    simp only [TopCat.modelCategory.J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

/-- Free-boundary right lifting is the already proved original Borel trivial-fibration class. -/
theorem I_rlp_eq_borelTrivialFibrations : I.{u}.rlp = borelTrivialFibrations.{u} := by
  ext X Y p
  exact I_rlp_iff p

/-- The original Borel cofibration class has the literal free-boundary generators. -/
theorem I_rlp_llp_eq_borelCofibrations : I.{u}.rlp.llp = borelCofibrations.{u} := by
  rw [I_rlp_eq_borelTrivialFibrations]
  rfl

/-- Free-boundary right lifting is underlying fibration and weak equivalence. -/
theorem I_rlp_iff_trivialFibration {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    I.rlp p ↔ Fibration p.hom ∧ WeakEquivalence p.hom := by
  rw [I_rlp_eq_borelTrivialFibrations]
  exact borelTrivialFibrations_iff p

/-- Free-horn right lifting is exactly an underlying native TopCat fibration. -/
theorem J_rlp_iff_fibration {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    J.rlp p ↔ Fibration p.hom := by
  rw [J_rlp_iff, fibration_iff]
  rfl

/-- The boundary right lifting class is contained in the horn right lifting class. -/
theorem I_rlp_le_J_rlp : I.{u}.rlp ≤ J.{u}.rlp := by
  intro X Y p hp
  exact (J_rlp_iff_fibration p).2 ((I_rlp_iff_trivialFibration p).1 hp).1

end

end DaggerOriginalBorelFreeGenerators
