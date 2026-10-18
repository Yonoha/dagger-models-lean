import RigidificationCofNerveLift

open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryRigidificationCof

noncomputable section

/-- Actual coherentNerve has boundary RLP, including dimension zero. -/
theorem nerve_boundary_rlp {A B : SC.{u}} (p : A ⟶ B)
    (hp : ordinaryTrivialFibrations p) : SSet.modelCategoryQuillen.I.rlp (N.map p) :=
  (DaggerModels.KanQuillenReuse.boundary_lifting_iff_rlp (N.map p)).mp
    (boundary_lifting p hp)

/-- Boundary-cell generation applies to EVERY original simplicial monomorphism. -/
theorem nerve_mono_lifting {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    {A B : SC.{u}} (p : A ⟶ B) (hp : ordinaryTrivialFibrations p) :
    HasLiftingProperty i (N.map p) := by
  have h := nerve_boundary_rlp p hp
  rw [DaggerModels.SSetBoundaryCells.I_rlp_eq_monomorphisms_rlp] at h
  exact h i (show Mono i from inferInstance)

/-- FULL T03, with the literal original rigidification and ordinary lifting class. -/
theorem mono_rigidification_cofibration {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    ordinaryCofibrations (C.map i) := by
  intro A B p hp
  exact (Adjunction.hasLiftingProperty_iff
    DaggerModels.OrdinaryRigidification.rigidificationCoherentNerveAdjunction i p).mpr
      (nerve_mono_lifting i p hp)

/-- The complete original-map target with all right-class hypotheses exposed. -/
theorem mono_rigidification_lifting {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    {A B : SC.{u}} (p : A ⟶ B) (ho : Function.Surjective p.obj)
    (hh : ∀ x y, Fibration (p.map x y) ∧ geometric (p.map x y)) :
    HasLiftingProperty (C.map i) p :=
  mono_rigidification_cofibration i p ⟨ho, hh⟩

end

end DaggerOrdinaryRigidificationCof
