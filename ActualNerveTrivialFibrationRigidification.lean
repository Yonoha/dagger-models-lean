import ProofActualNecklaceConeBridge

/-! Reuse the existing full boundary-lifting theorem for the literal original C and N. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOrdinaryRigidificationCof DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualNerveTrivialFibrationRigidification
noncomputable section

/-- Every native Kan trivial fibration has geometrically weak original rigidification Homs.
No injectivity of its vertex map is required. -/
theorem trivialFibration_local_and_surjective {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    (∀ a b : (OrdinaryRigidification.rigidification.obj X).Obj,
      GW ((OrdinaryRigidification.rigidification.map p).map a b)) ∧
      Function.Surjective (OrdinaryRigidification.rigidification.map p).obj :=
  DaggerOriginalRigidificationBoundaryWeak.boundary_lifting_local_and_surjective p
    ((KanQuillenReuse.boundary_lifting_iff_trivial p).mpr ⟨inferInstance, inferInstance⟩)

/-- The original coherent nerve preserves object-surjective local trivial fibrations. -/
theorem nerve_trivialFibration {A B : SimplicialCat.{u, u}} (p : A ⟶ B)
    (ho : Function.Surjective p.obj)
    (hh : ∀ a b : A.Obj, trivialFibrations SSet.{u} (p.map a b)) :
    trivialFibrations SSet.{u} (OrdinaryRigidification.coherentNerve.map p) := by
  rw [mem_trivialFibrations_iff]
  apply (KanQuillenReuse.boundary_lifting_iff_trivial _).mp
  apply boundary_lifting p
  refine ⟨ho, fun a b ↦ ?_⟩
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp (hh a b)
  have : WeakEquivalence (p.map a b) := hw
  exact ⟨hf, (weakEquivalence_iff_GW _).mp hw⟩

/-- The actual composite C(N(p)) has weak Hom maps and a surjective object map. -/
theorem rigidification_nerve_local_and_surjective {A B : SimplicialCat.{u, u}}
    (p : A ⟶ B) (ho : Function.Surjective p.obj)
    (hh : ∀ a b : A.Obj, trivialFibrations SSet.{u} (p.map a b)) :
    (∀ a b : (OrdinaryRigidification.rigidification.obj
      (OrdinaryRigidification.coherentNerve.obj A)).Obj,
      GW ((OrdinaryRigidification.rigidification.map
        (OrdinaryRigidification.coherentNerve.map p)).map a b)) ∧
      Function.Surjective (OrdinaryRigidification.rigidification.map
        (OrdinaryRigidification.coherentNerve.map p)).obj := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp (nerve_trivialFibration p ho hh)
  have : Fibration (OrdinaryRigidification.coherentNerve.map p) := hf
  have : WeakEquivalence (OrdinaryRigidification.coherentNerve.map p) := hw
  exact trivialFibration_local_and_surjective _

end
end DaggerActualNerveTrivialFibrationRigidification
