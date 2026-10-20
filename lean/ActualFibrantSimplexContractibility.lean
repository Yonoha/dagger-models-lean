import ActualThinReplacementExtension
import ActualOrdinalRigidificationComparison

/-! Contractibility of all nonempty Homs in the rigidification of the actual fibrant simplex gadget. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualFibrantGadgetData
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualFibrantSimplexContractibility
noncomputable section

local instance (n : ℕ) : EnrichedCategory SSet.{u} (ULift.{u} (Fin (n + 1))) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The native simplex comparison is surjective on its literal original object types. -/
theorem comparison_surjective (n : ℕ) :
    Function.Surjective (DaggerActualOrdinalRigidificationComparison.comparison.{u} n).obj := by
  intro y
  let e := rigidificationSimplexIso.{u}.app ⦋n⦌
  let z : (cosimplicialThickening.obj ⦋n⦌).Obj := ⟨y⟩
  refine ⟨e.inv.obj z, ?_⟩
  change (e.hom.obj (e.inv.obj z)).as = y
  have h := congrArg (fun f : cosimplicialThickening.obj ⦋n⦌ ⟶
      cosimplicialThickening.obj ⦋n⦌ ↦ f.obj z) e.inv_hom_id
  exact congrArg (fun w ↦ w.as) h

/-- The original C of the constant enriched ordinal's nerve has contractible nonempty Homs. -/
theorem nerveOrdinal_hom_toUnit_GW (n : ℕ)
    (a b : (rigidification.obj
      (coherentNerve.obj (constant (ULift.{u} (Fin (n + 1)))))).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  let e := rigidification.mapIso (DaggerActualThinConstantCoherentNerve.ordinalNerveIso.{u} n)
  let p := e.hom.map a b
  let Y : SSet.{u} := (e.hom.obj a ⟶[SSet.{u}] e.hom.obj b)
  have : WeakEquivalence p := inferInstance
  obtain ⟨v⟩ := h
  have ht : DaggerSSetGluing.GW (toUnit Y) :=
    DaggerActualRigidificationSimplexHomContractibility.simplex_hom_toUnit_GW n _ _
      ⟨p.app (op ⦋0⦌) v⟩
  have : WeakEquivalence (toUnit Y) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr ht
  have he : p ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The actual F(Δ[n]) = N(R(C(Δ[n]))) has weakly contractible nonempty rigidification Homs.
This is unconditional on the ordinary counit and on any supplied comparison weak equivalence. -/
theorem simplex_gadget_hom_toUnit_GW (n : ℕ)
    (a b : (rigidification.obj (gadget.obj (Δ[n] : SSet.{u}))).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  obtain ⟨q, _, ho, hh⟩ := DaggerActualThinReplacementExtension.exists_trivial_extension
    (ULift.{u} (Fin (n + 1)))
    (DaggerActualOrdinalRigidificationComparison.comparison n) (comparison_surjective n)
    (DaggerActualOrdinalRigidificationComparison.comparison_hom_GW n)
  let f := rigidification.map (coherentNerve.map q)
  let p := f.map a b
  let Y : SSet.{u} := (f.obj a ⟶[SSet.{u}] f.obj b)
  have hp : DaggerSSetGluing.GW p :=
    (DaggerActualNerveTrivialFibrationRigidification.rigidification_nerve_local_and_surjective
      q ho hh).1 a b
  have : WeakEquivalence p := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hp
  obtain ⟨v⟩ := h
  have ht : DaggerSSetGluing.GW (toUnit Y) :=
    nerveOrdinal_hom_toUnit_GW n _ _ ⟨p.app (op ⦋0⦌) v⟩
  have : WeakEquivalence (toUnit Y) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr ht
  have he : p ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerActualFibrantSimplexContractibility
