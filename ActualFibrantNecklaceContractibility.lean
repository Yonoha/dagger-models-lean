import ActualNecklaceOrdinalComparison
import ActualFibrantRightConeEndpoints

/-! Every selected original necklace has contractible endpoint Homs after the actual gadget unit. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualFibrantGadgetData
open DaggerChosenRigidificationNecklace NecklaceCode NecklaceThickening
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualFibrantNecklaceContractibility
noncomputable section

local instance (n : ℕ) : EnrichedCategory SSet.{u} (ULift.{u} (Fin (n + 1))) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- All nonempty Homs of the original C(F(T)) are weakly contractible for every necklace code. -/
theorem necklace_gadget_hom_toUnit_GW (T : NecklaceCode)
    (a b : (rigidification.obj (gadget.obj (toSSet.{u} T))).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  obtain ⟨q, _, ho, hh⟩ := DaggerActualThinReplacementExtension.exists_trivial_extension
    (Vertices.{u} T) (DaggerActualNecklaceOrdinalComparison.comparison T)
    (DaggerActualNecklaceOrdinalComparison.comparison_surjective T)
    (DaggerActualNecklaceOrdinalComparison.comparison_hom_GW T)
  let f := rigidification.map (coherentNerve.map q)
  let p := f.map a b
  let Y : SSet.{u} := (f.obj a ⟶[SSet.{u}] f.obj b)
  have hp : DaggerSSetGluing.GW p :=
    (DaggerActualNerveTrivialFibrationRigidification.rigidification_nerve_local_and_surjective
      q ho hh).1 a b
  have : WeakEquivalence p := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hp
  obtain ⟨v⟩ := h
  have ht : DaggerSSetGluing.GW (toUnit Y) :=
    DaggerActualFibrantSimplexContractibility.nerveOrdinal_hom_toUnit_GW T.len _ _
      ⟨p.app (op ⦋0⦌) v⟩
  have : WeakEquivalence (toUnit Y) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr ht
  have he : p ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The reused whole necklace isomorphism retains the first original vertex. -/
theorem inverse_first_obj (T : NecklaceCode) :
    (chosenNecklaceIso.{u} T).inv.obj ⟨ULift.up 0⟩ = RV T.toSSet T.first :=
  chosenNecklaceIso_inv_objects T _

/-- The same reused isomorphism retains the last original vertex. -/
theorem inverse_last_obj (T : NecklaceCode) :
    (chosenNecklaceIso.{u} T).inv.obj ⟨ULift.up (Fin.last T.len)⟩ = RV T.toSSet T.last :=
  chosenNecklaceIso_inv_objects T _

/-- A concrete joint-path vertex lies in the original necklace endpoint Hom, including point codes. -/
def endpoint_vertex (T : NecklaceCode) :
    (RV (toSSet.{u} T) T.first ⟶[SSet.{u}] RV T.toSSet T.last).obj (op ⦋0⦌) :=
  ((chosenNecklaceIso T).inv.map ⟨ULift.up 0⟩ ⟨ULift.up (Fin.last T.len)⟩ ≫
    targetHomTransport (inverse_first_obj T) (inverse_last_obj T)).app (op ⦋0⦌)
      ((CategoryTheory.Functor.const (Fin 1)).obj
        (DaggerActualNecklaceOrdinalComparison.minimalJointPath T
          (ULift.up 0) (ULift.up (Fin.last T.len)) (Fin.zero_le (Fin.last T.len))))

/-- The prescribed C(unit) images of the original necklace endpoints have weakly contractible Hom.
No nonemptiness, comparison weakness or counit weakness is assumed. -/
theorem endpoint_hom_toUnit_GW (T : NecklaceCode) :
    DaggerSSetGluing.GW (toUnit
      ((rigidification.map (DaggerActualFibrantGadgetData.unit.app (toSSet.{u} T))).obj
          (RV T.toSSet T.first) ⟶[SSet.{u}]
        (rigidification.map (DaggerActualFibrantGadgetData.unit.app T.toSSet)).obj
          (RV T.toSSet T.last))) := by
  apply necklace_gadget_hom_toUnit_GW
  exact ⟨((rigidification.map (DaggerActualFibrantGadgetData.unit.app T.toSSet)).map
    (RV T.toSSet T.first) (RV T.toSSet T.last)).app (op ⦋0⦌) (endpoint_vertex T)⟩

end
end DaggerActualFibrantNecklaceContractibility
