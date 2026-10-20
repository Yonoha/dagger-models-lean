import ActualFibrantSimplexContractibility
import ActualRightConeObjectClassification
import ActualCounitRightConeRelativeDirectedHomotopy

/-! The same thin-ordinal route applies to every original collapsed-face right cone. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualFibrantGadgetData
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy DaggerOriginalEnrichedHomTransport
open DaggerActualRigidificationDirectedIntervalObjects
open DaggerActualCounitRightConeRelativeDirectedHomotopy
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualFibrantRightConeContractibility
noncomputable section

local instance (n : ℕ) : EnrichedCategory SSet.{u} (ULift.{u} (Fin (n + 1))) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The saved relative homotopy fixes the full line through every original cone object. -/
theorem line_fixed (n : ℕ) (a : (rigidification.obj (cone.{u} n)).Obj) :
    vertexLine (cone n) a ≫ relativeHomotopy n =
      SSet.const ((RigidificationVertices.vertexEquiv (cone n)).symm a) := by
  obtain ⟨b, rfl⟩ := (DaggerActualRightConeObjectClassification.objectEquiv n).surjective a
  cases b
  · exact alphaLine_fixed n
  · exact omegaLine_fixed n

/-- The same actual retraction is weak on every Hom, including reverse and diagonal Homs. -/
theorem retraction_all_hom_GW (n : ℕ) (a b : (rigidification.obj (cone.{u} n)).Obj) :
    DaggerSSetGluing.GW ((rigidification.map (projection n ≫ lastEdge n)).map a b) :=
  DaggerActualRigidificationRelativeDirectedHomotopy.endomorphism_GW
    (cone n) (relativeHomotopy n) (projection n ≫ lastEdge n)
    (relativeHomotopy_time_zero n) (relativeHomotopy_time_one n)
    a b (line_fixed n a) (line_fixed n b)

/-- The original right-cone edge projection has weak maps on all Homs. -/
theorem projection_all_hom_GW (n : ℕ) (a b : (rigidification.obj (cone.{u} n)).Obj) :
    DaggerSSetGluing.GW ((rigidification.map (projection n)).map a b) := by
  have hs : rigidification.map (lastEdge.{u} n) ≫ rigidification.map (projection n) =
      𝟙 (rigidification.obj (Δ[1] : SSet.{u})) := by
    rw [← Functor.map_comp, lastEdge_projection, CategoryTheory.Functor.map_id]
  apply DaggerOriginalEnrichedHomRetract.GW_of_retract
    (rigidification.map (projection n)) (rigidification.map (lastEdge n)) hs
  have hc : rigidification.map (projection.{u} n) ≫ rigidification.map (lastEdge n) =
      rigidification.map (projection n ≫ lastEdge n) := (Functor.map_comp _ _ _).symm
  exact (GW_functorHom_congr hc a b).mpr (retraction_all_hom_GW n a b)

/-- The same original edge projection is surjective, with its original last-edge section. -/
theorem projection_surjective (n : ℕ) :
    Function.Surjective (rigidification.map (projection.{u} n)).obj := by
  intro x
  refine ⟨(rigidification.map (lastEdge n)).obj x, ?_⟩
  have hs : rigidification.map (lastEdge.{u} n) ≫ rigidification.map (projection n) =
      𝟙 (rigidification.obj (Δ[1] : SSet.{u})) := by
    rw [← Functor.map_comp, lastEdge_projection, CategoryTheory.Functor.map_id]
  exact congrArg (fun f : rigidification.obj (Δ[1] : SSet.{u}) ⟶
    rigidification.obj (Δ[1] : SSet.{u}) ↦ f.obj x) hs

/-- The actual cone comparison retains the original edge projection and original ordinal map. -/
def comparison (n : ℕ) : rigidification.obj (cone.{u} n) ⟶
    constant (ULift.{u} (Fin 2)) :=
  rigidification.map (projection n) ≫ DaggerActualOrdinalRigidificationComparison.comparison 1

/-- The whole comparison is surjective on objects. -/
theorem comparison_surjective (n : ℕ) : Function.Surjective (comparison.{u} n).obj :=
  (DaggerActualFibrantSimplexContractibility.comparison_surjective 1).comp
    (projection_surjective n)

/-- Every literal cone comparison Hom is weak, without a nonempty-Hom restriction. -/
theorem comparison_hom_GW (n : ℕ) (a b : (rigidification.obj (cone.{u} n)).Obj) :
    DaggerSSetGluing.GW ((comparison n).map a b) := by
  have : WeakEquivalence ((rigidification.map (projection n)).map a b) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (projection_all_hom_GW n a b)
  have : WeakEquivalence ((DaggerActualOrdinalRigidificationComparison.comparison 1).map
      ((rigidification.map (projection n)).obj a)
      ((rigidification.map (projection n)).obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualOrdinalRigidificationComparison.comparison_hom_GW 1 _ _)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence ((rigidification.map (projection n)).map a b ≫ _)
  infer_instance

/-- Every nonempty Hom in the actual rigidified fibrant right-cone gadget is weakly contractible.
The proof uses only saved cone geometry and native trivial-fibration rigidification. -/
theorem cone_gadget_hom_toUnit_GW (n : ℕ)
    (a b : (rigidification.obj (gadget.obj (cone.{u} n))).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) := by
  obtain ⟨q, _, ho, hh⟩ := DaggerActualThinReplacementExtension.exists_trivial_extension
    (ULift.{u} (Fin 2)) (comparison n) (comparison_surjective n) (comparison_hom_GW n)
  let f := rigidification.map (coherentNerve.map q)
  let p := f.map a b
  let Y : SSet.{u} := (f.obj a ⟶[SSet.{u}] f.obj b)
  have hp : DaggerSSetGluing.GW p :=
    (DaggerActualNerveTrivialFibrationRigidification.rigidification_nerve_local_and_surjective
      q ho hh).1 a b
  have : WeakEquivalence p := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hp
  obtain ⟨v⟩ := h
  have ht : DaggerSSetGluing.GW (toUnit Y) :=
    DaggerActualFibrantSimplexContractibility.nerveOrdinal_hom_toUnit_GW 1 _ _
      ⟨p.app (op ⦋0⦌) v⟩
  have : WeakEquivalence (toUnit Y) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr ht
  have he : p ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerActualFibrantRightConeContractibility
