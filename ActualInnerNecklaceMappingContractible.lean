import ActualOriginalNecklaceInclusionWeak
import ActualSimplexOuterMappingContractible
import ChosenNecklaceCategory

/-! The SAME inner-horn replacement and BOTH ORIGINAL necklace endpoints have contractible mapping.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace DaggerNativeInnerHornFactorization
open DaggerNativeJoyalMappingTest DaggerActualGeneralRightConeMapping
open DaggerActualInnerConeIntervalComparison DaggerActualRightMappingWeakInvariance
open DaggerActualSimplexOuterMappingContractible DaggerActualOriginalNecklaceInclusionWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerNecklaceMappingContractible
noncomputable section

variable (T : NecklaceCode)

local instance targetQuasicategory : (Δ[T.len] : SSet.{u}).Quasicategory :=
  simplex_quasicategory T.len

def comparison : replacement.obj (NecklaceCode.toSSet.{u} T) ⟶ (Δ[T.len] : SSet.{u}) :=
  (DaggerActualInnerReplacementExtensions.exists_extension T.inclusion).choose

theorem unit_comparison : unit.app (NecklaceCode.toSSet.{u} T) ≫ comparison T = T.inclusion :=
  (DaggerActualInnerReplacementExtensions.exists_extension T.inclusion).choose_spec

theorem comparison_categorical_weak : weakCategoricalEquivalences (comparison.{u} T) :=
  weakCategoricalEquivalences.of_precomp (unit.app T.toSSet) (comparison T)
    (DaggerNativeInnerJoyalMappingWeak.unit_weak T.toSSet)
    ((unit_comparison T).symm ▸ original_inclusion_weak T)

def sourceFirst : (replacement.obj (NecklaceCode.toSSet.{u} T)).obj (op ⦋0⦌) :=
  (unit.app T.toSSet).app (op ⦋0⦌) T.first

def sourceLast : (replacement.obj (NecklaceCode.toSSet.{u} T)).obj (op ⦋0⦌) :=
  (unit.app T.toSSet).app (op ⦋0⦌) T.last

theorem inclusion_first : (NecklaceCode.inclusion.{u} T).app (op ⦋0⦌) T.first =
    firstVertex T.len := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  simpa only [NecklaceCode.first, firstVertex, Equiv.apply_symm_apply] using
    T.inclusion_vertex (ULift.up 0)

theorem inclusion_last : (NecklaceCode.inclusion.{u} T).app (op ⦋0⦌) T.last =
    lastVertex T.len := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  simpa only [NecklaceCode.last, lastVertex, Equiv.apply_symm_apply] using
    T.inclusion_vertex (ULift.up (Fin.last T.len))

theorem comparison_first : (comparison.{u} T).app (op ⦋0⦌) (sourceFirst T) =
    firstVertex T.len :=
  (congrFun (NatTrans.congr_app (unit_comparison T) (op ⦋0⦌)) T.first).trans (inclusion_first T)

theorem comparison_last : (comparison.{u} T).app (op ⦋0⦌) (sourceLast T) = lastVertex T.len :=
  (congrFun (NatTrans.congr_app (unit_comparison T) (op ⦋0⦌)) T.last).trans (inclusion_last T)

def mappingComparison :
    rightMapping (replacement.obj T.toSSet) (sourceFirst.{u} T) (sourceLast T) ⟶
      rightMapping (Δ[T.len] : SSet.{u}) (firstVertex T.len) (lastVertex T.len) :=
  mapTo (comparison T) (sourceFirst T) (sourceLast T) (firstVertex T.len) (lastVertex T.len)
    (comparison_first T) (comparison_last T)

theorem mappingComparison_weak : WeakEquivalence (mappingComparison.{u} T) := by
  have h : ∀ (c d : (Δ[T.len] : SSet.{u}).obj (op ⦋0⦌))
      (hc : (comparison T).app (op ⦋0⦌) (sourceFirst T) = c)
      (hd : (comparison T).app (op ⦋0⦌) (sourceLast T) = d),
      WeakEquivalence (mapTo (comparison T) (sourceFirst T) (sourceLast T) c d hc hd) := by
    intro c d hc hd
    subst c
    subst d
    exact map_weak_of_categorical_weak (comparison T) (comparison_categorical_weak T)
      (sourceFirst T) (sourceLast T)
  exact h _ _ (comparison_first T) (comparison_last T)

theorem innerNecklace_mapping_kan :
    (rightMapping (replacement.obj T.toSSet) (sourceFirst.{u} T) (sourceLast T)).KanComplex :=
  DaggerActualGeneralRightConeKan.rightMapping_kan _ _ _

theorem innerNecklace_mapping_point_weak : WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from
      (rightMapping (replacement.obj T.toSSet) (sourceFirst.{u} T) (sourceLast T))) := by
  have : WeakEquivalence (mappingComparison.{u} T) := mappingComparison_weak T
  have : WeakEquivalence (outerMappingIso.{u} T.len).hom := outer_mapping_point_weak T.len
  have he : mappingComparison T ≫ (outerMappingIso T.len).hom =
      SSet.stdSimplex.isTerminalObj₀.from _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← he]
  infer_instance

theorem innerNecklace_mapping_toUnit_weak : WeakEquivalence
    (toUnit (rightMapping (replacement.obj T.toSSet) (sourceFirst.{u} T) (sourceLast T))) := by
  let E := rightMapping (replacement.obj T.toSSet) (sourceFirst.{u} T) (sourceLast T)
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from E) :=
    innerNecklace_mapping_point_weak T
  have he : SSet.stdSimplex.isTerminalObj₀.from E ≫ e.hom = toUnit E :=
    isTerminalTensorUnit.hom_ext _ _
  rw [← he]
  infer_instance

end
end DaggerActualInnerNecklaceMappingContractible
