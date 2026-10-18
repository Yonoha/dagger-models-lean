import ActualIteratedGadgetProperties
import ActualRightConeKanMapping
import ActualQSingularFibrantWeakEquivalences
import ActualFibrantGadgetVertices

/-! Right-cone mapping objects of every positive-level selected gadget are Kan and contractible. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerActualIteratedGadgetData
open OriginalOrdinaryLocalKanReplacement
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitBNextConeEvaluationIndex
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualIteratedGadgetRightMapping
noncomputable section

/-- The same original local Kan unit carries endpoint contractibility to its actual output Hom. -/
theorem replacement_endpoint_GW (P : BaseCode) (k : ℕ) :
    DaggerSSetGluing.GW (toUnit
      ((unit.app (rigidification.obj (spaceAt.{u} P k))).obj
          (RV (spaceAt P k) (alphaAt P k)) ⟶[SSet.{u}]
        (unit.app (rigidification.obj (spaceAt.{u} P k))).obj
          (RV (spaceAt P k) (omegaAt P k)))) := by
  let C := rigidification.obj (spaceAt.{u} P k)
  let a := RV (spaceAt P k) (alphaAt P k)
  let b := RV (spaceAt P k) (omegaAt P k)
  let f := (unit.app C).map a b
  let Y : SSet.{u} := ((unit.app C).obj a ⟶[SSet.{u}] (unit.app C).obj b)
  have : WeakEquivalence f := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (OriginalOrdinaryLocalKanReplacementHom.unit_hom_geometric C a b)
  have : WeakEquivalence (toUnit (a ⟶[SSet.{u}] b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedGadgetProperties.endpoint_hom_GW ⟨P, k⟩)
  have he : f ≫ toUnit Y = toUnit (a ⟶[SSet.{u}] b) := isTerminalTensorUnit.hom_ext _ _
  have : WeakEquivalence (f ≫ toUnit Y) := by rw [he]; infer_instance
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    (weakEquivalence_of_precomp f (toUnit Y))

/-- The existing Q-singular functor preserves weak contractibility of every Kan object. -/
theorem singular_toUnit_GW (X : SSet.{u}) [X.KanComplex]
    (h : DaggerSSetGluing.GW (toUnit X)) :
    DaggerSSetGluing.GW (toUnit (singular.obj X)) := by
  have : singular.{u}.IsRightAdjoint := ⟨_, ⟨realizationSingularAdjunction⟩⟩
  have : IsFibrant (𝟙_ (SSet.{u})) :=
    (isFibrant_iff_of_isTerminal (𝟙 (𝟙_ (SSet.{u}))) isTerminalTensorUnit).mpr
      inferInstance
  have : WeakEquivalence (toUnit X) := (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr h
  have : WeakEquivalence (singular.map (toUnit X)) :=
    DaggerActualQSingularFibrantWeakEquivalences.singular_weakEquivalence _
  let e := (isTerminalTensorUnit.isTerminalObj singular (𝟙_ (SSet.{u}))).uniqueUpToIso
    (isTerminalTensorUnit (C := SSet.{u}))
  have : IsIso e.hom := e.isIso_hom
  have he : singular.map (toUnit X) ≫ e.hom = toUnit (singular.obj X) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The exact original right-cone mapping object of every positive level is Kan. -/
theorem rightCone_Kan (P : BaseCode) (k : ℕ) :
    (rightConeSimplices (replacement.obj (rigidification.obj (spaceAt.{u} P k)))
      (alphaAt P (k + 1)) (omegaAt P (k + 1))).KanComplex :=
  DaggerActualRightConeKanMapping.rightCone_Kan _
    (replacement_locallyKan (rigidification.obj (spaceAt P k))) _ _

/-- Its literal terminal map is weak; this does not assume the desired ordinary counit weakness. -/
theorem rightCone_toUnit_GW (P : BaseCode) (k : ℕ) :
    DaggerSSetGluing.GW (toUnit
      (rightConeSimplices (replacement.obj (rigidification.obj (spaceAt.{u} P k)))
        (alphaAt P (k + 1)) (omegaAt P (k + 1)))) := by
  let C := rigidification.obj (spaceAt.{u} P k)
  let D := replacement.obj C
  let a := alphaAt.{u} P (k + 1)
  let b := omegaAt.{u} P (k + 1)
  have ha : NerveVertices.vertexEquiv D a =
      (unit.app C).obj (RV (spaceAt P k) (alphaAt P k)) :=
    DaggerActualFibrantGadgetVertices.unit_vertex _ _
  have hb : NerveVertices.vertexEquiv D b =
      (unit.app C).obj (RV (spaceAt P k) (omegaAt P k)) :=
    DaggerActualFibrantGadgetVertices.unit_vertex _ _
  let Y : SSet.{u} := (NerveVertices.vertexEquiv D a ⟶[SSet.{u}] NerveVertices.vertexEquiv D b)
  have : Y.KanComplex := replacement_locallyKan C _ _
  have ht : DaggerSSetGluing.GW (toUnit Y) := by
    dsimp only [Y]
    rw [ha, hb]
    exact replacement_endpoint_GW P k
  let e := DaggerActualRightConeSingularComparisonIso.comparisonIso D a b
  have : WeakEquivalence e.hom := inferInstance
  have : WeakEquivalence (toUnit (singular.obj Y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (singular_toUnit_GW Y ht)
  have he : e.hom ≫ toUnit (singular.obj Y) = toUnit (rightConeSimplices D a b) :=
    isTerminalTensorUnit.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerActualIteratedGadgetRightMapping
