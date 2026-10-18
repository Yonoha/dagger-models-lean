import FixedCategoryHomLimits
import OrdinaryAnodyneTensor
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-! Transfinite closure on every original Hom of the fixed-object dagger category.
Only filtered colimits are used: no Hom evaluation is assumed to preserve pushouts. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerFixedCategoryHomLimits

universe u

namespace DaggerFixedCategoryHomTransfinite

noncomputable section

variable (O : Type u)

/-- The actual anodyne condition at every ordered pair of original objects. -/
def Q : MorphismProperty (FixedDaggerSimplicialCat O) :=
  fun _ _ f ↦ ∀ x y : O, SSet.anodyneExtensions ((homEval O x y).map f)

theorem Q_iff_original {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    Q O f ↔ ∀ x y : O, SSet.anodyneExtensions (f.val.map x y) :=
  forall₂_congr (fun x y ↦ original_hom_property_iff SSet.anodyneExtensions f x y)

instance homEvalPreservesWellOrderContinuous (x y : O) (J : Type u)
    [LinearOrder J] [OrderBot J] :
    PreservesWellOrderContinuousOfShape J (homEval O x y) where
  preservesColimitsOfShape j hj := by
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    infer_instance

/-- Mathlib transports the same chain, source isomorphism, inclusion and colimit. -/
def mappedTransfiniteComposition (x y : O) (J : Type u)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {C D : FixedDaggerSimplicialCat O} {f : C ⟶ D}
    (h : (Q O).TransfiniteCompositionOfShape J f) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape J ((homEval O x y).map f) :=
  (h.ofLE (show Q O ≤ SSet.anodyneExtensions.inverseImage (homEval O x y) from
    fun _ _ _ hf ↦ hf x y)).map

instance Q_transfiniteOfShape (J : Type u)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (Q O).IsStableUnderTransfiniteCompositionOfShape J where
  le _ _ _ hf x y := SSet.anodyneExtensions.transfiniteCompositionsOfShape_le J _
    (mappedTransfiniteComposition O x y J hf.some).mem

instance Q_transfinite : MorphismProperty.IsStableUnderTransfiniteComposition.{u} (Q O) where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ := inferInstance

theorem Q_le_W : Q O ≤ DaggerFixedCategoryGenerators.W O := by
  intro C D f hf
  apply (DaggerFixedCategoryGenerators.W_iff_homwise f).2
  intro x y
  exact (mem_trivialCofibrations_iff _).1
    ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      ((Q_iff_original O f).1 hf x y)) |>.2

theorem transfiniteCompositions_le_W :
    MorphismProperty.transfiniteCompositions.{u} (Q O) ≤ DaggerFixedCategoryGenerators.W O :=
  (MorphismProperty.transfiniteCompositions_le (Q O)).trans (Q_le_W O)

end

end DaggerFixedCategoryHomTransfinite
