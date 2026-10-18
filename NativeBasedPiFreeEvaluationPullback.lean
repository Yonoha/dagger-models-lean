import NativeTotalBasedPiFunctor
import NativeFreeSphereFibreNaturality
import NativeMappingEvaluationRealizationUnit

/-! The original total based-pi rows map to the actual free-evaluation pullback over vertices. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial Opposite
open DaggerNativeTotalBasedPiFunctor DaggerNativeSimpleSphereFreeClasses
open DaggerNativeFreeSphereFibreNaturality DaggerNativeMappingEvaluationRealizationUnit
open DaggerNativeUnitalMultiplicationAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBasedPiFreeEvaluationPullback
noncomputable section

def vertexRows (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  F ⋙ SSet.evaluation.obj (op ⦋0⦌)

def basedRows (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) : SSet.{u} :=
  F ⋙ totalPiFunctor n

def basedProjection (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    basedRows F n ⟶ vertexRows F := Functor.whiskerLeft F (vertexProjection n)

def vertexComponents (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    vertexRows F ⟶ (F ⋙ SSet.π₀Functor : SSet.{u}) :=
  Functor.whiskerLeft F SSet.toπ₀NatTrans

variable (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (i : Fin (n + 2))
  (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
  [∀ k, IsFibrant (F.obj k)] (hS : ∀ k x, TrivialActionAt (F.obj k) x)

def toFreeComponents : basedRows F n ⟶
    (F ⋙ ihom (SSet.boundary (n + 1) : SSet.{u}) ⋙ SSet.π₀Functor : SSet.{u}) where
  app k s := (piFreeSphereFibreEquiv n i a (F.obj k) s.1 (hS k s.1) s.2).val
  naturality k l α := by
    funext ⟨x, s⟩
    exact (freeSphereFibre_natural_val n i a (F.map α) x (hS k x) (hS l _) s).symm

theorem toFreeComponents_evaluation :
    toFreeComponents F n i a hS ≫
        rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) =
      basedProjection F n ≫ vertexComponents F := by
  apply NatTrans.ext
  funext k ⟨x, s⟩
  exact (piFreeSphereFibreEquiv n i a (F.obj k) x (hS k x) s).property

def comparisonMap : basedRows F n ⟶
    pullback (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))
      (vertexComponents F) :=
  pullback.lift (toFreeComponents F n i a hS) (basedProjection F n)
    (toFreeComponents_evaluation F n i a hS)

theorem comparisonMap_fst :
    comparisonMap F n i a hS ≫ pullback.fst
        (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))
        (vertexComponents F) = toFreeComponents F n i a hS := by
  simp only [comparisonMap, pullback.lift_fst]

theorem comparisonMap_snd :
    comparisonMap F n i a hS ≫ pullback.snd
        (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))
        (vertexComponents F) = basedProjection F n := by
  simp only [comparisonMap, pullback.lift_snd]

end
end DaggerNativeBasedPiFreeEvaluationPullback
