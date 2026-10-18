import NativeRowwiseWeakEvaluation
import NativeBasedPiProjectionFibration
import NativeWeakMapTrivialAction

/-! Transfer original based-pi horn lifting forwards using actual free evaluation and actions. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra Simplicial
open DaggerNativeRowwiseWeakEvaluation DaggerNativeWeakMapTrivialAction
open DaggerNativeUnitalMultiplicationAction DaggerNativeBasedPiFreeEvaluationPullback
open DaggerNativeMappingEvaluationRealizationUnit DaggerNativeBasedPiProjectionFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeakRowBasedPiTransfer
noncomputable section

theorem target_row_actions_trivial {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)] (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (hS : ∀ k x, TrivialActionAt (F.obj k) x) :
    ∀ k y, TrivialActionAt (G.obj k) y := by
  intro k
  have := hf k
  exact all_trivial_actions_of_weak (f.app k) (hS k)

theorem target_basedProjection_fibration {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)] (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (hS : ∀ k x, TrivialActionAt (F.obj k) x)
    (hE : Fibration (C := SSet.{u})
      (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))) :
    Fibration (basedProjection G n) := by
  have : Fibration (C := SSet.{u})
      (rowEvaluation G (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))) :=
    (evaluation_fibration_iff f hf _).mp hE
  exact basedProjection_fibration G n i a (target_row_actions_trivial f hf hS)

end
end DaggerNativeWeakRowBasedPiTransfer
