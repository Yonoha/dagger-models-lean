import NativeFinitePiHomotopyAction
import NativeSimplexPullbackFibrationDetection

/-! Literal binary products inherit trivial actions through their exact finite Pi object. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory
open DaggerNativeFinitePiWeak DaggerNativeFinitePiKan
open DaggerNativeFinitePiHomotopyAction DaggerNativeUnitalMultiplicationAction
open DaggerNativeWeakMapTrivialAction DaggerNativeSimplexPullbackFibrationDetection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBinaryProductLoopAction
noncomputable section

def pairFamily (X Y : SSet.{u}) : Fin 2 → SSet.{u} := Fin.cases X (fun _ ↦ Y)

def pairPiIso (X Y : SSet.{u}) : X ⊗ Y ≅ piObject (pairFamily X Y) where
  hom :=
    { app _ a := Fin.cases a.1 (fun _ ↦ a.2)
      naturality _ _ _ := by
        funext a i
        refine Fin.cases ?_ (fun _ ↦ ?_) i <;> rfl }
  inv :=
    { app _ a := (a 0, a 1)
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext d a i
    fin_cases i <;> rfl

instance tensor_fibrant (X Y : SSet.{u}) [IsFibrant X] [IsFibrant Y] :
    IsFibrant (X ⊗ Y) := by
  have : Fibration (fst X Y) := product_projection_fibration X Y
  exact isFibrant_of_fibration (fst X Y)

theorem tensor_actions_trivial (X Y : SSet.{u}) [IsFibrant X] [IsFibrant Y]
    (hX : ∀ x, TrivialActionAt X x) (hY : ∀ y, TrivialActionAt Y y) :
    ∀ a : (X ⊗ Y).obj (op ⦋0⦌), TrivialActionAt (X ⊗ Y) a := by
  letI : IsFibrant (X ⊗ Y) := tensor_fibrant X Y
  letI : ∀ i, IsFibrant (pairFamily X Y i) := by
    intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact (inferInstance : IsFibrant X)
    · exact (inferInstance : IsFibrant Y)
  letI : IsFibrant (piObject (pairFamily X Y)) :=
    finitePi_kan (pairFamily X Y) (fun _ ↦ inferInstance)
  apply all_trivial_actions_of_weak (pairPiIso X Y).inv
  intro a
  apply product_action_trivial
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact hX _
  · exact hY _

end
end DaggerNativeBinaryProductLoopAction
