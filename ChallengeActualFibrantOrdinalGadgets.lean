import ActualFibrantGadgetData
import ActualConstantSimplicialCategory
import OriginalCounitRightCone

/-! The problem retains the original C, N, R, standard simplices and actual pushout cones. -/
set_option autoImplicit false
open CategoryTheory Opposite HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualFibrantGadgetData
open DaggerOriginalCounitRightCone
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace DaggerActualFibrantOrdinalGadgetsChallenge

def statement : Prop :=
  (∀ (A : Type u) [Category.{u} A] [Quiver.IsThin A],
    Nonempty (coherentNerve.obj (constant A) ≅ nerve A)) ∧
  (∀ (X Y : SSet.{u}) (p : X ⟶ Y),
    SSet.KanComplex X → (∀ q, Subsingleton (Y.obj q)) → Fibration p) ∧
  (∀ (n : ℕ) (a b : (rigidification.obj (gadget.obj (Δ[n] : SSet.{u}))).Obj),
    Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌)) →
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
        (toUnit (a ⟶[SSet.{u}] b))))) ∧
  ∀ (n : ℕ) (a b : (rigidification.obj (gadget.obj (cone.{u} n))).Obj),
    Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌)) →
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
        (toUnit (a ⟶[SSet.{u}] b))))

end DaggerActualFibrantOrdinalGadgetsChallenge
