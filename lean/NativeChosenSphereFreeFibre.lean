import NativeSimpleSphereFreeClasses
import NativePositiveBoundaryConnected

/-! Use exactly the retained boundary vertex and its actual horn point for free sphere fibres. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open DaggerNativeSimpleSphereFreeClasses DaggerNativePositiveBoundaryConnected
open DaggerNativeSSetCoproductSummandFibration DaggerNativeUnitalMultiplicationAction
open SSet.KanComplex DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeChosenSphereFreeFibre
noncomputable section

def chosenHornPoint (n : ℕ) : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) 0 : SSet.{u}) :=
  SSet.const (hornVertex_nonempty n (0 : Fin (n + 2))).some

theorem chosenHornPoint_comp_boundary (n : ℕ) :
    chosenHornPoint.{u} n ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0) =
      SSet.const (boundaryVertex n) := by
  rw [chosenHornPoint, SSet.const_comp]
  rfl

def piChosenFreeSphereFibreEquiv (n : ℕ) (X : SSet.{u}) [IsFibrant X]
    (x : X _⦋0⦌) (hX : TrivialActionAt X x) :
    π n X x ≃ {c : ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj X).π₀ //
      SSet.mapπ₀ (pointEvaluation (SSet.const (boundaryVertex n)) X) c = SSet.π₀.mk x} := by
  simpa only [chosenHornPoint_comp_boundary] using
    (piFreeSphereFibreEquiv n 0 (chosenHornPoint n) X x hX)

end
end DaggerNativeChosenSphereFreeFibre
