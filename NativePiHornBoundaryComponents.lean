import NativeHornBoundaryAttachment
import NativePushoutConstantMappingFibres
import NativePointedHomotopyComponents
import OriginalSimplicialPiZeroWeakEquivalence

/-! The original native pi_n is identified with maps from the sphere boundary fixed on its horn. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalClosed HomotopicalAlgebra
open SSet.KanComplex DaggerNativeHornBoundaryAttachment
open DaggerNativePushoutConstantMappingFibres DaggerNativePointedHomotopyComponents
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiHornBoundaryComponents
noncomputable section

abbrev hornMappingSpace (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u}) (x : X _⦋0⦌) :
    ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj X).Subcomplex :=
  constantMappingFibre (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x

def sphereHornMappingIso (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u}) (x : X _⦋0⦌) :
    (hornMappingSpace n i X x : SSet.{u}) ≅ pointedMappingSpace n X x :=
  restrictionFibreIso (boundary_horn_missing_face_isPushout n i).flip X x

def piToHornComponent (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u}) [IsFibrant X]
    (x : X _⦋0⦌) : π n X x → (hornMappingSpace n i X x : SSet.{u}).π₀ :=
  fun p ↦ SSet.mapπ₀ (sphereHornMappingIso n i X x).inv (piComponentsEquiv n X x p)

theorem piToHornComponent_bijective (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u})
    [IsFibrant X] (x : X _⦋0⦌) : Function.Bijective (piToHornComponent n i X x) :=
  (bijective_mapPiZero (sphereHornMappingIso n i X x).inv).comp
    (piComponentsEquiv n X x).bijective

def piHornComponentsEquiv (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u}) [IsFibrant X]
    (x : X _⦋0⦌) : π n X x ≃ (hornMappingSpace n i X x : SSet.{u}).π₀ :=
  Equiv.ofBijective (piToHornComponent n i X x) (piToHornComponent_bijective n i X x)

theorem piHornComponentsEquiv_restrict (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u})
    [IsFibrant X] (x : X _⦋0⦌) (p : π n X x) :
    SSet.mapπ₀ (sphereHornMappingIso n i X x).hom (piHornComponentsEquiv n i X x p) =
      piComponentsEquiv n X x p := by
  change SSet.mapπ₀ (sphereHornMappingIso n i X x).hom
    (SSet.mapπ₀ (sphereHornMappingIso n i X x).inv (piComponentsEquiv n X x p)) = _
  rw [← SSet.mapπ₀_comp_apply, Iso.inv_hom_id]
  exact SSet.mapπ₀_id_apply _

end
end DaggerNativePiHornBoundaryComponents
