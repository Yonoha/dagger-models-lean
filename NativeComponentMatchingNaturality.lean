import NativeComponentPartialMatchingComparison

/-! The canonical component comparison commutes with every actual bisimplicial map. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeComponentPartialMatchingComparison
universe u
namespace DaggerNativeComponentMatchingNaturality
noncomputable section

def componentMap {X Y : BiSSet.{u}} (f : X ⟶ Y) : componentRows X ⟶ componentRows Y :=
  Functor.whiskerRight f SSet.π₀Functor

theorem componentComparison_natural (K : SSet.{u}) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (s : (horizontalMapping K X).π₀) :
    componentComparison K Y (SSet.mapπ₀ (horizontalMap K f) s) =
      componentComparison K X s ≫ componentMap f := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective s
  apply NatTrans.ext
  funext d x
  rfl

end
end DaggerNativeComponentMatchingNaturality
