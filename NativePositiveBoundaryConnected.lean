import NativeConnectedHornsAndSimplex
import NativeSSetCoproductSummandFibration

/-! The existing boundary model of every positive sphere is nonempty and preconnected. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeSSetCoproductSummandFibration
universe u
namespace DaggerNativePositiveBoundaryConnected
noncomputable section

def boundaryVertex (n : ℕ) : (SSet.boundary (n + 1) : SSet.{u}) _⦋0⦌ := by
  let v := (hornVertex_nonempty n (0 : Fin (n + 2))).some
  exact ⟨v.val, (SSet.horn_le_boundary (0 : Fin (n + 2))) _ v.property⟩

instance positiveBoundary_components_subsingleton (n : ℕ) :
    Subsingleton ((SSet.boundary (n + 2) : SSet.{u}).π₀) := by
  let H : (Δ[n + 2] : SSet.{u}).Subcomplex := SSet.horn (n + 2) 0
  let i : (H : SSet.{u}) ⟶ (SSet.boundary (n + 2) : SSet.{u}) :=
    SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0)
  letI : Subsingleton ((H : SSet.{u}).π₀) :=
    DaggerNativeConnectedHornsAndSimplex.horn_components_subsingleton (n + 1) 0
  have hs : Function.Surjective (SSet.mapπ₀ i) := by
    intro c
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective c
    have hb : b.val ∈ H.obj (op ⦋0⦌) := by
      change b.val ∈ (SSet.horn (n + 2) 0).obj (op ⦋0⦌)
      rw [SSet.horn_obj_zero]
      trivial
    exact ⟨SSet.π₀.mk ⟨b.val, hb⟩, rfl⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  exact congrArg (SSet.mapπ₀ i) (Subsingleton.elim a b)

end
end DaggerNativePositiveBoundaryConnected
