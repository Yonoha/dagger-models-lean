import NativePartialFaceUnionGeometry

/-! The original horn is exactly the finite union of all faces except its missing face. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeHornAsPartialFaceUnion
noncomputable section

theorem faceUnion_erase_eq_horn (m : ℕ) (k : Fin (m + 1)) :
    faceUnion.{u} (Finset.univ.erase k) = SSet.horn m k := by
  apply le_antisymm
  · exact faceUnion_le_horn _ k (Finset.notMem_erase k _)
  · rw [SSet.horn_eq_iSup]
    apply iSup_le
    intro j
    exact Finset.le_sup (f := fun l ↦ SSet.stdSimplex.face {l}ᶜ)
      (Finset.mem_erase.mpr ⟨j.property, Finset.mem_univ _⟩)

theorem horn_face_indices_nonempty (m : ℕ) (k : Fin (m + 2)) :
    (Finset.univ.erase k).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne k
  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩

end
end DaggerNativeHornAsPartialFaceUnion
