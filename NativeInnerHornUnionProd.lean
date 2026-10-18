import NativeInnerPairing
import TopCatModelCategory.SSet.PairingUnionProd

/-!
# The actual inner-horn / boundary pushout-product belongs to the exact inner-left class

Reuse the pinned original union-product pairing and its proved innerness.
The full original subcomplex and its inclusion are retained in every degree.
-/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open DaggerNativeInnerHornFactorization DaggerNativeInnerPairing
universe u
namespace DaggerNativeInnerHornUnionProd
noncomputable section

/-- The original full union inclusion is inner-left for every inner horn and boundary. -/
theorem horn_union_boundary_innerAnodyne (m : ℕ) (i : Fin (m + 3))
    (h0 : 0 < i) (hn : i < Fin.last (m + 2)) (n : ℕ) :
    innerAnodyne ((SSet.horn.{u} (m + 2) i).unionProd (SSet.boundary n)).ι := by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hn)
  have hi : i ≠ 0 := by
    intro h
    subst h
    simp at h0
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  exact pairing_innerAnodyne (SSet.prodStdSimplex.pairingCore k.succ n).pairing
    (SSet.prodStdSimplex.isInner_pairingCore n k).pairing

end
end DaggerNativeInnerHornUnionProd
