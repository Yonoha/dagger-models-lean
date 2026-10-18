import NativeWalkingMarkedWordOperators

/-! Both exact round trips for insertion and deletion of original walking-product words. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordInsertions
open DaggerNativeWalkingMarkedWordOperators
universe u
namespace DaggerWalkingWordOperationRoundTrips
noncomputable section

theorem insert_delete_val {α : Type u} {d : ℕ} (f : Fin (d + 2) → α) (i : Fin (d + 2)) :
    Fin.insert (fun k ↦ f (i.succAbove k)) i (f i) = f := by
  funext j
  obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp
  · simp

theorem delete_insertWords {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1)) :
    deleteWords (insertWords w i v hm) i = w := by
  apply Subtype.ext
  funext j
  exact insertWords_old w i v hm j

def reinsertWords {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2)) : Words n (d + 1) :=
  insertWords (deleteWords w i) i (w.val i) (by
    change Monotone (fun k ↦ (Fin.insert (fun j ↦ w.val (i.succAbove j)) i (w.val i) k).1)
    rw [insert_delete_val]
    exact w.property)

theorem reinsertWords_eq {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2)) :
    reinsertWords w i = w := by
  apply Subtype.ext
  exact insert_delete_val w.val i

end
end DaggerWalkingWordOperationRoundTrips
