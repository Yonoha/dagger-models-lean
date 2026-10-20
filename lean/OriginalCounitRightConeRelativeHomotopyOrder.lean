import OriginalCounitRightConeContractibilityRetraction
import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# The ordinal prism for the actual right cone

This is the first source-only bridge toward a relative homotopy on the literal
pushout cone. No weak-equivalence or `Q n` contractibility assertion occurs.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerOriginalCounitRightConeRelativeHomotopy

noncomputable section

/-- On the large simplex (`k = 1`) this sends `(i,0)` to `i` and
`(i,1)` to `max i n`; on the initial face (`k = 0`) it stays in that face. -/
def prismOrder (n k : ℕ) :
    Fin (n + k + 1) × Fin 2 →o Fin (n + k + 1) where
  toFun p := ⟨max p.1.val (n * p.2.val), by
    have h₁ : p.1.val < n + k + 1 := p.1.isLt
    have h₂ : p.2.val ≤ 1 := by omega
    have h₃ : n * p.2.val ≤ n := by simpa using Nat.mul_le_mul_left n h₂
    omega⟩
  monotone' a b hab := by
    rcases hab with ⟨h₁, h₂⟩
    change max a.1.val (n * a.2.val) ≤ max b.1.val (n * b.2.val)
    exact max_le_max (Fin.le_iff_val_le_val.mp h₁)
      (Nat.mul_le_mul_left n (Fin.le_iff_val_le_val.mp h₂))

/-- Time zero is the identity on every vertex, including the terminal one. -/
theorem prismOrder_zero (n k : ℕ) (i : Fin (n + k + 1)) :
    prismOrder n k (i, 0) = i := by
  apply Fin.ext
  change max i.val (n * 0) = i.val
  simp

/-- At time one all vertices on the initial face meet its last vertex. -/
theorem prismOrder_one_initial (n : ℕ) (i : Fin (n + 2))
    (hi : i.val ≤ n) :
    prismOrder n 1 (i, 1) = (⟨n, by omega⟩ : Fin (n + 2)) := by
  apply Fin.ext
  change max i.val (n * 1) = n
  simpa using (max_eq_right hi)

/-- The final vertex remains fixed throughout the ordinal prism. -/
theorem prismOrder_last (n : ℕ) (t : Fin 2) :
    prismOrder n 1 (Fin.last (n + 1), t) = Fin.last (n + 1) := by
  apply Fin.ext
  have ht : t.val ≤ 1 := by omega
  have hnt : n * t.val ≤ n := by simpa using Nat.mul_le_mul_left n ht
  change max (n + 1) (n * t.val) = n + 1
  exact max_eq_left (by omega)

/-- The prism respects the actual last-face inclusion at both times. -/
theorem prismOrder_face (n : ℕ) (i : Fin (n + 1)) (t : Fin 2) :
    prismOrder n 1 (i.castSucc, t) =
      (prismOrder n 0 (i, t)).castSucc := by
  apply Fin.ext
  change max i.val (n * t.val) = max i.val (n * t.val)
  rfl

/-- The actual simplicial map induced by the product-poset prism.
Its source is the Cartesian product in `SSet`, not a formal cylinder symbol. -/
def simplexPrism (n k : ℕ) :
    (Δ[n + k] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[n + k] :=
  (SSet.prodStdSimplex.isoNerve (n + k) 1).hom ≫
    nerveMap
      ((show Monotone
          (fun p : ULift.{u} (Fin (n + k + 1) × Fin 2) ↦
            ULift.up (prismOrder n k p.down)) from by
        intro a b hab
        exact (prismOrder n k).monotone hab).functor) ≫
      (SSet.stdSimplex.isoNerve (n + k)).inv

/-- The prism has the prescribed value on every simplex, not only vertices. -/
theorem simplexPrism_app (n k d : ℕ)
    (z : (Δ[n + k] ⊗ Δ[1] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) :
    (simplexPrism.{u} n k).app (op ⦋d⦌) z i =
      prismOrder n k (z.1 i, z.2 i) := by
  rfl

end

end DaggerOriginalCounitRightConeRelativeHomotopy
