import NativeHoIsoTriangles

/-! Actual simplicial maps preserve every face and degeneracy on raw simplex values. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
universe u
namespace DaggerSSetOperatorMapValues

theorem map_restrict {X Y : SSet.{u}} (f : X ⟶ Y) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : X.obj (op ⦋n⦌)) :
    f.app (op ⦋m⦌) (X.map α.op s) = Y.map α.op (f.app (op ⦋n⦌) s) :=
  congrFun (f.naturality α.op) s

theorem map_face {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 2))
    (s : X.obj (op ⦋n + 1⦌)) : f.app (op ⦋n⦌) (X.δ i s) =
      Y.δ i (f.app (op ⦋n + 1⦌) s) := map_restrict f (SimplexCategory.δ i) s

theorem map_degeneracy {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 1))
    (s : X.obj (op ⦋n⦌)) : f.app (op ⦋n + 1⦌) (X.σ i s) =
      Y.σ i (f.app (op ⦋n⦌) s) := map_restrict f (SimplexCategory.σ i) s

end DaggerSSetOperatorMapValues
