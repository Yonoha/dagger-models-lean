import NativeFinitePiKan
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! The original finite pointwise Pi commutes with the native internal Hom. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed
open DaggerNativeFinitePiWeak DaggerNativeFinitePiKan
universe u
namespace DaggerNativeIhomFinitePi
noncomputable section

def piIhomMap {k : ℕ} (K : SSet.{u}) (X : Fin k → SSet.{u}) :
    piObject (fun i ↦ (ihom K).obj (X i)) ⟶ (ihom K).obj (piObject X) where
  app n a :=
    { app m α t i := (a i).app m α t
      naturality α β := by
        funext t i
        exact congrFun ((a i).naturality α β) t }
  naturality _ _ _ := rfl

def piIhomInv {k : ℕ} (K : SSet.{u}) (X : Fin k → SSet.{u}) :
    (ihom K).obj (piObject X) ⟶ piObject (fun i ↦ (ihom K).obj (X i)) where
  app n a i := ((ihom K).map (projection X i)).app n a
  naturality n m α := by
    funext a i
    exact congrFun (((ihom K).map (projection X i)).naturality α) a

def piIhomIso {k : ℕ} (K : SSet.{u}) (X : Fin k → SSet.{u}) :
    piObject (fun i ↦ (ihom K).obj (X i)) ≅ (ihom K).obj (piObject X) where
  hom := piIhomMap K X
  inv := piIhomInv K X
  hom_inv_id := by
    apply NatTrans.ext
    funext n a i
    apply Functor.HomObj.ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n a
    apply Functor.HomObj.ext
    rfl

theorem piIhomIso_projection {k : ℕ} (K : SSet.{u}) (X : Fin k → SSet.{u})
    (i : Fin k) : (piIhomIso K X).hom ≫ (ihom K).map (projection X i) =
      projection (fun i ↦ (ihom K).obj (X i)) i := by
  apply NatTrans.ext
  funext n a
  apply Functor.HomObj.ext
  rfl

end
end DaggerNativeIhomFinitePi
