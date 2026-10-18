import NativeWeakMapTrivialAction
import NativeFinitePiKan

/-! The actual finite pointwise product retains and detects native based homotopy classes. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeFinitePiWeak DaggerNativeFinitePiKan DaggerNativeUnitalMultiplicationAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFinitePiHomotopyAction
noncomputable section

def productRelStruct₀ {k n : ℕ} (X : Fin k → SSet.{u}) (a : (piObject X) _⦋0⦌)
    (p q : (piObject X).PtSimplex n a)
    (h : ∀ i, (p.pushforward (projection X i) (a i) rfl).RelStruct₀
      (q.pushforward (projection X i) (a i) rfl)) : p.RelStruct₀ q where
  map :=
    { app d t i := (h i).map.app d t
      naturality d e α := by
        funext t i
        exact congrFun ((h i).map.naturality α) t }
  δ_castSucc_map := by
    apply NatTrans.ext
    funext d t i
    exact congrFun (NatTrans.congr_app (h i).δ_castSucc_map d) t
  δ_succ_map := by
    apply NatTrans.ext
    funext d t i
    exact congrFun (NatTrans.congr_app (h i).δ_succ_map d) t
  δ_map_of_lt j hj := by
    apply NatTrans.ext
    funext d t i
    exact congrFun (NatTrans.congr_app ((h i).δ_map_of_lt j hj) d) t
  δ_map_of_gt j hj := by
    apply NatTrans.ext
    funext d t i
    exact congrFun (NatTrans.congr_app ((h i).δ_map_of_gt j hj) d) t

theorem mapπ_projections_jointly_injective {k n : ℕ} (X : Fin k → SSet.{u})
    [∀ i, IsFibrant (X i)] [IsFibrant (piObject X)] (a : (piObject X) _⦋0⦌)
    (p q : π n (piObject X) a)
    (h : ∀ i, mapπ (projection X i) n a (a i) rfl p =
      mapπ (projection X i) n a (a i) rfl q) : p = q := by
  obtain ⟨p, rfl⟩ := π.mk_surjective p
  obtain ⟨q, rfl⟩ := π.mk_surjective q
  apply π.mk_eq_mk_iff.mpr
  have hh (i : Fin k) : Nonempty
      ((p.pushforward (projection X i) (a i) rfl).RelStruct₀
        (q.pushforward (projection X i) (a i) rfl)) := π.mk_eq_mk_iff.mp (h i)
  exact ⟨productRelStruct₀ X a p q (fun i ↦ (hh i).some)⟩

theorem product_action_trivial {k : ℕ} (X : Fin k → SSet.{u})
    [∀ i, IsFibrant (X i)] [IsFibrant (piObject X)] (a : (piObject X) _⦋0⦌)
    (h : ∀ i, TrivialActionAt (X i) (a i)) : TrivialActionAt (piObject X) a := by
  intro n p s
  apply mapπ_projections_jointly_injective X a
  intro i
  have hn := congrFun ((actionMap (projection X i) n).naturality p) s
  change mapπ (projection X i) n a (a i) rfl (action.map p s) =
    action.map ((mapFundamentalGroupoid (projection X i)).map p)
      (mapπ (projection X i) n a (a i) rfl s) at hn
  exact hn.trans (h i n _ _)

end
end DaggerNativeFinitePiHomotopyAction
