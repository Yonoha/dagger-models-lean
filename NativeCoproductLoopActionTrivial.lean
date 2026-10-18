import NativeCoproductHomotopy
import NativeZeroHomotopyAction

/-! All actual coproduct vertices inherit trivial native based loop actions. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeCoproductHomotopy DaggerNativeUnitalMultiplicationAction
open DaggerNativeZeroHomotopyAction DaggerNativeWeakMapTrivialAction
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductLoopActionTrivial
noncomputable section

theorem summand_action_trivial {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) (x : (X i) _⦋0⦌)
    (hX : TrivialActionAt (X i) x) :
    TrivialActionAt (∐ X) ((Sigma.ι X i).app (op ⦋0⦌) x) := by
  intro n p s
  cases n with
  | zero => exact zero_action_trivial _ p s
  | succ n =>
    have hb := (bijective_mapπ_one_iff (Sigma.ι X i) rfl).mp
      (summand_mapπ_positive_bijective X i x 0)
    obtain ⟨p, rfl⟩ := hb.2 p
    obtain ⟨s, rfl⟩ := (summand_mapπ_positive_bijective X i x n).2 s
    have hn := congrFun ((actionMap (Sigma.ι X i) (n + 1)).naturality p) s
    change mapπ (Sigma.ι X i) (n + 1) x _ rfl (action.map p s) =
      action.map ((mapFundamentalGroupoid (Sigma.ι X i)).map p)
        (mapπ (Sigma.ι X i) (n + 1) x _ rfl s) at hn
    rw [hX (n + 1) p s] at hn
    exact hn.symm

theorem coproduct_actions_trivial {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (hX : ∀ i x, TrivialActionAt (X i) x) :
    ∀ a : (∐ X) _⦋0⦌, TrivialActionAt (∐ X) a := by
  intro a
  obtain ⟨⟨i, x⟩, rfl⟩ := (coproductDegreeEquiv X (op ⦋0⦌)).surjective a
  exact summand_action_trivial X i x (hX i x)

theorem realized_coproduct_actions_trivial {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (hX : ∀ i x, TrivialActionAt (X i) x) :
    ∀ a : (TopCat.toSSet.obj (SSet.toTop.obj (∐ X))) _⦋0⦌,
      TrivialActionAt (TopCat.toSSet.obj (SSet.toTop.obj (∐ X))) a :=
  all_trivial_actions_of_weak (sSetTopAdj.unit.app (∐ X))
    (coproduct_actions_trivial X hX)

end
end DaggerNativeCoproductLoopActionTrivial
