import NativeWalkingKanTensor
import NativeFinitePiWeak

/-! The full original pointwise finite product is Kan when every original factor is Kan. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFinitePiWeak DaggerOriginalNativeKanFromHornFillers
universe u
namespace DaggerNativeFinitePiKan
noncomputable section

def projection {n : ℕ} (X : Fin n → SSet.{u}) (j : Fin n) : piObject X ⟶ X j where
  app _ a := a j
  naturality _ _ _ := rfl

theorem finitePi_kan {n : ℕ} (X : Fin n → SSet.{u})
    (hX : ∀ j, (X j).KanComplex) : (piObject X).KanComplex := by
  apply kanComplex_of_hornFillers
  intro m i a
  have he (j : Fin n) : ∃ l : (Δ[m + 1] : SSet.{u}) ⟶ X j,
      a ≫ projection X j = (SSet.horn (m + 1) i).ι ≫ l := by
    have := hX j
    exact SSet.KanComplex.hornFilling (a ≫ projection X j)
  let l (j : Fin n) := (he j).choose
  let t : (Δ[m + 1] : SSet.{u}) ⟶ piObject X :=
    { app d x j := (l j).app d x
      naturality d e α := by
        funext x j
        exact congrFun ((l j).naturality α) x }
  refine ⟨t, ?_⟩
  apply NatTrans.ext
  funext d x j
  exact congrFun (NatTrans.congr_app (he j).choose_spec d) x

end
end DaggerNativeFinitePiKan
