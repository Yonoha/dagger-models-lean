import OriginalSimplicialPiZeroLaxMonoidal
import NativeFinitePiWeak

/-! The original component quotient preserves finite pointwise products. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial
open DaggerOriginalSimplicialPiZeroLaxMonoidal DaggerNativeFinitePiWeak
universe u
namespace DaggerNativePiZeroProductEquivalence
noncomputable section

def productComponentsEquiv (X Y : SSet.{u}) : (X ⊗ Y).π₀ ≃ X.π₀ × Y.π₀ where
  toFun q := (SSet.mapπ₀ (fst X Y) q, SSet.mapπ₀ (snd X Y) q)
  invFun q := pairComponents X Y q.1 q.2
  left_inv q := by
    obtain ⟨⟨a, b⟩, rfl⟩ := SSet.π₀.mk_surjective q
    rfl
  right_inv q := by
    obtain ⟨a, b⟩ := q
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    rfl

theorem productComponentsEquiv_mk (X Y : SSet.{u})
    (a : X _⦋0⦌) (b : Y _⦋0⦌) :
    productComponentsEquiv X Y (SSet.π₀.mk (a, b)) = (SSet.π₀.mk a, SSet.π₀.mk b) := rfl

def finitePiComponentsEquiv (n : ℕ) : ∀ X : Fin n → SSet.{u},
    (piObject X).π₀ ≃ (∀ i, (X i).π₀) := by
  induction n with
  | zero =>
    intro X
    exact
      { toFun _ := fun i ↦ Fin.elim0 i
        invFun _ := SSet.π₀.mk (fun i ↦ Fin.elim0 i)
        left_inv q := by
          obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective q
          apply congrArg (SSet.π₀.mk (X := piObject X))
          funext i
          exact Fin.elim0 i
        right_inv a := by funext i; exact Fin.elim0 i }
  | succ n ih =>
    intro X
    exact ((SSet.π₀Functor.mapIso (piSuccIso X)).toEquiv.trans
      (productComponentsEquiv (X 0) (piObject (fun i ↦ X i.succ)))).trans
      ((Equiv.prodCongr (Equiv.refl _) (ih (fun i ↦ X i.succ))).trans
        (headTailEquiv (fun i ↦ (X i).π₀)).symm)

theorem finitePiComponentsEquiv_mk (n : ℕ) (X : Fin n → SSet.{u})
    (a : (piObject X) _⦋0⦌) :
    finitePiComponentsEquiv n X (SSet.π₀.mk a) = fun i ↦ SSet.π₀.mk (a i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · exact congrFun (ih (fun j ↦ X j.succ) (fun j ↦ a j.succ)) j

theorem finitePiComponentsEquiv_natural {n : ℕ} {X Y : Fin n → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (q : (piObject X).π₀) :
    finitePiComponentsEquiv n Y (SSet.mapπ₀ (piMap f) q) =
      fun i ↦ SSet.mapπ₀ (f i) (finitePiComponentsEquiv n X q i) := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective q
  rw [SSet.mapπ₀_mk, finitePiComponentsEquiv_mk, finitePiComponentsEquiv_mk]
  rfl

end
end DaggerNativePiZeroProductEquivalence
