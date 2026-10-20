import NativePullbackPositivePiComparison

/-! Retain explicitly named projection vertices in the canonical positive-pi pullback formula. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex DaggerNativePullbackPiExact DaggerNativePullbackPositivePiComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePullbackPositivePiRebase
noncomputable section

theorem coordinateEquation {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (e : E _⦋0⦌) (c : C _⦋0⦌)
    (he : (pullback.fst p q).app _ w = e) (hc : (pullback.snd p q).app _ w = c) :
    p.app _ e = q.app _ c :=
  (congrArg (p.app _) he.symm).trans
    ((basepointEquation p q w).trans (congrArg (q.app _) hc))

def rebasedComparison {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (e : E _⦋0⦌) (c : C _⦋0⦌)
    (he : (pullback.fst p q).app _ w = e) (hc : (pullback.snd p q).app _ w = c)
    (n : ℕ) : π (n + 1) (pullback p q) w →
    {z : π (n + 1) E e × π (n + 1) C c //
      mapπ p (n + 1) e (q.app _ c) (coordinateEquation p q w e c he hc) z.1 =
        mapπ q (n + 1) c (q.app _ c) rfl z.2} :=
  fun s ↦ ⟨(mapπ (pullback.fst p q) (n + 1) w e he s,
      mapπ (pullback.snd p q) (n + 1) w c hc s), by
    simp only [mapπ_mapπ, pullback.condition]⟩

theorem rebasedComparison_surjective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C]
    (w : (pullback p q) _⦋0⦌) (e : E _⦋0⦌) (c : C _⦋0⦌)
    (he : (pullback.fst p q).app _ w = e) (hc : (pullback.snd p q).app _ w = c)
    (n : ℕ) : Function.Surjective (rebasedComparison p q w e c he hc n) := by
  subst e
  subst c
  exact positiveComparison_surjective p q w n

theorem rebasedComparison_bijective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C]
    (w : (pullback p q) _⦋0⦌) (e : E _⦋0⦌) (c : C _⦋0⦌)
    (he : (pullback.fst p q).app _ w = e) (hc : (pullback.snd p q).app _ w = c)
    (n : ℕ) (hp : Function.Surjective
      (mapπ p (n + 2) e (q.app _ c) (coordinateEquation p q w e c he hc))) :
    Function.Bijective (rebasedComparison p q w e c he hc n) := by
  subst e
  subst c
  exact positiveComparison_bijective p q w n hp

end
end DaggerNativePullbackPositivePiRebase
