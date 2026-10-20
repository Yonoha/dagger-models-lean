import NativePullbackFibreIso
import TopCatModelCategory.ModelCategorySSet
import TopCatModelCategory.SSet.HomotopySequence

/-! Original pullback projections and fibre maps form the native homotopy exact-sequence square. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex DaggerNativePullbackFibreIso
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePullbackPiExact
noncomputable section

theorem basepointEquation {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) :
    p.app _ ((pullback.fst p q).app _ w) = q.app _ ((pullback.snd p q).app _ w) :=
  congrFun (NatTrans.congr_app (pullback.condition (f := p) (g := q)) _) w

def fibreComparison {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) (c : C _⦋0⦌) :
    (Subcomplex.fiber (pullback.snd p q) c : SSet.{u}) ⟶
      (Subcomplex.fiber p (q.app _ c) : SSet.{u}) :=
  Subcomplex.mapFiber (pullback.snd p q) p (pullback.fst p q) q
    (pullback.condition (f := p) (g := q)) c (q.app _ c) rfl

theorem fibreComparison_isIso {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (c : C _⦋0⦌) : IsIso (fibreComparison p q c) :=
  mapFiber_isIso_of_isPullback (pullback.snd p q) p (pullback.fst p q) q
    (IsPullback.of_hasPullback p q) c (q.app _ c) rfl

def fibrePiMap {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) :
    π t (Subcomplex.fiber (pullback.snd p q) ((pullback.snd p q).app _ w))
      (Subcomplex.fiber.basePoint (pullback.snd p q) (x := w) rfl) →
    π t (Subcomplex.fiber p (q.app _ ((pullback.snd p q).app _ w)))
      (Subcomplex.fiber.basePoint p (basepointEquation p q w)) :=
  mapπ (fibreComparison p q ((pullback.snd p q).app _ w)) t _ _ rfl

theorem fibrePiMap_bijective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) : Function.Bijective (fibrePiMap p q w t) := by
  have := fibreComparison_isIso p q ((pullback.snd p q).app _ w)
  exact (mapπEquivOfIso (asIso (fibreComparison p q ((pullback.snd p q).app _ w)))
    t _ _ rfl).bijective

def leftPi {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) :
    π t (pullback p q) w → π t E ((pullback.fst p q).app _ w) :=
  mapπ (pullback.fst p q) t _ _ rfl

def rightPi {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) :
    π t (pullback p q) w → π t C ((pullback.snd p q).app _ w) :=
  mapπ (pullback.snd p q) t _ _ rfl

def basePi {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) :
    π t E ((pullback.fst p q).app _ w) →
      π t B (q.app _ ((pullback.snd p q).app _ w)) :=
  mapπ p t _ _ (basepointEquation p q w)

def otherPi {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) :
    π t C ((pullback.snd p q).app _ w) →
      π t B (q.app _ ((pullback.snd p q).app _ w)) := mapπ q t _ _ rfl

theorem projection_compatibility {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ) (s : π t (pullback p q) w) :
    basePi p q w t (leftPi p q w t s) = otherPi p q w t (rightPi p q w t s) := by
  simp only [basePi, leftPi, otherPi, rightPi, mapπ_mapπ, pullback.condition]

def positiveComparison {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (n : ℕ) : π (n + 1) (pullback p q) w →
    {z : π (n + 1) E ((pullback.fst p q).app _ w) ×
      π (n + 1) C ((pullback.snd p q).app _ w) //
        basePi p q w (n + 1) z.1 = otherPi p q w (n + 1) z.2} :=
  fun s ↦ ⟨(leftPi p q w (n + 1) s, rightPi p q w (n + 1) s),
    projection_compatibility p q w (n + 1) s⟩

theorem leftPi_fibrePi {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (w : (pullback p q) _⦋0⦌) (t : ℕ)
    (s : π t (Subcomplex.fiber (pullback.snd p q) ((pullback.snd p q).app _ w))
      (Subcomplex.fiber.basePoint (pullback.snd p q) (x := w) rfl)) :
    leftPi p q w t (HomotopySequence.map₁ (pullback.snd p q) rfl t s) =
      HomotopySequence.map₁ p (basepointEquation p q w) t (fibrePiMap p q w t s) := by
  simp only [leftPi, fibrePiMap, fibreComparison, HomotopySequence.map₁,
    mapπ_mapπ, Subcomplex.mapFiber_ι]

theorem rightPi_fibre {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) [IsFibrant C]
    (w : (pullback p q) _⦋0⦌) (t : ℕ)
    (s : π t (Subcomplex.fiber (pullback.snd p q) ((pullback.snd p q).app _ w))
      (Subcomplex.fiber.basePoint (pullback.snd p q) (x := w) rfl)) :
    rightPi p q w t (HomotopySequence.map₁ (pullback.snd p q) rfl t s) = 1 :=
  HomotopySequence.map₂_map₁_apply (p := pullback.snd p q) (he := rfl) s

theorem fibre_delta_naturality {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant E] [IsFibrant B] [IsFibrant C] [IsFibrant (pullback p q)]
    (w : (pullback p q) _⦋0⦌)
    (n : ℕ) (s : π (n + 1) C ((pullback.snd p q).app _ w)) :
    fibrePiMap p q w n (HomotopySequence.δ' (pullback.snd p q) (e := w) rfl n 0 s) =
      HomotopySequence.δ' p (basepointEquation p q w) n 0 (otherPi p q w (n + 1) s) := by
  have : Fibration (pullback.snd p q) := inferInstance
  have hh := HomotopySequence.δ'_naturality (p := pullback.snd p q) (he := rfl)
    (p' := p) (he' := basepointEquation p q w) n 0 s
    (pullback.fst p q) q (pullback.condition (f := p) (g := q)) rfl
  simpa only [fibrePiMap, fibreComparison, otherPi] using hh.symm

end
end DaggerNativePullbackPiExact
