import NativeOriginalCoreWalkingInverse
import NativeRelativeWalkingCoreFibration

/-! Exact core/pullback comparison whenever the actual pullback of the original cores is Kan. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeOriginalCoreWalkingInverse
open DaggerNativeKanSourceOriginalCoreFactor
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCorePullback
noncomputable section

def toPullback {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B) :
    (ordinaryCoreCandidate (pullback p f) : SSet.{u}) ⟶
      pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) :=
  pullback.lift (ordinaryCoreCandidateMap (pullback.fst p f))
    (ordinaryCoreCandidateMap (pullback.snd p f)) (by
      rw [← core_map_comp, ← core_map_comp, pullback.condition])

def toAmbient {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B) :
    pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) ⟶ pullback p f :=
  pullback.lift
    (pullback.fst (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) ≫
      (ordinaryCoreCandidate E).ι)
    (pullback.snd (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) ≫
      (ordinaryCoreCandidate X).ι) (by
      rw [Category.assoc, Category.assoc, ← ordinaryCoreCandidateMap_comp_ι,
        ← ordinaryCoreCandidateMap_comp_ι, pullback.condition_assoc])

theorem toPullback_toAmbient {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B) :
    toPullback p f ≫ toAmbient p f = (ordinaryCoreCandidate (pullback p f)).ι := by
  apply pullback.hom_ext
  · simp only [toAmbient, Category.assoc, pullback.lift_fst, toPullback,
      pullback.lift_fst_assoc, ordinaryCoreCandidateMap_comp_ι]
  · simp only [toAmbient, Category.assoc, pullback.lift_snd, toPullback,
      pullback.lift_snd_assoc, ordinaryCoreCandidateMap_comp_ι]

def comparisonIso {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [(pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f)).KanComplex] :
    (ordinaryCoreCandidate (pullback p f) : SSet.{u}) ≅
      pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) where
  hom := toPullback p f
  inv := factor (toAmbient p f)
  hom_inv_id := by
    apply (cancel_mono (ordinaryCoreCandidate (pullback p f)).ι).mp
    rw [Category.assoc, factor_comp, toPullback_toAmbient, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (ordinaryCoreCandidate E).ι).mp
      simp only [Category.assoc, toPullback, pullback.lift_fst]
      rw [ordinaryCoreCandidateMap_comp_ι, ← Category.assoc, factor_comp]
      simp [toAmbient]
    · apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
      simp only [Category.assoc, toPullback, pullback.lift_snd]
      rw [ordinaryCoreCandidateMap_comp_ι, ← Category.assoc, factor_comp]
      simp [toAmbient]

theorem pullback_cores_kan {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [X.Quasicategory] [Fibration (ordinaryCoreCandidateMap p)] :
    (pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f)).KanComplex := by
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex := native_quasi_core_kan X
  exact isFibrant_of_fibration
    (pullback.snd (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f))

def fibrationComparisonIso {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [X.Quasicategory] [Fibration (ordinaryCoreCandidateMap p)] :
    (ordinaryCoreCandidate (pullback p f) : SSet.{u}) ≅
      pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) := by
  have := pullback_cores_kan p f
  exact comparisonIso p f

theorem comparisonIso_fst {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [(pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f)).KanComplex] :
    (comparisonIso p f).hom ≫
      pullback.fst (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) =
        ordinaryCoreCandidateMap (pullback.fst p f) := by
  simp [comparisonIso, toPullback]

theorem comparisonIso_snd {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [(pullback (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f)).KanComplex] :
    (comparisonIso p f).hom ≫
      pullback.snd (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f) =
        ordinaryCoreCandidateMap (pullback.snd p f) := by
  simp [comparisonIso, toPullback]

end
end DaggerNativeOriginalCorePullback
