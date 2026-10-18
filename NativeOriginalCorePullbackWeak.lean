import NativeOriginalCorePullback

/-! Base change of an actual map with Kan-trivial original core has Kan-weak original core. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeOriginalCoreWalkingInverse
open DaggerNativeOriginalCorePullback
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCorePullbackWeak
noncomputable section

theorem canonical_projection_weak {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B)
    [X.Quasicategory] [Fibration (ordinaryCoreCandidateMap p)]
    [WeakEquivalence (ordinaryCoreCandidateMap p)] :
    WeakEquivalence (ordinaryCoreCandidateMap (pullback.snd p f)) := by
  have := pullback_cores_kan p f
  have : WeakEquivalence
      (pullback.snd (ordinaryCoreCandidateMap p) (ordinaryCoreCandidateMap f)) := inferInstance
  rw [← comparisonIso_snd p f]
  infer_instance

theorem square_projection_weak {P E X B : SSet.{u}}
    {a : P ⟶ E} {b : P ⟶ X} {p : E ⟶ B} {f : X ⟶ B}
    (h : IsPullback a b p f) [X.Quasicategory]
    [Fibration (ordinaryCoreCandidateMap p)] [WeakEquivalence (ordinaryCoreCandidateMap p)] :
    WeakEquivalence (ordinaryCoreCandidateMap b) := by
  have : WeakEquivalence (ordinaryCoreCandidateMap (pullback.snd p f)) :=
    canonical_projection_weak p f
  let e := ordinaryCoreCandidateFunctor.mapIso h.isoPullback
  have he : e.hom ≫ ordinaryCoreCandidateMap (pullback.snd p f) =
      ordinaryCoreCandidateMap b := by
    change ordinaryCoreCandidateMap h.isoPullback.hom ≫ _ = _
    rw [← core_map_comp]
    congr 1
    simp
  rw [← he]
  infer_instance

end
end DaggerNativeOriginalCorePullbackWeak
