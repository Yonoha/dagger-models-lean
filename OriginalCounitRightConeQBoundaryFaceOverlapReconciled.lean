import OriginalCounitRightConeQBoundaryRecognitionReconciled

/-!
# The exact face-overlap criterion for the literal Q boundary map

All points of the boundary-indexed colimit come from codimension-one Q
faces. Thus the actual boundary comparison is monic exactly when every
equality between two face images already holds in that colimit. This does
not assume or prove the remaining flag-normal-form overlap implication.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQBoundaryMono
open DaggerOriginalCounitRightConeQBoundaryRecognition

universe u

namespace DaggerOriginalCounitRightConeQBoundaryFaceOverlap

noncomputable section

/-- Every simplex of the literal boundary Q colimit comes from a Q face. -/
theorem faceQToBoundary_jointly_surjective (k : ℕ) (q : SimplexCategoryᵒᵖ)
    (z : (boundaryQColimit.{u} (k + 1)).obj q) :
    ∃ (i : Fin (k + 2)) (x : (QFunctor.{u}.obj ⦋k⦌).obj q),
      (faceQToBoundary.{u} k i).app q x = z := by
  have htop := SSet.iSup_range_eq_top_of_isColimit
    (colimit.isColimit (boundaryQDiagram.{u} (k + 1)))
  change (⨆ σ : SimplexIndex (∂Δ[k + 1] : SSet.{u}),
      SSet.Subcomplex.range
        (colimit.ι (boundaryQDiagram.{u} (k + 1)) σ)) = ⊤ at htop
  have hz : z ∈ (⨆ σ : SimplexIndex (∂Δ[k + 1] : SSet.{u}),
      SSet.Subcomplex.range
        (colimit.ι (boundaryQDiagram.{u} (k + 1)) σ)).obj q := by
    rw [htop]
    trivial
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion,
    Set.mem_range] at hz
  obtain ⟨σ, x, hx⟩ := hz
  obtain ⟨i, g, hg⟩ := boundaryQ_leg_factors_face.{u} k σ
  refine ⟨i, (QFunctor.{u}.map g).app q x, ?_⟩
  have hpoint := congrFun (NatTrans.congr_app hg q) x
  simpa only [NatTrans.comp_app, types_comp_apply] using hpoint.symm.trans hx

/-- The only remaining monicity obligation is compatibility on each pair of
literal Q faces, in every simplicial degree. -/
theorem boundaryQMap_mono_iff_face_overlap (k : ℕ) :
    Mono (boundaryQMap.{u} (k + 1)) ↔
      ∀ (q : SimplexCategoryᵒᵖ) (i j : Fin (k + 2))
        (x y : (QFunctor.{u}.obj ⦋k⦌).obj q),
        (QFunctor.{u}.map (SimplexCategory.δ i)).app q x =
          (QFunctor.{u}.map (SimplexCategory.δ j)).app q y →
        (faceQToBoundary.{u} k i).app q x =
          (faceQToBoundary.{u} k j).app q y := by
  constructor
  · intro hm q i j x y heq
    have hinj : Function.Injective ((boundaryQMap.{u} (k + 1)).app q) :=
      (CategoryTheory.mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app _).1 hm q)
    apply hinj
    have hi := congrFun (NatTrans.congr_app (faceQToBoundary_comp.{u} k i) q) x
    have hj := congrFun (NatTrans.congr_app (faceQToBoundary_comp.{u} k j) q) y
    simpa only [NatTrans.comp_app, types_comp_apply] using hi.trans (heq.trans hj.symm)
  · intro hoverlap
    apply (NatTrans.mono_iff_mono_app _).2
    intro q
    apply (CategoryTheory.mono_iff_injective _).2
    intro x y hxy
    obtain ⟨i, xi, rfl⟩ := faceQToBoundary_jointly_surjective.{u} k q x
    obtain ⟨j, yj, rfl⟩ := faceQToBoundary_jointly_surjective.{u} k q y
    apply hoverlap q i j xi yj
    have hi := congrFun (NatTrans.congr_app (faceQToBoundary_comp.{u} k i) q) xi
    have hj := congrFun (NatTrans.congr_app (faceQToBoundary_comp.{u} k j) q) yj
    simpa only [NatTrans.comp_app, types_comp_apply] using hi.symm.trans (hxy.trans hj)

end

end DaggerOriginalCounitRightConeQBoundaryFaceOverlap
