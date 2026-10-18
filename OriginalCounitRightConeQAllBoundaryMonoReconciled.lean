import OriginalCounitRightConeQCommonLiftClassReconciled
import OriginalCounitRightConeQCommonBoundaryOverlapReconciled
import OriginalCounitRightConeQZeroBoundaryMonoReconciled

/-!
# Monicity of every literal right-cone Q boundary comparison

Equal images from distinct faces lift through their common original cone.
The original boundary-simplex diagram identifies the two resulting face
legs. Together with the zero-coface obstruction and split coface injection,
this proves monicity for the actual boundary-indexed colimit in every degree.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQLatching DaggerOriginalCounitRightConeQBoundaryMono
open DaggerOriginalCounitRightConeQBoundaryFaceOverlap
open DaggerOriginalCounitRightConeQCofaceInjection
open DaggerOriginalCounitRightConeQZeroBoundaryMono
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonBoundaryOverlap
open DaggerOriginalCounitRightConeQCommonLiftClass

universe u

namespace DaggerOriginalCounitRightConeQAllBoundaryMono

noncomputable section

/-- Common Q preimages witness every distinct positive-dimensional face overlap. -/
theorem positive_face_overlap (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (i j : Fin (n + 3)) (x y : (QFunctor.{u}.obj ⦋n + 1⦌).obj q)
    (heq : (QFunctor.{u}.map (SimplexCategory.δ i)).app q x =
      (QFunctor.{u}.map (SimplexCategory.δ j)).app q y) :
    (faceQToBoundary.{u} (n + 1) i).app q x =
      (faceQToBoundary.{u} (n + 1) j).app q y := by
  by_cases hij : i = j
  · subst j
    rw [Qcoface_app_injective (n + 1) i q heq]
  · cases q with
    | op d =>
        induction d using SimplexCategory.rec with | _ d
        obtain ⟨z, hz⟩ := two_Q_cofaces_common_preimage n d i j hij
          ((Qmap.{u} (SimplexCategory.δ i)).app (op ⦋d⦌) x) x y rfl heq.symm
        have hfi : QFunctor.{u}.map (factorI n i j hij) ≫
            QFunctor.{u}.map (SimplexCategory.δ i) =
              QFunctor.{u}.map (commonBaseHom n i j hij) := by
          rw [← CategoryTheory.Functor.map_comp, factorI_spec]
        have hfj : QFunctor.{u}.map (factorJ n i j hij) ≫
            QFunctor.{u}.map (SimplexCategory.δ j) =
              QFunctor.{u}.map (commonBaseHom n i j hij) := by
          rw [← CategoryTheory.Functor.map_comp, factorJ_spec]
        have hxi : (QFunctor.{u}.map (factorI n i j hij)).app (op ⦋d⦌) z = x := by
          apply Qcoface_app_injective (n + 1) i (op ⦋d⦌)
          have h := congrFun (NatTrans.congr_app hfi (op ⦋d⦌)) z
          exact h.trans hz
        have hxj : (QFunctor.{u}.map (factorJ n i j hij)).app (op ⦋d⦌) z = y := by
          apply Qcoface_app_injective (n + 1) j (op ⦋d⦌)
          have h := congrFun (NatTrans.congr_app hfj (op ⦋d⦌)) z
          exact h.trans (hz.trans heq)
        have h := congrFun (NatTrans.congr_app
          (commonQFaceLegs_agree.{u} n i j hij) (op ⦋d⦌)) z
        change (faceQToBoundary.{u} (n + 1) i).app (op ⦋d⦌)
          ((QFunctor.{u}.map (factorI n i j hij)).app (op ⦋d⦌) z) =
            (faceQToBoundary.{u} (n + 1) j).app (op ⦋d⦌)
              ((QFunctor.{u}.map (factorJ n i j hij)).app (op ⦋d⦌) z) at h
        rwa [hxi, hxj] at h

/-- The actual boundary of the zero-simplex has no simplex-index objects. -/
theorem boundaryZeroIndex_isEmpty :
    IsEmpty (SimplexIndex (∂Δ[0] : SSet.{u})) := by
  constructor
  intro σ
  let s := SSet.yonedaEquiv σ.hom
  have hs : ¬ Function.Surjective (SSet.stdSimplex.asOrderHom s.val) := s.property
  apply hs
  intro v
  refine ⟨0, ?_⟩
  apply Fin.ext
  have hv := v.isLt
  have h0 := ((SSet.stdSimplex.asOrderHom s.val) 0).isLt
  omega

/-- The original zero boundary comparison is monic because its source has no simplices. -/
theorem boundaryQMap_zero_mono : Mono (boundaryQMap.{u} 0) := by
  haveI := boundaryZeroIndex_isEmpty.{u}
  apply (NatTrans.mono_iff_mono_app _).2
  intro q
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y _
  have htop := SSet.iSup_range_eq_top_of_isColimit
    (colimit.isColimit (boundaryQDiagram.{u} 0))
  change (⨆ σ : SimplexIndex (∂Δ[0] : SSet.{u}),
    SSet.Subcomplex.range (colimit.ι (boundaryQDiagram.{u} 0) σ)) = ⊤ at htop
  have hx : x ∈ (⨆ σ : SimplexIndex (∂Δ[0] : SSet.{u}),
      SSet.Subcomplex.range (colimit.ι (boundaryQDiagram.{u} 0) σ)).obj q := by
    rw [htop]
    trivial
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion] at hx
  obtain ⟨σ, _⟩ := hx
  exact isEmptyElim σ

/-- Every actual boundary-indexed right-cone Q comparison is a monomorphism. -/
theorem boundaryQMap_mono (n : ℕ) : Mono (boundaryQMap.{u} n) := by
  cases n with
  | zero => exact boundaryQMap_zero_mono
  | succ k =>
      cases k with
      | zero => exact boundaryQMap_one_mono
      | succ n =>
          apply (boundaryQMap_mono_iff_face_overlap.{u} (n + 1)).2
          exact positive_face_overlap n

end

end DaggerOriginalCounitRightConeQAllBoundaryMono
