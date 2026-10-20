import NativePiEvaluationFibreComponents
import NativeKanPointEvaluationFibration
import TopCatModelCategory.SSet.FundamentalGroupoidAction

/-! The original based-pi/evaluation-fibre equivalence is natural for actual target maps. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open SSet.KanComplex DaggerNativePiEvaluationFibreComponents
open DaggerNativeHornBoundaryAttachment DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiEvaluationFibreNaturality
noncomputable section

theorem boundary_vertex_ext (n : ℕ) (i : Fin (n + 2)) (X : SSet.{u})
    (v w : ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj X) _⦋0⦌)
    (hH : ((MonoidalClosed.pre
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _ v =
        ((MonoidalClosed.pre
          (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _ w)
    (hF : ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ v =
      ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ w) : v = w := by
  apply SSet.ihom₀Equiv.injective
  apply (boundary_horn_missing_face_isPushout n i).hom_ext
  · apply SSet.ihom₀Equiv.symm.injective
    simpa only [SSet.ihom₀Equiv_symm_comp, Equiv.symm_apply_apply] using hH
  · apply SSet.ihom₀Equiv.symm.injective
    simpa only [SSet.ihom₀Equiv_symm_comp, Equiv.symm_apply_apply] using hF

theorem restriction_target_vertex {A D X Y : SSet.{u}} (j : A ⟶ D)
    (v : ((ihom D).obj X) _⦋0⦌) (s : A ⟶ X) (f : X ⟶ Y)
    (h : ((MonoidalClosed.pre j).app X).app _ v = SSet.ihom₀Equiv.symm s) :
    ((MonoidalClosed.pre j).app Y).app _ (((ihom D).map f).app _ v) =
      SSet.ihom₀Equiv.symm (s ≫ f) := by
  have hn := congrFun (NatTrans.congr_app ((MonoidalClosed.pre j).naturality f) _) v
  change ((MonoidalClosed.pre j).app Y).app _ (((ihom D).map f).app _ v) =
    ((ihom A).map f).app _ (((MonoidalClosed.pre j).app X).app _ v) at hn
  rw [hn, h, ← SSet.ihom₀Equiv_symm_comp']

def evaluationFibreMap {D X Y : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D) (f : X ⟶ Y)
    (x : X _⦋0⦌) :
    (SSet.Subcomplex.fiber (pointEvaluation a X) x : SSet.{u}) ⟶
      (SSet.Subcomplex.fiber (pointEvaluation a Y) (f.app _ x) : SSet.{u}) :=
  SSet.Subcomplex.mapFiber (pointEvaluation a X) (pointEvaluation a Y)
    ((ihom D).map f) f (pointEvaluation_natural a f) _ _ rfl

theorem piEvaluationFibreEquiv_natural (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) (x : X _⦋0⦌) (s : π n X x) :
    SSet.mapπ₀ (evaluationFibreMap
        (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) f x)
        (piEvaluationFibreEquiv n i a X x s) =
      piEvaluationFibreEquiv n i a Y (f.app _ x) (mapπ f n x _ rfl s) := by
  obtain ⟨s, rfl⟩ := π.mk_surjective s
  rw [mapπ_mk]
  obtain ⟨v₀, h₀H, h₀F, he₀⟩ := piEvaluationFibreEquiv_mk_lift n i a X x s
  obtain ⟨v₁, h₁H, h₁F, he₁⟩ :=
    piEvaluationFibreEquiv_mk_lift n i a Y (f.app _ x) (s.pushforward f _ rfl)
  rw [he₀, he₁, SSet.mapπ₀_mk]
  apply congrArg SSet.π₀.mk
  apply Subtype.ext
  apply boundary_vertex_ext n i Y
  · change ((MonoidalClosed.pre
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app Y).app _
        (((ihom (SSet.boundary (n + 1) : SSet.{u})).map f).app _ v₀.val) = _
    rw [h₁H]
    simpa only [SSet.const_comp] using restriction_target_vertex _ _ _ f h₀H
  · change ((MonoidalClosed.pre (SSet.boundary.ι i)).app Y).app _
      (((ihom (SSet.boundary (n + 1) : SSet.{u})).map f).app _ v₀.val) = _
    rw [h₁F]
    exact restriction_target_vertex _ _ _ f h₀F

end
end DaggerNativePiEvaluationFibreNaturality
