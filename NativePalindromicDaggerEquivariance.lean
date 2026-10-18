import NativeOrdinaryGroupoidSigma
import NativeGroupoidPalindromicNaturality

/-! The EXACT original inverse-dagger Sigma intertwines the EXACT real dagger fold. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeGroupoidChainExtension DaggerNativeGroupoidPalindromicSection
open DaggerNativeGroupoidPalindromicNaturality DaggerNativeOrdinaryGroupoidSigma
open DaggerNativeOrdinaryDaggerNerve DaggerNativeOrdinaryDaggerNerveLift
open DaggerNativePalindromicVertexFold DaggerNativeRealEdgewiseIndex
open DaggerNativeRealEdgewiseDaggerInvolution
universe u
namespace DaggerNativePalindromicDaggerEquivariance
noncomputable section
variable (C : Type u) [Groupoid.{u} C] [DaggerCategory C]

/-- Reversing an extended chain applies Sigma and reverses only its vertex parameter. -/
theorem reversal_ofVertices {n m : SimplexCategory} (F : Fin (n.len + 1) ⥤ C)
    (v : Fin (m.len + 1) → Fin (n.len + 1)) :
    SSet.opObjEquiv ((reversal C).app (op m) (ofVertices F v)) =
      ofVertices (F ⋙ sigmaFunctor C) (v ∘ Fin.rev) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change DaggerCategory.dagger (bridge F (v j.rev) (v i.rev)) =
    bridge (F ⋙ sigmaFunctor C) (v i.rev) (v j.rev)
  rw [bridge_postcomp, bridge_reverse F (v j.rev) (v i.rev), dagger_inv]
  rfl

/-- The WHOLE palindromic section exchanges ORIGINAL Sigma and ORIGINAL real dagger. -/
theorem section_comm :
    nerveMap (sigmaFunctor C) ≫ sectionMap C =
      sectionMap C ≫ involution (daggerNerve C) := by
  apply NatTrans.ext
  funext n F
  change fold C n.unop (F ⋙ sigmaFunctor C) =
    SSet.opObjEquiv ((reversal C).app (epsilon.op.obj n) (fold C n.unop F))
  unfold fold
  refine Eq.trans ?_ (reversal_ofVertices C (n := n.unop)
    (m := epsilon.obj n.unop) F (vertex n.unop)).symm
  apply congrArg (ofVertices (F ⋙ sigmaFunctor C))
  funext k
  exact (vertex_rev n.unop k).symm

end
end DaggerNativePalindromicDaggerEquivariance
