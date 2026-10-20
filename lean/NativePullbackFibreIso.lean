import TopCatModelCategory.SSet.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! A genuine pullback identifies the original native fibres by the actual fibre map. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
universe u
namespace DaggerNativePullbackFibreIso
noncomputable section

theorem fibre_outer_pullback {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (α : E ⟶ E') (β : B ⟶ B')
    (hs : IsPullback α p p' β) (b : B.obj (Opposite.op ⦋0⦌))
    (b' : B'.obj (Opposite.op ⦋0⦌)) (h : β.app _ b = b') :
    IsPullback ((SSet.Subcomplex.fiber p b).ι ≫ α)
      (SSet.stdSimplex.objZeroIsTerminal.from (SSet.Subcomplex.fiber p b : SSet.{u}))
      p' (SSet.yonedaEquiv.symm b') := by
  have ht := (SSet.Subcomplex.fiber_isPullback p b).paste_horiz hs
  simpa only [SSet.yonedaEquiv_symm_zero, SSet.const_comp, h] using ht

def pullbackFibreIso {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (α : E ⟶ E') (β : B ⟶ B')
    (hs : IsPullback α p p' β) (b : B.obj (Opposite.op ⦋0⦌))
    (b' : B'.obj (Opposite.op ⦋0⦌)) (h : β.app _ b = b') :
    (SSet.Subcomplex.fiber p b : SSet.{u}) ≅ (SSet.Subcomplex.fiber p' b' : SSet.{u}) :=
  (fibre_outer_pullback p p' α β hs b b' h).isoPullback ≪≫
    (SSet.Subcomplex.fiber_isPullback p' b').isoPullback.symm

theorem pullbackFibreIso_hom_ι {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (α : E ⟶ E') (β : B ⟶ B')
    (hs : IsPullback α p p' β) (b : B.obj (Opposite.op ⦋0⦌))
    (b' : B'.obj (Opposite.op ⦋0⦌)) (h : β.app _ b = b') :
    (pullbackFibreIso p p' α β hs b b' h).hom ≫ (SSet.Subcomplex.fiber p' b').ι =
      (SSet.Subcomplex.fiber p b).ι ≫ α := by
  dsimp only [pullbackFibreIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

theorem mapFiber_isIso_of_isPullback {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (α : E ⟶ E') (β : B ⟶ B')
    (hs : IsPullback α p p' β) (b : B.obj (Opposite.op ⦋0⦌))
    (b' : B'.obj (Opposite.op ⦋0⦌)) (h : β.app _ b = b') :
    IsIso (SSet.Subcomplex.mapFiber p p' α β hs.w b b' h) := by
  have he : SSet.Subcomplex.mapFiber p p' α β hs.w b b' h =
      (pullbackFibreIso p p' α β hs b b' h).hom := by
    apply (cancel_mono (SSet.Subcomplex.fiber p' b').ι).mp
    rw [SSet.Subcomplex.mapFiber_ι, pullbackFibreIso_hom_ι]
  rw [he]
  infer_instance

end
end DaggerNativePullbackFibreIso
