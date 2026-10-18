import NativeSSetFibrationSquareFibreWeak
import TopCatModelCategory.SSet.Fiber

/-! The existing weak-square theorem applies to the exact native Subcomplex.mapFiber. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open DaggerNativeSSetFibrationSquareFibreWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeakSquareNativeFibres
noncomputable section

theorem native_mapFiber_weak {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (h : f ≫ p' = p ≫ g) (b : B _⦋0⦌) (b' : B' _⦋0⦌) (hb : g.app _ b = b')
    [Fibration p] [Fibration p'] [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (SSet.Subcomplex.mapFiber p p' f g h b b' hb) := by
  let v : (Δ[0] : SSet.{u}) ⟶ B := SSet.yonedaEquiv.symm b
  let v' : (Δ[0] : SSet.{u}) ⟶ B' := SSet.yonedaEquiv.symm b'
  have hv : v ≫ g = v' := by
    simp only [v, v', SSet.yonedaEquiv_symm_zero, SSet.const_comp, hb]
  let m := fibreMap p p' f g h.symm v v' hv
  have : WeakEquivalence m := fibreMap_weakEquivalence p p' f g h.symm v v' hv
  let e := (SSet.Subcomplex.fiber_isPullback p b).isoPullback
  let e' := (SSet.Subcomplex.fiber_isPullback p' b').isoPullback
  have he : SSet.Subcomplex.mapFiber p p' f g h b b' hb ≫ e'.hom = e.hom ≫ m := by
    apply pullback.hom_ext
    · dsimp only [e, e']
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, SSet.Subcomplex.mapFiber_ι]
      rw [Category.assoc, fibreMap_fst, ← Category.assoc,
        IsPullback.isoPullback_hom_fst]
    · exact SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _
  have : WeakEquivalence (e.hom ≫ m) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac he

end
end DaggerNativeWeakSquareNativeFibres
