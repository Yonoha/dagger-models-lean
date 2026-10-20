import NativeFibrationWeakFromVertexFibres

/-! Reuse the previously proved native standard-simplex vertex weak equivalence.
A native Kan fibration covering vertices covers every simplex. If it is also mono,
the ORIGINAL whole simplicial map is an isomorphism, without fibrancy assumptions on objects.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeStandardSimplexContraction DaggerNativeFibrationWeakFromVertexFibres
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSSetMonoFibrationIso
noncomputable section

theorem surjective_app {X Y : SSet.{u}} (f : X ⟶ Y) [Fibration f]
    (hv : Function.Surjective (f.app (op ⦋0⦌))) (n : ℕ) :
    Function.Surjective (f.app (op ⦋n⦌)) := by
  intro y
  let φ : (Δ[n] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm y
  let v : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const (firstVertex n)
  have : Mono v := by
    constructor
    intro K a b _
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext a b
  have : Cofibration v := (SSet.modelCategoryQuillen.cofibration_iff v).mpr inferInstance
  have : WeakEquivalence v := first_vertex_weak n
  have : HasLiftingProperty v f := inferInstance
  obtain ⟨x, hx⟩ := hv (φ.app (op ⦋0⦌) (firstVertex n))
  have sq : CommSq (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) v f φ :=
    ⟨by simp only [v, SSet.const_comp, hx]⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
  exact sq.fac_right

theorem isIso_of_vertices {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] [Fibration f]
    (hv : Function.Surjective (f.app (op ⦋0⦌))) : IsIso f := by
  apply (NatTrans.isIso_iff_isIso_app f).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  exact ⟨(mono_iff_injective _).mp inferInstance, surjective_app f hv q.unop.len⟩

end
end DaggerNativeSSetMonoFibrationIso
