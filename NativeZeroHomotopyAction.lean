import NativeUnitalMultiplicationAction

/-! Native fundamental loops act trivially on degree-zero homotopy classes. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeZeroHomotopyAction
noncomputable section

theorem zero_action_trivial {X : SSet.{u}} [IsFibrant X] (x : X _⦋0⦌)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) (s : π 0 X x) :
    action.map p s = s := by
  obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
  obtain ⟨s, rfl⟩ := π.mk_surjective s
  let t := action.map' p s
  have h : ActionStruct p s t := action.actionStruct p s
  rw [action.map_eq h]
  obtain ⟨a, rfl⟩ := (SSet.PtSimplex.equiv₀ x).symm.surjective s
  obtain ⟨b, hb⟩ := (SSet.PtSimplex.equiv₀ x).symm.surjective t
  rw [← hb] at h ⊢
  apply SSet.Subcomplex.RelativeMorphism.Homotopy.eq
  exact ((SSet.PtSimplex.Homotopy.equiv₀ x).symm ((ActionStruct.equiv₀ p) h)).symm

end
end DaggerNativeZeroHomotopyAction
