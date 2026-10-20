import NativeInnerHornHoIso

/-! Any horn of dimension at least three determines a simplex in a native strict Segal set. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeHighHornRestrictionInjective
noncomputable section

theorem high_horn_restriction_injective {X : SSet.{u}} [X.IsStrictSegal]
    (n : ℕ) (i : Fin (n + 4)) {f g : (Δ[n + 3] : SSet.{u}) ⟶ X}
    (h : (Λ[n + 3, i] : (Δ[n + 3] : SSet.{u}).Subcomplex).ι ≫ f =
      (Λ[n + 3, i] : (Δ[n + 3] : SSet.{u}).Subcomplex).ι ≫ g) : f = g := by
  apply SSet.yonedaEquiv.injective
  apply (SSet.StrictSegal.ofIsStrictSegal X).spineInjective
  ext k
  simp only [SSet.StrictSegal.spineEquiv, Equiv.coe_fn_mk, SSet.spine_arrow]
  change X.map (SimplexCategory.mkOfSucc k).op
      (f.app (op ⦋n + 3⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 _))) =
    X.map (SimplexCategory.mkOfSucc k).op
      (g.app (op ⦋n + 3⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 _)))
  rw [← FunctorToTypes.naturality, ← FunctorToTypes.naturality]
  let q := SSet.horn.edge₃ (n + 3) i k.castSucc k.succ
    (Fin.castSucc_le_succ k) (by omega)
  have hq : q.val = (Δ[n + 3] : SSet.{u}).map (SimplexCategory.mkOfSucc k).op
      (SSet.stdSimplex.objEquiv.symm (𝟙 _)) := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [← hq]
  exact congrFun (NatTrans.congr_app h (op ⦋1⦌)) q

theorem horn_face_eq {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    {f g : (Δ[n + 1] : SSet.{u}) ⟶ X}
    (h : (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ f =
      (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ g)
    (j : Fin (n + 2)) (hj : j ≠ i) : SSet.stdSimplex.δ j ≫ f = SSet.stdSimplex.δ j ≫ g := by
  have hh := congrArg (fun p ↦ SSet.horn.ι i j hj ≫ p) h
  simpa only [← Category.assoc, SSet.horn.ι_ι] using hh

end
end DaggerNativeHighHornRestrictionInjective
