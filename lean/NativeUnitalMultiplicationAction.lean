import TopCatModelCategory.SSet.FundamentalGroupoidAction
import TopCatModelCategory.ModelCategorySSet

/-! An actual strict unital multiplication kills the native loop action at its unit. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeUnitalMultiplicationAction
noncomputable section

def TrivialActionAt (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) (s : π n X x),
    action.map p s = s

theorem unitPoint_eq_const (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.unitHomEquiv X).symm x = (SSet.const x : 𝟙_ SSet.{u} ⟶ X) := by
  apply (SSet.unitHomEquiv X).injective
  rw [Equiv.apply_symm_apply]
  change x = (SSet.const x : 𝟙_ SSet.{u} ⟶ X).app (op ⦋0⦌) PUnit.unit
  simp only [SSet.const_app, SimplexCategory.const_eq_id,
    op_id, FunctorToTypes.map_id_apply]

def unitActionStruct {X : SSet.{u}} (x : X _⦋0⦌) (μ : X ⊗ X ⟶ X)
    (hL : ∀ (q : SimplexCategoryᵒᵖ) (a : X.obj q),
      μ.app q ((SSet.const x : 𝟙_ SSet.{u} ⟶ X).app q PUnit.unit, a) = a)
    (hR : ∀ (q : SimplexCategoryᵒᵖ) (a : X.obj q),
      μ.app q (a, (SSet.const x : 𝟙_ SSet.{u} ⟶ X).app q PUnit.unit) = a)
    {n : ℕ} (p : FundamentalGroupoid.Edge (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk x)) (s : X.PtSimplex n x) : ActionStruct p s s where
  map := lift (snd _ _ ≫ p.map) (fst _ _ ≫ s.map) ≫ μ
  whiskerRight_ι_comp_map := by
    have hs : (SSet.boundary n).ι ≫ s.map = SSet.const x := by
      simpa only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const] using s.comm
    apply NatTrans.ext
    funext q a
    change μ.app q (p.map.app q a.2, s.map.app q a.1.val) = p.map.app q a.2
    have hv := congrFun (NatTrans.congr_app hs q) a.1
    change s.map.app q a.1.val = (SSet.const x : 𝟙_ SSet.{u} ⟶ X).app q PUnit.unit at hv
    rw [hv]
    exact hR q _
  ι₀_map := by
    have hp : SSet.ι₀ ≫ snd (Δ[n] : SSet.{u}) Δ[1] ≫ p.map = SSet.const x := by
      rw [SSet.ι₀_snd_assoc, SSet.const_comp, p.comm₀']
    apply NatTrans.ext
    funext q a
    change μ.app q ((SSet.ι₀ ≫ snd (Δ[n] : SSet.{u}) Δ[1] ≫ p.map).app q a,
      s.map.app q a) = s.map.app q a
    rw [hp]
    exact hL q _
  ι₁_map := by
    have hp : SSet.ι₁ ≫ snd (Δ[n] : SSet.{u}) Δ[1] ≫ p.map = SSet.const x := by
      rw [SSet.ι₁_snd_assoc, SSet.const_comp, p.comm₁']
    apply NatTrans.ext
    funext q a
    change μ.app q ((SSet.ι₁ ≫ snd (Δ[n] : SSet.{u}) Δ[1] ≫ p.map).app q a,
      s.map.app q a) = s.map.app q a
    rw [hp]
    exact hL q _

theorem unit_action_trivial {X : SSet.{u}} [IsFibrant X]
    (x : X _⦋0⦌) (μ : X ⊗ X ⟶ X)
    (hL : ∀ (q : SimplexCategoryᵒᵖ) (a : X.obj q),
      μ.app q ((SSet.const x : 𝟙_ SSet.{u} ⟶ X).app q PUnit.unit, a) = a)
    (hR : ∀ (q : SimplexCategoryᵒᵖ) (a : X.obj q),
      μ.app q (a, (SSet.const x : 𝟙_ SSet.{u} ⟶ X).app q PUnit.unit) = a) :
    TrivialActionAt X x := by
  intro n p s
  obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
  obtain ⟨s, rfl⟩ := π.mk_surjective s
  exact action.map_eq (unitActionStruct x μ hL hR p s)

end
end DaggerNativeUnitalMultiplicationAction
