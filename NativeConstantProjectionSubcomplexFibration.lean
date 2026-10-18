import NativeSSetCoproductSummandFibration
import OriginalUnitaryDiscreteConstantRecovered

/-! A subcomplex cut out by values of a constant projection is a union of components. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeConstantProjectionSubcomplexFibration
noncomputable section

theorem constant_simplex_value {B : Type u} {n : SimplexCategory}
    (b : SSet.stdSimplex.obj n ⟶ DaggerUnitaryDiscrete.constSSet B)
    (q : SimplexCategoryᵒᵖ) (t : (SSet.stdSimplex.obj n).obj q) :
    b.app q t = SSet.yonedaEquiv b := by
  obtain ⟨c, rfl⟩ := SSet.yonedaEquiv.symm.surjective b
  rw [Equiv.apply_symm_apply]
  rfl

theorem hasLiftingProperty {X : SSet.{u}} {B : Type u} (A : X.Subcomplex)
    (p : X ⟶ DaggerUnitaryDiscrete.constSSet B) (U : Set B)
    (hm : ∀ q s, s ∈ A.obj q ↔ p.app q s ∈ U) (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι A.ι where
  sq_hasLift := by
    intro a b sq
    obtain ⟨v⟩ := DaggerNativeSSetCoproductSummandFibration.hornVertex_nonempty n k
    have hv : b.app (op ⦋0⦌) v.val ∈ A.obj (op ⦋0⦌) := by
      have hh := congrFun (NatTrans.congr_app sq.w (op ⦋0⦌)) v
      change (a.app (op ⦋0⦌) v).val = b.app (op ⦋0⦌) v.val at hh
      exact hh ▸ (a.app (op ⦋0⦌) v).property
    have hu : SSet.yonedaEquiv (b ≫ p) ∈ U := by
      have ht := (hm (op ⦋0⦌) (b.app (op ⦋0⦌) v.val)).mp hv
      change (b ≫ p).app (op ⦋0⦌) v.val ∈ U at ht
      rw [constant_simplex_value] at ht
      exact ht
    have hb : SSet.Subcomplex.range b ≤ A := by
      intro q x hx
      obtain ⟨t, rfl⟩ := hx
      apply (hm q _).mpr
      change (b ≫ p).app q t ∈ U
      rw [constant_simplex_value]
      exact hu
    refine CommSq.HasLift.mk' ⟨SSet.Subcomplex.lift b hb, ?_, SSet.Subcomplex.lift_ι b hb⟩
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, SSet.Subcomplex.lift_ι]
    exact sq.w.symm

theorem fibration {X : SSet.{u}} {B : Type u} (A : X.Subcomplex)
    (p : X ⟶ DaggerUnitaryDiscrete.constSSet B) (U : Set B)
    (hm : ∀ q s, s ∈ A.obj q ↔ p.app q s ∈ U) : Fibration A.ι := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro P Q f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  exact hasLiftingProperty A p U hm n k

end
end DaggerNativeConstantProjectionSubcomplexFibration
