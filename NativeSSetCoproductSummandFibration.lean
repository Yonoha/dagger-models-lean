import OriginalSimplicialCategoryBarCoproductDegrees
import TopCatModelCategory.ModelCategorySSet

/-!
# Every actual simplicial coproduct summand inclusion is a Kan fibration

An entire standard simplex into the native coproduct belongs to one unchanged
summand. A vertex of every positive horn forces that same summand in a lifting
square. The resulting native horn lift adds no Kan condition on the summands.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSSetCoproductSummandFibration
noncomputable section

/-- Every positive horn contains a vertex, including either one-dimensional horn. -/
theorem hornVertex_nonempty (n : ℕ) (k : Fin (n + 2)) :
    Nonempty ((Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj (op ⦋0⦌)) := by
  refine ⟨⟨SSet.stdSimplex.obj₀Equiv.symm k, ?_⟩⟩
  change Set.range (fun _ : Fin 1 ↦ k) ∪ {k} ≠ Set.univ
  intro h
  obtain ⟨j, hj⟩ := exists_ne k
  have hm : j ∈ Set.range (fun _ : Fin 1 ↦ k) ∪ {k} := by rw [h]; trivial
  rcases hm with ⟨a, ha⟩ | ha
  · exact hj ha.symm
  · exact hj ha

/-- Every whole standard simplex factors through an actual entire original summand. -/
theorem simplex_factor_summand {I : Type u} (X : I → SSet.{u}) (n : ℕ)
    (b : (Δ[n] : SSet.{u}) ⟶ ∐ X) :
    ∃ (i : I) (g : (Δ[n] : SSet.{u}) ⟶ X i), g ≫ Sigma.ι X i = b := by
  obtain ⟨⟨i, a⟩, ha⟩ := (coproductDegreeEquiv X (op ⦋n⦌)).surjective
    (SSet.yonedaEquiv b)
  refine ⟨i, SSet.yonedaEquiv.symm a, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  change SSet.yonedaEquiv.symm (coproductDegreeEquiv X (op ⦋n⦌) ⟨i, a⟩) = b
  rw [ha]
  exact SSet.yonedaEquiv.symm_apply_apply b

/-- The actual summand inclusion lifts every native positive horn. -/
theorem coproductSummand_hasLiftingProperty {I : Type u} (X : I → SSet.{u}) (i : I)
    (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (Sigma.ι X i) where
  sq_hasLift := by
    intro a b sq
    obtain ⟨j, g, hg⟩ := simplex_factor_summand X (n + 1) b
    obtain ⟨v⟩ := hornVertex_nonempty n k
    have h : (Sigma.ι X i).app (op ⦋0⦌) (a.app (op ⦋0⦌) v) =
        (Sigma.ι X j).app (op ⦋0⦌) (g.app (op ⦋0⦌) v.val) :=
      (congrFun (NatTrans.congr_app sq.w (op ⦋0⦌)) v).trans
        (congrFun (NatTrans.congr_app hg (op ⦋0⦌)) v.val).symm
    have hij : i = j := (Sigma.mk.inj
      ((coproductDegreeEquiv X (op ⦋0⦌)).injective h)).1
    cases hij
    refine CommSq.HasLift.mk' ⟨g, ?_, hg⟩
    apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg]
    exact sq.w.symm

/-- Every unchanged native summand inclusion is a Kan-model fibration, without fibrancy. -/
theorem coproductSummand_fibration {I : Type u} (family : I → SSet.{u}) (i : I) :
    Fibration (Sigma.ι family i) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro P Q f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  exact coproductSummand_hasLiftingProperty family i n k

end
end DaggerNativeSSetCoproductSummandFibration
