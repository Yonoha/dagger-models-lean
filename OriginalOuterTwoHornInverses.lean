import OriginalQuasicategoryOuterTwoHorns

/-!
# Original path inverses from actual right outer two-horn fillers

The native pushout for the right outer two-horn glues an actual edge to the
identity at its target. A literal filler gives a left-inverse triangle. Applying
this construction a second time proves two-sided invertibility in the same
native path-quotient homotopy category. No Kan or quasi-category premise is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
open DaggerOriginalQuasicategoryOuterTwoHorns

universe u

namespace DaggerOriginalOuterTwoHornInverses

noncomputable section

/-- The literal right outer two-horn extension property, in arbitrary universe. -/
def rightOuterTwoHornFillers (X : SSet.{u}) : Prop :=
  ∀ σ₀ : (Λ[2, 2] : SSet.{u}) ⟶ X,
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X, σ₀ = Λ[2, 2].ι ≫ σ

/-- Every actual edge has a left-inverse triangle from the literal right outer two-horn. -/
theorem left_inverse_triangle {X : SSet.{u}} (hX : rightOuterTwoHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    ∃ r : SSet.Edge y x, Nonempty (r.CompStruct e (SSet.Edge.id y)) := by
  let a : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm (SSet.Edge.id y).edge
  let b : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  have w : SSet.stdSimplex.δ 0 ≫ a = SSet.stdSimplex.δ 0 ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [a, b, Equiv.apply_symm_apply, (SSet.Edge.id y).tgt_eq, e.tgt_eq]
  let φ := SSet.horn₂₂.isPushout.desc a b w
  obtain ⟨μ, hμ⟩ := hX φ
  have h02 : SSet.stdSimplex.δ 1 ≫ μ = a := by
    rw [← horn₂_inl_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₂.isPushout.inl_desc a b w
  have h12 : SSet.stdSimplex.δ 0 ≫ μ = b := by
    rw [← horn₂_inr_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₂.isPushout.inr_desc a b w
  have d1 : X.δ 1 (SSet.yonedaEquiv μ) = (SSet.Edge.id y).edge := by
    simpa only [yonedaEquiv_coface, a, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h02
  have d0 : X.δ 0 (SSet.yonedaEquiv μ) = e.edge := by
    simpa only [yonedaEquiv_coface, b, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h12
  obtain ⟨a0, a1, a2, e01, e12, e02, t, ht⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv μ)
  have he02 : e02.edge = (SSet.Edge.id y).edge := by
    rw [← t.d₁, ht]
    exact d1
  have he12 : e12.edge = e.edge := by
    rw [← t.d₀, ht]
    exact d0
  have ha0 : a0 = y := by rw [← e02.src_eq, he02, (SSet.Edge.id y).src_eq]
  have ha1 : a1 = x := by rw [← e12.src_eq, he12, e.src_eq]
  have ha2 : a2 = y := by rw [← e12.tgt_eq, he12, e.tgt_eq]
  subst a0 a1 a2
  have h02e : e02 = SSet.Edge.id y := SSet.Edge.ext he02
  have h12e : e12 = e := SSet.Edge.ext he12
  subst e02 e12
  exact ⟨e01, ⟨t⟩⟩

/-- Every original edge path class is invertible, using two successive actual triangles. -/
theorem original_homMk_isIso {X : SSet.{u}} (hX : rightOuterTwoHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
  obtain ⟨r, ⟨t⟩⟩ := left_inverse_triangle hX e
  obtain ⟨s, ⟨v⟩⟩ := left_inverse_triangle hX r
  have hr : SSet.Truncated.HomotopyCategory.homMk r ≫
      SSet.Truncated.HomotopyCategory.homMk e = 𝟙 _ := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t).trans
      (SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj X) y)
  have hs : SSet.Truncated.HomotopyCategory.homMk s ≫
      SSet.Truncated.HomotopyCategory.homMk r = 𝟙 _ := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk v).trans
      (SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj X) x)
  have hes : SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk s := by
    calc
      _ = (SSet.Truncated.HomotopyCategory.homMk s ≫
          SSet.Truncated.HomotopyCategory.homMk r) ≫
          SSet.Truncated.HomotopyCategory.homMk e := by rw [hs, Category.id_comp]
      _ = SSet.Truncated.HomotopyCategory.homMk s := by
        rw [Category.assoc, hr, Category.comp_id]
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk r, ?_, hr⟩⟩
  rw [hes]
  exact hs

/-- Every morphism in the same original path quotient is invertible, without edge-surjectivity. -/
theorem original_path_isIso {X : SSet.{u}} (hX : rightOuterTwoHornFillers X)
    {x y : ((SSet.truncation 2).obj X).HomotopyCategory} (f : x ⟶ y) : IsIso f := by
  have htop : MorphismProperty.isomorphisms ((SSet.truncation 2).obj X).HomotopyCategory =
      ⊤ := by
    apply SSet.Truncated.HomotopyCategory.morphismProperty_eq_top
    intro a b e
    exact original_homMk_isIso hX e
  have hf : MorphismProperty.isomorphisms ((SSet.truncation 2).obj X).HomotopyCategory f := by
    rw [htop]
    trivial
  exact hf

/-- The native homotopy category carries a groupoid structure from actual right two-horns. -/
def originalPathGroupoid (X : SSet.{u}) (hX : rightOuterTwoHornFillers X) :
    Groupoid ((SSet.truncation 2).obj X).HomotopyCategory :=
  Groupoid.ofIsIso (original_path_isIso hX)

end

end DaggerOriginalOuterTwoHornInverses
