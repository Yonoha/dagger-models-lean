import OriginalVertexCosliceLeftLifting
import OriginalQuasicategoryInvertibleTriangles

/-!
# Original inverse triangles lifted through the actual left two-horn property

Glue an original edge and its source identity using the native (2,0)-horn
pushout. A prescribed target inverse triangle makes an original relative
commuting square. Native lifting gives an actual source inverse triangle and
the exact target inverse edge. Applying this twice reflects invertibility in
the same original path quotient; no source Kan or outer-horn premise is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerOriginalQuasicategoryInvertibleTriangles

universe u

namespace DaggerOriginalRelativeLeftTwoHornInverses

noncomputable section

/-- A prescribed target inverse triangle lifts to the same original source edge and identity. -/
theorem lift_inverse_triangle {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p]
    {x y : E.obj (op ⦋0⦌)} (e : SSet.Edge x y)
    (r : SSet.Edge (p.app (op ⦋0⦌) y) (p.app (op ⦋0⦌) x))
    (t : (e.map p).CompStruct r ((SSet.Edge.id x).map p)) :
    ∃ g : SSet.Edge y x, Nonempty (e.CompStruct g (SSet.Edge.id x)) ∧ g.map p = r := by
  let a : (Δ[1] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm e.edge
  let b : (Δ[1] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
  have wab : SSet.stdSimplex.δ 1 ≫ a = SSet.stdSimplex.δ 1 ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [a, b, Equiv.apply_symm_apply, e.src_eq, (SSet.Edge.id x).src_eq]
  let φ := SSet.horn₂₀.isPushout.desc a b wab
  let β : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have h01 : SSet.stdSimplex.δ 2 ≫ β = a ≫ p := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    simp only [β, a, Equiv.apply_symm_apply, t.d₂]
    rfl
  have h02 : SSet.stdSimplex.δ 1 ≫ β = b ≫ p := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    simp only [β, b, Equiv.apply_symm_apply, t.d₁]
    rfl
  have w : φ ≫ p = Λ[2, 0].ι ≫ β := by
    apply SSet.horn₂₀.isPushout.hom_ext
    · change (SSet.horn₂₀.ι₀₁ ≫ φ) ≫ p = (SSet.horn₂₀.ι₀₁ ≫ Λ[2, 0].ι) ≫ β
      rw [SSet.horn₂₀.isPushout.inl_desc, horn₀_inl_comp]
      exact h01.symm
    · change (SSet.horn₂₀.ι₀₂ ≫ φ) ≫ p = (SSet.horn₂₀.ι₀₂ ≫ Λ[2, 0].ι) ≫ β
      rw [SSet.horn₂₀.isPushout.inr_desc, horn₀_inr_comp]
      exact h02.symm
  let sq : CommSq φ (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p β := ⟨w⟩
  haveI : sq.HasLift := HasLiftingProperty.sq_hasLift sq
  let μ := sq.lift
  have hμ : φ = Λ[2, 0].ι ≫ μ := sq.fac_left.symm
  have hμp : μ ≫ p = β := sq.fac_right
  have hE01 : SSet.stdSimplex.δ 2 ≫ μ = a := by
    rw [← horn₀_inl_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₀.isPushout.inl_desc a b wab
  have hE02 : SSet.stdSimplex.δ 1 ≫ μ = b := by
    rw [← horn₀_inr_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₀.isPushout.inr_desc a b wab
  have d2 : E.δ 2 (SSet.yonedaEquiv μ) = e.edge := by
    simpa only [yonedaEquiv_coface, a, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hE01
  have d1 : E.δ 1 (SSet.yonedaEquiv μ) = (SSet.Edge.id x).edge := by
    simpa only [yonedaEquiv_coface, b, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hE02
  obtain ⟨a0, a1, a2, e01, e12, e02, v, hv⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv μ)
  have he01 : e01.edge = e.edge := by rw [← v.d₂, hv]; exact d2
  have he02 : e02.edge = (SSet.Edge.id x).edge := by rw [← v.d₁, hv]; exact d1
  have ha0 : a0 = x := by rw [← e01.src_eq, he01, e.src_eq]
  have ha1 : a1 = y := by rw [← e01.tgt_eq, he01, e.tgt_eq]
  have ha2 : a2 = x := by rw [← e02.tgt_eq, he02, (SSet.Edge.id x).tgt_eq]
  subst a0 a1 a2
  have h01e : e01 = e := SSet.Edge.ext he01
  have h02e : e02 = SSet.Edge.id x := SSet.Edge.ext he02
  subst e01 e02
  refine ⟨e12, ⟨v⟩, ?_⟩
  have hbase := congrArg SSet.yonedaEquiv hμp
  rw [SSet.yonedaEquiv_comp] at hbase
  change p.app (op ⦋2⦌) (SSet.yonedaEquiv μ) = SSet.yonedaEquiv β at hbase
  have ht : (v.map p).simplex = t.simplex := by
    change p.app (op ⦋2⦌) v.simplex = t.simplex
    rw [hv]
    exact hbase.trans (Equiv.apply_symm_apply _ _)
  have hd := congrArg (fun s ↦ X.δ 0 s) ht
  dsimp only at hd
  rw [(v.map p).d₀, t.d₀] at hd
  exact SSet.Edge.ext hd

/-- An original edge with invertible image admits a source inverse triangle with invertible image.
-/
theorem inverse_triangle_of_invertible_image {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p]
    (hX : innerHornFillers X) {x y : E.obj (op ⦋0⦌)} (e : SSet.Edge x y)
    (he : edgeIsInvertible X (e.map p).edge) :
    ∃ g : SSet.Edge y x, Nonempty (e.CompStruct g (SSet.Edge.id x)) ∧
      edgeIsInvertible X (g.map p).edge := by
  obtain ⟨r, ⟨t⟩, _, hr⟩ := inverse_triangles hX (e.map p) he
  have t' : (e.map p).CompStruct r ((SSet.Edge.id x).map p) := by
    simpa only [SSet.Edge.map_id] using t
  obtain ⟨g, hg, hgp⟩ := lift_inverse_triangle p e r t'
  exact ⟨g, hg, by rw [hgp]; exact hr⟩

/-- The actual relative left two-horn property reflects invertibility in the original path quotient.
-/
theorem original_homMk_isIso_of_invertible_image {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p]
    (hX : innerHornFillers X) {x y : E.obj (op ⦋0⦌)} (e : SSet.Edge x y)
    (he : edgeIsInvertible X (e.map p).edge) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
  obtain ⟨g, ⟨t⟩, hg⟩ := inverse_triangle_of_invertible_image p hX e he
  obtain ⟨h, ⟨v⟩, _⟩ := inverse_triangle_of_invertible_image p hX g hg
  have heg : SSet.Truncated.HomotopyCategory.homMk e ≫
      SSet.Truncated.HomotopyCategory.homMk g = 𝟙 _ :=
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t).trans
      (SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj E) x)
  have hgh : SSet.Truncated.HomotopyCategory.homMk g ≫
      SSet.Truncated.HomotopyCategory.homMk h = 𝟙 _ :=
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk v).trans
      (SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj E) y)
  have heh : SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk h := by
    calc
      _ = SSet.Truncated.HomotopyCategory.homMk e ≫
          (SSet.Truncated.HomotopyCategory.homMk g ≫
            SSet.Truncated.HomotopyCategory.homMk h) := by rw [hgh, Category.comp_id]
      _ = SSet.Truncated.HomotopyCategory.homMk h := by
        rw [← Category.assoc, heg, Category.id_comp]
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk g, heg, ?_⟩⟩
  rw [heh]
  exact hgh

/-- The same original unit-based invertibility predicate is reflected, with no source change. -/
theorem edgeIsInvertible_of_invertible_image {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p]
    (hX : innerHornFillers X) {x y : E.obj (op ⦋0⦌)} (e : SSet.Edge x y)
    (he : edgeIsInvertible X (e.map p).edge) : edgeIsInvertible E e.edge :=
  (edgeIsInvertible_iff_original_homMk_isIso E e).mpr
    (original_homMk_isIso_of_invertible_image p hX e he)

end

end DaggerOriginalRelativeLeftTwoHornInverses
