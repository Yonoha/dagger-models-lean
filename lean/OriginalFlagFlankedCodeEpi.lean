import OriginalFlagSurvivingBeads
import ChosenNecklaceBeadMaps
import ChosenNecklaceWedgeFunctor
import ChosenNecklacePointMaps
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {T U : NecklaceCode} {n : ℕ}
variable (F : Flag.{u} T n) (G : Flag.{u} U n)
variable (f : NecklaceCode.Hom.{u} T U) (hfg : NecklaceCode.Flag.map f F = G)
variable (hF : Flanked F) (hG : Flanked G)

/-- Only actual image-bead equality transports the original code operator's codomain. -/
private def codeBeadOperatorTo (c : T.Bead)
    (hc : orderMap f.map c.left < orderMap f.map c.right) (d : U.Bead)
    (hd : flankedImageBead F G f hfg hF hG c hc = d) : ⦋c.length⦌ ⟶ ⦋d.length⦌ :=
  flankedBeadOperator F G f hfg hF hG c hc ≫
    eqToHom (congrArg (fun e : U.Bead ↦ ⦋e.length⦌) hd)

private theorem codeBeadOperatorTo_triangle (c : T.Bead)
    (hc : orderMap f.map c.left < orderMap f.map c.right) (d : U.Bead)
    (hd : flankedImageBead F G f hfg hF hG c hc = d) :
    T.beadSimplex c ≫ f.map =
      SSet.stdSimplex.map (codeBeadOperatorTo F G f hfg hF hG c hc d hd) ≫
        U.beadSimplex d := by
  cases hd
  simpa only [codeBeadOperatorTo, eqToHom_refl, Category.comp_id] using
    flankedBeadOperator_triangle F G f hfg hF hG c hc

/-- The actual initial point supplies a preimage in EVERY degree, including N=0. -/
theorem flanked_code_point_app (m : ℕ) :
    f.map.app (op ⦋m⦌) ((pointAt T (ULift.up 0)).app _ (zeroSimplex m)) =
      (pointAt U (ULift.up 0)).app _ (zeroSimplex m) := by
  exact congrFun (NatTrans.congr_app (pointAt_first_comp f) (op ⦋m⦌)) (zeroSimplex m)

include hfg hF hG in
/-- Every target simplex lifts through its SAME point or bead, not just through vertices. -/
theorem flanked_code_app_surjective (m : ℕ) :
    Function.Surjective (f.map.app (op ⦋m⦌)) := by
  intro y
  obtain ⟨i, g, hg⟩ := U.simplex_factors_piece (SSet.yonedaEquiv.symm y)
  cases i with
  | none =>
      let z := SSet.yonedaEquiv g
      have hy : (U.pieceι none).app (op ⦋m⦌) z = y := by
        have he := congrArg SSet.yonedaEquiv hg
        rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] at he
        exact he
      have hz : ∀ k : Fin (m + 1), z.val k = 0 := by
        have hh := z.property
        change z.val ∈ (SSet.stdSimplex.face {0}).obj (op ⦋m⦌) at hh
        rw [SSet.stdSimplex.mem_face_iff] at hh
        intro k
        exact Finset.mem_singleton.mp (hh k)
      have hinc : U.inclusion.app _ ((U.pieceι none).app _ z) = z.val :=
        congrFun (NatTrans.congr_app (U.pieceι_inclusion none) (op ⦋m⦌)) z
      have hpoint : y = (pointAt U (ULift.up 0)).app _ (zeroSimplex m) := by
        apply constant_simplex_eq U (ULift.up 0) y
        intro k
        rw [← hy]
        exact (congrArg (fun x : (Δ[U.len] : SSet.{u}).obj (op ⦋m⦌) ↦ x k) hinc)
          |>.trans (hz k)
      refine ⟨(pointAt T (ULift.up 0)).app _ (zeroSimplex m), ?_⟩
      exact (flanked_code_point_app f m).trans hpoint.symm
  | some d =>
      let z := SSet.yonedaEquiv (g ≫ d.faceIso.inv)
      have ht : (g ≫ d.faceIso.inv) ≫ U.beadSimplex d = SSet.yonedaEquiv.symm y := by
        calc
          (g ≫ d.faceIso.inv) ≫ U.beadSimplex d = g ≫ U.beadι d := by
            simp only [NecklaceCode.beadSimplex, Category.assoc, Iso.inv_hom_id_assoc]
          _ = g ≫ U.pieceι (some d) := by rw [U.pieceι_some]
          _ = _ := hg
      have hy : (U.beadSimplex d).app (op ⦋m⦌) z = y := by
        have he := congrArg SSet.yonedaEquiv ht
        rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] at he
        exact he
      let c := survivingSourceBead F G f hfg hF hG d
      have hc : orderMap f.map c.left < orderMap f.map c.right :=
        survivingSourceBead_positive F G f hfg hF hG d
      have hd : flankedImageBead F G f hfg hF hG c hc = d :=
        survivingSourceBead_image F G f hfg hF hG d
      let s := codeBeadOperatorTo F G f hfg hF hG c hc d hd
      letI : Epi s := by
        dsimp only [s, codeBeadOperatorTo]
        infer_instance
      letI : IsSplitEpi s := isSplitEpi_of_epi s
      letI : IsSplitEpi (SSet.stdSimplex.map s) := by infer_instance
      obtain ⟨x, hx⟩ :=
        CategoryTheory.surjective_of_epi ((SSet.stdSimplex.map s).app (op ⦋m⦌)) z
      have htriangle := codeBeadOperatorTo_triangle F G f hfg hF hG c hc d hd
      have he := congrFun (NatTrans.congr_app htriangle (op ⦋m⦌)) x
      change f.map.app _ ((T.beadSimplex c).app _ x) =
        (U.beadSimplex d).app _ ((SSet.stdSimplex.map s).app _ x) at he
      rw [hx, hy] at he
      exact ⟨(T.beadSimplex c).app _ x, he⟩

include hfg hF hG in
/-- Epi of the SAME flanked code map, without Kan, Mono or a target map into X. -/
theorem flanked_code_epi : Epi f.map := by
  rw [NatTrans.epi_iff_epi_app]
  intro q
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with
  | _ m =>
      exact (CategoryTheory.epi_iff_surjective _).mpr
        (flanked_code_app_surjective F G f hfg hF hG m)

end

end DaggerOriginalFlagFlankification
