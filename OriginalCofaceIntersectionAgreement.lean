import OriginalStandardCofaceIntersections

/-!
# Standard common-face equations imply agreement on actual intersections

The native range factorization of the original double coface is epi onto the
entire face intersection. Cancel it and use the native face isomorphisms to
transfer the standard two-coface equation to the exact subcomplex overlap.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedCofaceGluing
open DaggerOriginalStandardCofaceIntersections

universe u

namespace DaggerOriginalCofaceIntersectionAgreement

noncomputable section

/-- Compatible standard coface maps agree on the whole original face intersection. -/
theorem intersection_agreement {X : SSet.{u}} {n : ℕ}
    (a b : Fin (n + 2)) (hab : a ≤ b)
    (μa μb : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (w : SSet.stdSimplex.δ a ≫ μb = SSet.stdSimplex.δ b ≫ μa) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso a.castSucc).inv ≫ μa) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso b.succ).inv ≫ μb) := by
  let A := SSet.stdSimplex.face.{u} {a.castSucc}ᶜ
  let B := SSet.stdSimplex.face.{u} {b.succ}ᶜ
  let ea := SSet.stdSimplex.faceSingletonComplIso.{u} a.castSucc
  let eb := SSet.stdSimplex.faceSingletonComplIso.{u} b.succ
  let p := SSet.stdSimplex.δ.{u} a ≫ SSet.stdSimplex.δ b.succ
  have hp : SSet.Subcomplex.range p = A ⊓ B := range_two_cofaces a b hab
  let t : (Δ[n] : SSet.{u}) ⟶
      ((A ⊓ B : (Δ[n + 2] : SSet.{u}).Subcomplex) : SSet.{u}) :=
    SSet.Subcomplex.toRange p ≫ SSet.Subcomplex.homOfLE hp.le
  haveI : IsIso (SSet.Subcomplex.homOfLE hp.le) := homOfLE_isIso_of_eq hp
  haveI : Epi t := by dsimp [t]; infer_instance
  have ht : t ≫ (A ⊓ B).ι = p := by
    dsimp [t]
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    rfl
  have ha : t ≫ SSet.Subcomplex.homOfLE inf_le_left =
      SSet.stdSimplex.δ b ≫ ea.hom := by
    apply (cancel_mono A.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, ht, Category.assoc,
      SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    exact (SSet.stdSimplex.map_comp _ _).symm.trans
      ((congrArg SSet.stdSimplex.map (SimplexCategory.δ_comp_δ hab)).trans
        (SSet.stdSimplex.map_comp _ _))
  have hb : t ≫ SSet.Subcomplex.homOfLE inf_le_right =
      SSet.stdSimplex.δ a ≫ eb.hom := by
    apply (cancel_mono B.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, ht, Category.assoc,
      SSet.stdSimplex.faceSingletonComplIso_hom_ι]
  apply (cancel_epi t).mp
  change t ≫ (SSet.Subcomplex.homOfLE inf_le_left ≫ (ea.inv ≫ μa)) =
    t ≫ (SSet.Subcomplex.homOfLE inf_le_right ≫ (eb.inv ≫ μb))
  have hleft := congrArg (fun r ↦ r ≫ (ea.inv ≫ μa)) ha
  have hright := congrArg (fun r ↦ r ≫ (eb.inv ≫ μb)) hb
  dsimp only at hleft hright
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hleft hright
  exact hleft.trans (w.symm.trans hright.symm)

end

end DaggerOriginalCofaceIntersectionAgreement
