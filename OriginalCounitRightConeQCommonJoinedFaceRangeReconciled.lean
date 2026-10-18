import OriginalCounitRightConeQCommonJoinedFaceReconciled

/-!
# The explicit common joined map fills the codimension-two face

The increasing joined vertex map is the unique order embedding onto the
large-simplex vertices avoiding the two omitted old vertices. The
standard-simplex image is therefore the full corresponding face.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQJoinVertexFormula
open DaggerOriginalCounitRightConeQCommonJoinedFace

universe u

namespace DaggerOriginalCounitRightConeQCommonJoinedFaceRange

noncomputable section

private theorem large_pair_complement_card (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    ({i.castSucc, j.castSucc}ᶜ : Finset (Fin (n + 4))).card = n + 2 := by
  have hij' : i.castSucc ≠ j.castSucc := by
    intro h
    exact hij (Fin.castSucc_inj.mp h)
  rw [Finset.card_compl, Finset.card_pair hij']
  simp

/-- The standard-simplex image of the explicitly enumerated common
old face is the large face omitting the two coface indices. -/
theorem commonJoinMap_range_eq_face (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    SSet.Subcomplex.range (joinMap.{u} (commonBaseHom n i j hij)) =
      SSet.stdSimplex.face.{u}
        ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ) := by
  let α := commonBaseHom n i j hij
  let S : Finset (Fin (n + 4)) := {i.castSucc, j.castSucc}ᶜ
  have hcard : S.card = n + 2 := large_pair_complement_card n i j hij
  let e : Fin (n + 2) ≃o S := Finset.orderIsoOfFin S hcard
  have hbase : Function.Injective α.toOrderHom := by
    intro x y h
    apply (commonBaseOrderIso n i j hij).injective
    exact Subtype.ext h
  have hjoin : Function.Injective (joinHom α).toOrderHom := by
    intro x y h
    cases x using Fin.lastCases with
    | last =>
        cases y using Fin.lastCases with
        | last => rfl
        | cast z =>
            have hlast : (joinHom α).toOrderHom (Fin.last (n + 1)) =
                Fin.last (n + 3) := by
              simpa using (joinHom_last α)
            change (joinHom α).toOrderHom (Fin.last (n + 1)) =
              (joinHom α).toOrderHom z.castSucc at h
            rw [hlast, joinHom_castSucc] at h
            exact False.elim ((Fin.castSucc_ne_last
              (α.toOrderHom z)) h.symm)
    | cast w =>
        cases y using Fin.lastCases with
        | last =>
            have hlast : (joinHom α).toOrderHom (Fin.last (n + 1)) =
                Fin.last (n + 3) := by
              simpa using (joinHom_last α)
            change (joinHom α).toOrderHom w.castSucc =
              (joinHom α).toOrderHom (Fin.last (n + 1)) at h
            rw [joinHom_castSucc, hlast] at h
            exact False.elim ((Fin.castSucc_ne_last
              (α.toOrderHom w)) h)
        | cast z =>
            rw [joinHom_castSucc, joinHom_castSucc] at h
            exact congrArg Fin.castSucc (hbase (Fin.castSucc_inj.mp h))
  let f : Fin (n + 2) ↪o Fin (n + 4) :=
    OrderEmbedding.ofStrictMono _
      ((joinHom α).toOrderHom.monotone.strictMono_of_injective hjoin)
  let g : Fin (n + 2) ↪o Fin (n + 4) := S.orderEmbOfFin hcard
  have hfg : f = g := by
    apply OrderEmbedding.range_inj.mp
    calc
      Set.range f = {v | v ≠ i.castSucc ∧ v ≠ j.castSucc} := by
        ext v
        exact commonJoinHom_vertex_range n i j hij v
      _ = (S : Set (Fin (n + 4))) := by
        ext v
        simp [S, and_comm]
      _ = Set.range g := (Finset.range_orderEmbOfFin S hcard).symm
  have hhom : joinHom α =
      SimplexCategory.Hom.mk (a := ⦋n + 1⦌) (b := ⦋n + 3⦌)
        g.toOrderHom := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    exact DFunLike.congr_fun hfg v
  have hface : SSet.Subcomplex.range (joinMap.{u} α) =
      SSet.stdSimplex.face.{u} S := by
    rw [joinMap, hhom, SSet.Subcomplex.range_eq_ofSimplex,
      SSet.stdSimplex.yonedaEquiv_map]
    exact (SSet.stdSimplex.face_eq_ofSimplex S (n + 1) e).symm
  have hS : S = {i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ := by
    ext v
    simp [S]
  rw [hS] at hface
  exact hface

end

end DaggerOriginalCounitRightConeQCommonJoinedFaceRange
