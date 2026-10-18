import RigidificationCofRestrictions

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

theorem properMap_restrict (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (t : Finset (Fin (n + 2))) (ht : t.Nonempty) (hpt : t ≠ Finset.univ)
    (hi : i ∈ t) (hj : j ∈ t) :
    homFromFace t i j hi hj ≫ properMap a i j hp = faceMap a t ht hpt i j hi hj := by
  by_cases hij : i ≤ j
  · simpa only [properMap, dif_pos hij] using
      forwardProperMap_restrict a i j hij hp t ht hpt hi hj
  · exact empty_hom_ext (J := ULift.{u} t)
      (i := ULift.up ⟨i, hi⟩) (j := ULift.up ⟨j, hj⟩)
      (show (ULift.up ⟨j, hj⟩ : ULift.{u} t) < ULift.up ⟨i, hi⟩
        from lt_of_not_ge hij) _ _

theorem homFromFace_id (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    eId SSet.{u} (label s i hi) ≫ homFromFace s i i hi hi =
      eId SSet.{u} (SimplicialThickening.mk (ULift.up i)) :=
  (SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom).map_id _

theorem diagonal_proper (i : Fin (n + 2)) : ¬ (i = 0 ∧ i = Fin.last (n + 1)) := by
  rintro ⟨h0, hn⟩
  have h := congrArg Fin.val (h0.symm.trans hn)
  simp only [Fin.val_zero, Fin.val_last] at h
  omega

theorem properMap_id (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up i)) ≫
      properMap a i i (diagonal_proper i) = eId SSet (vertex a i) := by
  let s := Finset.Icc i i
  have hi : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  have hs := intervalNonempty i i le_rfl
  have hp := intervalProper i i (diagonal_proper i)
  rw [← homFromFace_id s i hi, Category.assoc, properMap_restrict a i i _ s hs hp hi hi]
  exact (canonicalFaceFunctor a s hs hp).map_id (label s i hi)

/-- Both original proper Hom maps are restrictions of ONE full proper-face functor. -/
theorem properMap_comp_forward (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (i j k : Fin (n + 2)) (hij : i ≤ j) (hjk : j ≤ k)
    (hpik : ¬ (i = 0 ∧ k = Fin.last (n + 1)))
    (hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)))
    (hpjk : ¬ (j = 0 ∧ k = Fin.last (n + 1))) :
    compose (ULift.up i) (ULift.up j) (ULift.up k) ≫ properMap a i k hpik =
      (properMap a i j hpij ⊗ₘ properMap a j k hpjk) ≫
        eComp SSet (vertex a i) (vertex a j) (vertex a k) := by
  let s := Finset.Icc i k
  have hik := hij.trans hjk
  have hi : i ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hik⟩
  have hj : j ∈ s := Finset.mem_Icc.mpr ⟨hij, hjk⟩
  have hk : k ∈ s := Finset.mem_Icc.mpr ⟨hik, le_rfl⟩
  have hs := intervalNonempty i k hik
  have hp := intervalProper i k hpik
  let e := subsetEmbedding.{u} s
  have hconv₁ : ∀ x : vertices.{u} (n + 1),
      e (ULift.up ⟨i, hi⟩) ≤ x → x ≤ e (ULift.up ⟨j, hj⟩) → x ∈ Set.range e := by
    intro x hx hy
    exact ⟨⟨⟨x.down, Finset.mem_Icc.mpr ⟨hx, hy.trans hjk⟩⟩⟩, rfl⟩
  have hconv₂ : ∀ x : vertices.{u} (n + 1),
      e (ULift.up ⟨j, hj⟩) ≤ x → x ≤ e (ULift.up ⟨k, hk⟩) → x ∈ Set.range e := by
    intro x hx hy
    exact ⟨⟨⟨x.down, Finset.mem_Icc.mpr ⟨hij.trans hx, hy⟩⟩⟩, rfl⟩
  let e₁ := convexHomIso e (ULift.up ⟨i, hi⟩) (ULift.up ⟨j, hj⟩) hconv₁
  let e₂ := convexHomIso e (ULift.up ⟨j, hj⟩) (ULift.up ⟨k, hk⟩) hconv₂
  apply (cancel_epi (e₁.hom ⊗ₘ e₂.hom)).mp
  change (homFromFace s i j hi hj ⊗ₘ homFromFace s j k hj hk) ≫ _ =
    (homFromFace s i j hi hj ⊗ₘ homFromFace s j k hj hk) ≫
      (properMap a i j hpij ⊗ₘ properMap a j k hpjk) ≫ _
  rw [tensorHom_comp_tensorHom_assoc]
  rw [properMap_restrict a i j hpij s hs hp hi hj,
    properMap_restrict a j k hpjk s hs hp hj hk]
  have hc := (SimplicialThickening.functor e.toOrderHom).map_comp
    (label s i hi) (label s j hj) (label s k hk)
  have hc' : eComp SSet.{u} (label s i hi) (label s j hj) (label s k hk) ≫
      homFromFace s i k hi hk =
      (homFromFace s i j hi hj ⊗ₘ homFromFace s j k hj hk) ≫
        compose (ULift.up i) (ULift.up j) (ULift.up k) := hc
  change _ = (faceMap a s hs hp i j hi hj ⊗ₘ faceMap a s hs hp j k hj hk) ≫ _
  rw [← Category.assoc, ← hc', Category.assoc,
    properMap_restrict a i k hpik s hs hp hi hk]
  exact (canonicalFaceFunctor a s hs hp).map_comp
    (label s i hi) (label s j hj) (label s k hk)

end

end DaggerOrdinaryRigidificationCof.BoundaryData
