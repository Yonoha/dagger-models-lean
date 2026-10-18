import OriginalStrictGroupoidHomFacePreservation
import OriginalStrictGroupoidHomHornFaces

/-!
# Fill all original faces below the missing horn face

For every actual original horn map, start with a degeneracy of one of its existing
faces and perform the original groupoid correction successively. The previously
proved actual matching equations preserve every face already filled.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidHomOperations
open DaggerOriginalStrictGroupoidHomFaceCorrection
open DaggerOriginalStrictGroupoidHomFacePreservation
open DaggerOriginalStrictGroupoidHomHornFaces

universe u

namespace DaggerOriginalStrictGroupoidHomLowerHornFilling

noncomputable section

/-- Every actual original horn can be matched on all faces below its missing face. -/
theorem exists_lower_filled (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (x y : C.Obj) (i : Fin (n + 3))
    (h : (Λ[n + 2, i] : SSet.{u}) ⟶ C.enriched.Hom x y) :
    ∃ w : PointHom C (n + 2) x y,
      ∀ (r : Fin (n + 3)), r < i → ∀ hr : r ≠ i,
        (C.enriched.Hom x y).δ r w = hornFaceValue i h r hr := by
  let S := C.enriched.Hom x y
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  let w₀ : PointHom C (n + 2) x y :=
    S.σ (0 : Fin (n + 2)) (hornFaceValue i h j₀ hj₀)
  have hstage : ∀ k : Fin (n + 3), k ≤ i →
      ∃ w : PointHom C (n + 2) x y,
        ∀ (r : Fin (n + 3)), r < k → ∀ hr : r ≠ i,
          S.δ r w = hornFaceValue i h r hr := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro _
      exact ⟨w₀, fun r hr _ ↦ False.elim (Fin.not_lt_zero r hr)⟩
    | succ j ih =>
      intro hji
      have hjlt : j.castSucc < i := by
        change j.val < i.val
        have h' := Fin.le_def.mp hji
        simp only [Fin.val_succ] at h'
        omega
      obtain ⟨w, hw⟩ := ih (le_of_lt hjlt)
      let a := hornFaceValue i h j.castSucc (ne_of_lt hjlt)
      refine ⟨lowerCorrection C hC (n + 1) j w a, ?_⟩
      intro r hr hri
      by_cases heq : r = j.castSucc
      · subst r
        exact lowerCorrection_face C hC (n + 1) j w a
      · have hrprev : r < j.castSucc := by
          have h' := Fin.lt_def.mp hr
          have hn : r.val ≠ j.val := fun he ↦ heq (Fin.ext he)
          simp only [Fin.val_succ] at h'
          change r.val < j.val
          omega
        have hjpos : 0 < j.val := by
          have h' := Fin.lt_def.mp hrprev
          simp only [Fin.val_castSucc] at h'
          omega
        have hjbound := j.is_lt
        let p : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have hp : p.succ = j := by
          apply Fin.ext
          dsimp [p]
          omega
        let l : Fin (n + 2) := ⟨r.val, by
          have h' := Fin.lt_def.mp hrprev
          simp only [Fin.val_castSucc] at h'
          omega⟩
        have hl : l.castSucc = r := Fin.ext rfl
        have hlp : l ≤ p.castSucc := by
          change r.val ≤ j.val - 1
          have h' := Fin.lt_def.mp hrprev
          simp only [Fin.val_castSucc] at h'
          omega
        have hpface : p.castSucc.succ = j.castSucc := congrArg Fin.castSucc hp
        have hmatch : S.δ l a = S.δ p.castSucc (S.δ l.castSucc w) := by
          have hh := hornFaceValue_compatible i h l p.castSucc hlp
            (by simpa only [hpface] using ne_of_lt hjlt)
            (by simpa only [hl] using hri)
          rw [hw l.castSucc (by simpa only [hl] using hrprev) (by
            simpa only [hl] using hri)]
          simpa only [a, hpface] using hh
        have hpres : S.δ r (lowerCorrection C hC (n + 1) j w a) = S.δ r w := by
          simpa only [hp, hl] using
            lowerCorrection_preserves_lower C hC n p l hlp w a hmatch
        exact hpres.trans (hw r hrprev hri)
  exact hstage i le_rfl

end

end DaggerOriginalStrictGroupoidHomLowerHornFilling
