import OriginalStrictGroupoidHomLowerHornFilling

/-!
# Fill every face of an actual original horn

After matching the faces below the missing one, correct the later faces in descending
order. The original face-preservation laws retain both the earlier lower faces and
all upper faces already fixed. No horn-filler existence premise is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidHomOperations
open DaggerOriginalStrictGroupoidHomFaceCorrection
open DaggerOriginalStrictGroupoidHomFacePreservation
open DaggerOriginalStrictGroupoidHomHornFaces
open DaggerOriginalStrictGroupoidHomLowerHornFilling

universe u

namespace DaggerOriginalStrictGroupoidHomAllHornFaces

noncomputable section

/-- Every actual original horn of dimension at least two has all its given faces filled. -/
theorem exists_all_faces_filled (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (x y : C.Obj) (i : Fin (n + 3))
    (h : (Λ[n + 2, i] : SSet.{u}) ⟶ C.enriched.Hom x y) :
    ∃ w : PointHom C (n + 2) x y,
      ∀ (r : Fin (n + 3)) (hr : r ≠ i),
        (C.enriched.Hom x y).δ r w = hornFaceValue i h r hr := by
  let S := C.enriched.Hom x y
  obtain ⟨w₀, hw₀⟩ := exists_lower_filled C hC n x y i h
  have hibound := i.is_lt
  have hstage : ∀ a : ℕ, a ≤ n + 2 - i.val →
      ∃ w : PointHom C (n + 2) x y,
        (∀ (r : Fin (n + 3)), r < i → ∀ hr : r ≠ i,
          S.δ r w = hornFaceValue i h r hr) ∧
        (∀ (r : Fin (n + 3)), n + 3 - a ≤ r.val → ∀ hr : r ≠ i,
          S.δ r w = hornFaceValue i h r hr) := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨w₀, hw₀, ?_⟩
      intro r hr _
      have hrbound := r.is_lt
      omega
    | succ a ih =>
      intro ha
      have habound : a ≤ n + 1 := by omega
      obtain ⟨w, hwlow, hwhigh⟩ := ih (by omega)
      let j : Fin (n + 2) := ⟨n + 1 - a, by omega⟩
      have hjval : j.val = n + 1 - a := rfl
      have hjbound := j.is_lt
      have hjlt : i < j.succ := by
        change i.val < j.val + 1
        omega
      let b := hornFaceValue i h j.succ (ne_of_gt hjlt)
      refine ⟨upperCorrection C hC (n + 1) j w b, ?_, ?_⟩
      · intro r hr hri
        have hrval : r.val < j.val := by
          have h' := Fin.lt_def.mp hr
          have h'' := Fin.lt_def.mp hjlt
          simp only [Fin.val_succ] at h''
          omega
        have hjpos : 0 < j.val := by omega
        let p : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have hp : p.succ = j := by
          apply Fin.ext
          dsimp [p]
          omega
        let l : Fin (n + 2) := ⟨r.val, by omega⟩
        have hl : l.castSucc = r := Fin.ext rfl
        have hlp : l ≤ p.castSucc := by
          change r.val ≤ j.val - 1
          omega
        have hmatch : S.δ l b = S.δ p.succ (S.δ l.castSucc w) := by
          have hh := hornFaceValue_compatible i h l j
            (by change r.val ≤ j.val; omega) (ne_of_gt hjlt)
            (by simpa only [hl] using hri)
          rw [hwlow l.castSucc (by simpa only [hl] using hr) (by
            simpa only [hl] using hri)]
          simpa only [b, hp] using hh
        have hpres : S.δ r (upperCorrection C hC (n + 1) j w b) = S.δ r w := by
          simpa only [hp, hl] using
            upperCorrection_preserves_lower C hC n p l hlp w b hmatch
        exact hpres.trans (hwlow r hr hri)
      · intro r hr hri
        by_cases heq : r = j.succ
        · subst r
          exact upperCorrection_face C hC (n + 1) j w b
        · have hrhigher : j.succ < r := by
            have hn : r.val ≠ j.val + 1 := fun he ↦ heq (Fin.ext he)
            change j.val + 1 < r.val
            omega
          have hrbound := r.is_lt
          have hrold : n + 3 - a ≤ r.val := by
            have h' := Fin.lt_def.mp hrhigher
            simp only [Fin.val_succ] at h'
            omega
          let q : Fin (n + 1) := ⟨j.val, by
            have h' := Fin.lt_def.mp hrhigher
            simp only [Fin.val_succ] at h'
            omega⟩
          have hq : q.castSucc = j := Fin.ext rfl
          let l : Fin (n + 2) := ⟨r.val - 1, by omega⟩
          have hl : l.succ = r := by
            apply Fin.ext
            dsimp [l]
            have h' := Fin.lt_def.mp hrhigher
            simp only [Fin.val_succ] at h'
            omega
          have hql : q.castSucc < l := by
            change j.val < r.val - 1
            have h' := Fin.lt_def.mp hrhigher
            simp only [Fin.val_succ] at h'
            omega
          have hqface : q.succ.castSucc = j.succ := congrArg Fin.succ hq
          have hmatch : S.δ l b = S.δ q.succ (S.δ l.succ w) := by
            have hh := hornFaceValue_compatible i h q.succ l
              (by
                change j.val + 1 ≤ r.val - 1
                have h' := Fin.lt_def.mp hrhigher
                simp only [Fin.val_succ] at h'
                omega)
              (by simpa only [hl] using hri)
              (by simpa only [hqface] using ne_of_gt hjlt)
            rw [hwhigh l.succ (by simpa only [hl] using hrold) (by
              simpa only [hl] using hri)]
            simpa only [b, hqface] using hh.symm
          have hpres : S.δ r (upperCorrection C hC (n + 1) j w b) = S.δ r w := by
            simpa only [hq, hl] using
              upperCorrection_preserves_upper C hC n q l hql w b hmatch
          exact hpres.trans (hwhigh r hrold hri)
  obtain ⟨w, hwlow, hwhigh⟩ := hstage (n + 2 - i.val) le_rfl
  refine ⟨w, ?_⟩
  intro r hri
  by_cases hr : r < i
  · exact hwlow r hr hri
  · apply hwhigh r ?_ hri
    have h' : i.val < r.val := Fin.lt_def.mp (lt_of_le_of_ne (le_of_not_gt hr) hri.symm)
    omega

end

end DaggerOriginalStrictGroupoidHomAllHornFaces
