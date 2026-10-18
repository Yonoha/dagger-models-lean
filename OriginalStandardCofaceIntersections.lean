import OriginalJoinedCofaceGluing

/-!
# Exact intersections of two original standard cofaces

The native composite of two cofaces has range equal to the actual intersection
of the two omitted-vertex faces. Its native range factorization is epi onto
that entire intersection. This lets standard common-face identities establish
agreement everywhere on the overlap, in every dimension and universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalStandardCofaceIntersections

/-- Below the omitted vertex, the coface has exactly the original vertex as preimage. -/
theorem coface_eq_castSucc_iff {n : ℕ} (a b : Fin (n + 2)) (hab : a ≤ b)
    (x : Fin (n + 2)) : b.succ.succAbove x = a.castSucc ↔ x = a := by
  have ha : b.succ.succAbove a = a.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by
      change a.val < b.val + 1
      change a.val ≤ b.val at hab
      omega)
  rw [← ha, Fin.succAbove_inj]

/-- The preimage of the other original omitted-vertex face is exactly its smaller face. -/
theorem face_preimage_coface {n : ℕ} (a b : Fin (n + 2)) (hab : a ≤ b) :
    (SSet.stdSimplex.face.{u} {a.castSucc}ᶜ).preimage (SSet.stdSimplex.δ b.succ) =
      SSet.stdSimplex.face {a}ᶜ := by
  ext q s
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (SSet.stdSimplex.δ b.succ).app (op ⦋d⦌) s ∈
        (SSet.stdSimplex.face {a.castSucc}ᶜ).obj (op ⦋d⦌) ↔
        s ∈ (SSet.stdSimplex.face {a}ᶜ).obj (op ⦋d⦌)
      rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
      simp only [Finset.mem_compl, Finset.mem_singleton]
      constructor <;> intro h x hx
      · apply h x
        change b.succ.succAbove (SSet.stdSimplex.asOrderHom s x) = a.castSucc
        exact (coface_eq_castSucc_iff a b hab _).mpr hx
      · apply h x
        exact (coface_eq_castSucc_iff a b hab (SSet.stdSimplex.asOrderHom s x)).mp hx

/-- The image of an original inverse image is its intersection with the original range. -/
theorem image_preimage_eq_inf_range {Y Z : SSet.{u}} (A : Z.Subcomplex) (f : Y ⟶ Z) :
    (A.preimage f).image f = A ⊓ SSet.Subcomplex.range f := by
  apply le_antisymm
  · exact le_inf (SSet.Subcomplex.image_preimage_le A f)
      (SSet.Subcomplex.image_le_range _ _)
  · intro q s hs
    obtain ⟨t, ht⟩ := hs.2
    refine ⟨t, ?_, ht⟩
    change f.app q t ∈ A.obj q
    rw [ht]
    exact hs.1

/-- The original double coface covers precisely the entire actual common-face subcomplex. -/
theorem range_two_cofaces {n : ℕ} (a b : Fin (n + 2)) (hab : a ≤ b) :
    SSet.Subcomplex.range (SSet.stdSimplex.δ.{u} a ≫ SSet.stdSimplex.δ b.succ) =
      SSet.stdSimplex.face {a.castSucc}ᶜ ⊓ SSet.stdSimplex.face {b.succ}ᶜ := by
  rw [SSet.Subcomplex.range_comp, SSet.stdSimplex.range_δ,
    ← face_preimage_coface a b hab, image_preimage_eq_inf_range, SSet.stdSimplex.range_δ]

end DaggerOriginalStandardCofaceIntersections
