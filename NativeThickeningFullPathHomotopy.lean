import NativeThickeningFullPaths

/-! The SAME native nerve homotopy fills each path to its full interval. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerNativeThickeningFullPaths
universe u
namespace DaggerNativeThickeningFullPathHomotopy
noncomputable section
variable {J : Type u} [LinearOrder J]

/-- Reuse the original natural-transformation nerve homotopy, with the exact interval. -/
def contraction (i j : J) :
    nerve (SimplicialThickening.Path i j) ⊗ (Δ[1] : SSet.{u}) ⟶
      nerve (SimplicialThickening.Path i j) :=
  DaggerNerveHomotopy.natTransMap (idToFull i j)

/-- Its object formula is the old path at zero and the full interval at one. -/
theorem contraction_obj_I (i j : J) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (t : (Δ[1] : SSet.{u}).obj q) (k : Fin (q.unop.len + 1)) :
    (((contraction i j).app q (p, t)).obj k).I =
      if (SSet.stdSimplex.objEquiv t).toOrderHom k = 0 then (p.obj k).I
      else Set.Icc i j := by
  change ((((ComposableArrows.mk₁ (idToFull i j)).obj
    ((SSet.stdSimplex.objEquiv t).toOrderHom k)).obj (p.obj k)).I) = _
  generalize ht : (SSet.stdSimplex.objEquiv t).toOrderHom k = a
  fin_cases a <;> rfl

/-- Composition always uses the original thickening composition map. -/
abbrev nativeComp (i j k : J) :=
  SimplicialThickening.SimplicialCategory.comp ⟨i⟩ ⟨j⟩ ⟨k⟩

/-- At the SAME interval parameter the full homotopy commutes with composition. -/
theorem contraction_comp (i j k : J) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (r : (nerve (SimplicialThickening.Path j k)).obj q)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (contraction i k).app q ((nativeComp i j k).app q (p, r), t) =
      (nativeComp i j k).app q
        ((contraction i j).app q (p, t), (contraction j k).app q (r, t)) := by
  refine CategoryTheory.Functor.ext (fun a ↦ SimplicialThickening.Path.ext ?_)
  change (((contraction i k).app q ((nativeComp i j k).app q (p, r), t)).obj a).I =
    (((contraction i j).app q (p, t)).obj a).I ∪
      (((contraction j k).app q (r, t)).obj a).I
  rw [contraction_obj_I, contraction_obj_I, contraction_obj_I]
  split_ifs
  · rfl
  · exact (fullPath_union i j k (p.obj a).le (r.obj a).le).symm

/-- The full homotopy fixes the SAME enriched identity at every interval simplex. -/
theorem contraction_id (i : J) (q : SimplexCategoryᵒᵖ)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (contraction i i).app q
      ((SimplicialThickening.SimplicialCategory.id ⟨i⟩).app q PUnit.unit, t) =
        (SimplicialThickening.SimplicialCategory.id ⟨i⟩).app q PUnit.unit := by
  refine CategoryTheory.Functor.ext (fun a ↦ SimplicialThickening.Path.ext ?_)
  rw [contraction_obj_I]
  change (if _ then ({i} : Set J) else Set.Icc i i) = {i}
  simp only [Set.Icc_self, ite_self]

/-- At zero this is the exact identity map on the original Hom nerve. -/
theorem contraction_zero (i j : J) :
    SSet.ι₀ ≫ contraction i j = 𝟙 (nerve (SimplicialThickening.Path i j)) := by
  calc
    _ = nerveMap (𝟭 (SimplicialThickening.Path i j)) :=
      (DaggerNerveHomotopy.natTransHomotopy (idToFull i j)).h₀
    _ = 𝟙 _ := by
      apply NatTrans.ext
      funext q p
      exact CategoryTheory.Functor.comp_id p

/-- At one it is exactly collapse followed by the original full-path center. -/
theorem contraction_one (i j : J) : SSet.ι₁ ≫ contraction i j =
    nerveMap (DaggerActualOrdinalRigidificationComparison.pathCollapse i j ⋙ center i j) :=
  (DaggerNerveHomotopy.natTransHomotopy (idToFull i j)).h₁

end
end DaggerNativeThickeningFullPathHomotopy
