import AmalgamStageEvaluation

/-! Full interior injectivity and coverage of the original four rank stages. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamUnitBoundary DaggerAmalgamPaddedClassifier
open DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem evaluationOO_interior_injective (a d : C.Obj) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v w' : (familyOO C B x b a d n).obj q)
    (hv : v ∉ (boundaryOO C B x b a d n).obj q)
    (hw' : w' ∉ (boundaryOO C B x b a d n).obj q)
    (he : (evaluationOO C B x b a d n).app q v =
      (evaluationOO C B x b a d n).app q w') : v = w' := by
  apply (familyOO_degreeEquiv C B x b a d n q).injective
  exact evalOO_interior_injective C B x b q a d n
    ⟨familyOO_degreeEquiv C B x b a d n q v,
      fun hc ↦ hv ((boundaryOO_iff_critical C B x b a d n q v).2 hc)⟩
    ⟨familyOO_degreeEquiv C B x b a d n q w',
      fun hc ↦ hw' ((boundaryOO_iff_critical C B x b a d n q w').2 hc)⟩ he

theorem evaluationON_interior_injective (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v w' : (familyON C B x b a w n).obj q)
    (hv : v ∉ (boundaryON C B x b a w n).obj q)
    (hw' : w' ∉ (boundaryON C B x b a w n).obj q)
    (he : (evaluationON C B x b a w n).app q v =
      (evaluationON C B x b a w n).app q w') : v = w' := by
  apply (familyON_degreeEquiv C B x b a w n q).injective
  exact evalON_interior_injective C B x b q a w hw n
    ⟨familyON_degreeEquiv C B x b a w n q v,
      fun hc ↦ hv ((boundaryON_iff_critical C B x b a w n q v).2 hc)⟩
    ⟨familyON_degreeEquiv C B x b a w n q w',
      fun hc ↦ hw' ((boundaryON_iff_critical C B x b a w n q w').2 hc)⟩ he

theorem evaluationNO_interior_injective (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v w' : (familyNO C B x b z d n).obj q)
    (hv : v ∉ (boundaryNO C B x b z d n).obj q)
    (hw' : w' ∉ (boundaryNO C B x b z d n).obj q)
    (he : (evaluationNO C B x b z d n).app q v =
      (evaluationNO C B x b z d n).app q w') : v = w' := by
  apply (familyNO_degreeEquiv C B x b z d n q).injective
  exact evalNO_interior_injective C B x b q z d hz n
    ⟨familyNO_degreeEquiv C B x b z d n q v,
      fun hc ↦ hv ((boundaryNO_iff_critical C B x b z d n q v).2 hc)⟩
    ⟨familyNO_degreeEquiv C B x b z d n q w',
      fun hc ↦ hw' ((boundaryNO_iff_critical C B x b z d n q w').2 hc)⟩ he

theorem evaluationNN_interior_injective (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v w' : (familyNN C B x b z w n).obj q)
    (hv : v ∉ (boundaryNN C B x b z w n).obj q)
    (hw' : w' ∉ (boundaryNN C B x b z w n).obj q)
    (he : (evaluationNN C B x b z w n).app q v =
      (evaluationNN C B x b z w n).app q w') : v = w' := by
  apply (familyNN_degreeEquiv C B x b z w n q).injective
  exact evalNN_interior_injective C B x b q z w hz hw n
    ⟨familyNN_degreeEquiv C B x b z w n q v,
      fun hc ↦ hv ((boundaryNN_iff_critical C B x b z w n q v).2 hc)⟩
    ⟨familyNN_degreeEquiv C B x b z w n q w',
      fun hc ↦ hw' ((boundaryNN_iff_critical C B x b z w n q w').2 hc)⟩ he

theorem evaluationOO_covers_successor (a d : C.Obj) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (h : (oldOldStage C B x b (n + 1) a d).toSSet.obj q) :
    h.val ∈ (oldOldStage C B x b n a d).obj q ∨
      ∃ v : (familyOO C B x b a d (n + 1)).obj q,
        (evaluationOO C B x b a d (n + 1)).app q v = h.val := by
  classical
  by_cases hs : h.val ∈ (oldOldStage C B x b n a d).obj q
  · exact Or.inl hs
  · right
    have hr : rankOf C B x b false q h.val = n + 1 := by
      have hl : rankOf C B x b false q h.val ≤ n + 1 := h.property
      have hn : ¬ rankOf C B x b false q h.val ≤ n := hs
      omega
    obtain ⟨v, hv⟩ := evalOO_covers_rank C B x b q a d (n + 1) h.val hr
    refine ⟨(familyOO_degreeEquiv C B x b a d (n + 1) q).symm v.val, ?_⟩
    change evalOO C B x b q a d (n + 1)
      ((familyOO_degreeEquiv C B x b a d (n + 1) q)
        ((familyOO_degreeEquiv C B x b a d (n + 1) q).symm v.val)) = h.val
    rw [Equiv.apply_symm_apply]
    exact hv

theorem evaluationON_covers_successor (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (h : (oldNewStage C B x b (n + 1) a w).toSSet.obj q) :
    h.val ∈ (oldNewStage C B x b n a w).obj q ∨
      ∃ v : (familyON C B x b a w (n + 1)).obj q,
        (evaluationON C B x b a w (n + 1)).app q v = h.val := by
  classical
  by_cases hs : h.val ∈ (oldNewStage C B x b n a w).obj q
  · exact Or.inl hs
  · right
    have hr : rankOf C B x b true q h.val = n + 1 := by
      have hl : rankOf C B x b true q h.val ≤ n + 1 := h.property
      have hn : ¬ rankOf C B x b true q h.val ≤ n := hs
      omega
    obtain ⟨v, hv⟩ := evalON_covers_rank C B x b q a w hw (n + 1) h.val hr
    refine ⟨(familyON_degreeEquiv C B x b a w (n + 1) q).symm v.val, ?_⟩
    change evalON C B x b q a w (n + 1)
      ((familyON_degreeEquiv C B x b a w (n + 1) q)
        ((familyON_degreeEquiv C B x b a w (n + 1) q).symm v.val)) = h.val
    rw [Equiv.apply_symm_apply]
    exact hv

theorem evaluationNO_covers_successor (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (h : (newOldStage C B x b (n + 1) z d).toSSet.obj q) :
    h.val ∈ (newOldStage C B x b n z d).obj q ∨
      ∃ v : (familyNO C B x b z d (n + 1)).obj q,
        (evaluationNO C B x b z d (n + 1)).app q v = h.val := by
  classical
  by_cases hs : h.val ∈ (newOldStage C B x b n z d).obj q
  · exact Or.inl hs
  · right
    have hr : rankOf C B x b true q h.val = n + 1 := by
      have hl : rankOf C B x b true q h.val ≤ n + 1 := h.property
      have hn : ¬ rankOf C B x b true q h.val ≤ n := hs
      omega
    obtain ⟨v, hv⟩ := evalNO_covers_rank C B x b q z d hz (n + 1) h.val hr
    refine ⟨(familyNO_degreeEquiv C B x b z d (n + 1) q).symm v.val, ?_⟩
    change evalNO C B x b q z d (n + 1)
      ((familyNO_degreeEquiv C B x b z d (n + 1) q)
        ((familyNO_degreeEquiv C B x b z d (n + 1) q).symm v.val)) = h.val
    rw [Equiv.apply_symm_apply]
    exact hv

theorem evaluationNN_covers_successor (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (h : (newNewStage C B x b (n + 1) z w).toSSet.obj q) :
    h.val ∈ (newNewStage C B x b n z w).obj q ∨
      ∃ v : (familyNN C B x b z w (n + 1)).obj q,
        (evaluationNN C B x b z w (n + 1)).app q v = h.val := by
  classical
  by_cases hs : h.val ∈ (newNewStage C B x b n z w).obj q
  · exact Or.inl hs
  · right
    have hr : rankOf C B x b true q h.val = n + 1 := by
      have hl : rankOf C B x b true q h.val ≤ n + 1 := h.property
      have hn : ¬ rankOf C B x b true q h.val ≤ n := hs
      omega
    obtain ⟨v, hv⟩ := evalNN_covers_rank C B x b q z w hz hw (n + 1) h.val hr
    refine ⟨(familyNN_degreeEquiv C B x b z w (n + 1) q).symm v.val, ?_⟩
    change evalNN C B x b q z w (n + 1)
      ((familyNN_degreeEquiv C B x b z w (n + 1) q)
        ((familyNN_degreeEquiv C B x b z w (n + 1) q).symm v.val)) = h.val
    rw [Equiv.apply_symm_apply]
    exact hv

end
end DaggerAmalgamSuccessor
