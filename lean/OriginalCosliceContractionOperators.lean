import OriginalJoinedVertexCoreCriterion

/-!
# Operators for contracting the original vertex coslice

For a monotone map t : [n] → [1], the operator on [0] ⋆ [n] collapses the
initial segment on which t is zero to the original first vertex. These exact
native ordinal operators commute with every original simplex operator. Their
two constant endpoints are the constant first-vertex map and the identity.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedVertexCoreCriterion

namespace DaggerOriginalCosliceContractionOperators

/-- The native join map fixes the original first vertex. -/
theorem joined_map_zero {a b : SimplexCategory} (f : a ⟶ b) :
    ((ordinalJoinLeft ⦋0⦌).map f).toOrderHom 0 = 0 := by
  simp [ordinalJoinLeft, AugmentedSimplexCategory.tensorHomOf,
    SimplexCategory.eqToHom_toOrderHom]
  rfl

/-- The native join map sends a suffix vertex to the suffix of its original image. -/
theorem joined_map_rightVertex {a b : SimplexCategory} (f : a ⟶ b)
    (j : Fin (a.len + 1)) :
    ((ordinalJoinLeft ⦋0⦌).map f).toOrderHom (rightVertex a j) =
      rightVertex b (f.toOrderHom j) := by
  have hc : ((⦋0⦌ : SimplexCategory).const a j) ≫ f =
      (⦋0⦌ : SimplexCategory).const b (f.toOrderHom j) := by
    ext i
    fin_cases i
    rfl
  have h := (ordinalJoinLeft ⦋0⦌).map_comp ((⦋0⦌ : SimplexCategory).const a j) f
  rw [hc] at h
  have hv := congrArg (fun g ↦ g.toOrderHom (1 : Fin 2)) h
  change (((ordinalJoinLeft ⦋0⦌).map
      ((⦋0⦌ : SimplexCategory).const b (f.toOrderHom j))).toOrderHom 1) =
    ((ordinalJoinLeft ⦋0⦌).map f).toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map ((⦋0⦌ : SimplexCategory).const a j)).toOrderHom 1) at hv
  rw [joined_vertex_pairOperator, joined_vertex_pairOperator] at hv
  exact hv.symm

/-- Collapse precisely the original initial segment selected by the interval simplex. -/
def contractionOperator (n : SimplexCategory) (t : n ⟶ ⦋1⦌) :
    (ordinalJoinLeft ⦋0⦌).obj n ⟶ (ordinalJoinLeft ⦋0⦌).obj n :=
  SimplexCategory.Hom.mk
    { toFun := fun j ↦ if ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom j ≤ 1 then 0 else j
      monotone' := fun i j hij ↦ by
        by_cases hi : ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom i ≤ 1
        · simp only [hi, ↓reduceIte, Fin.zero_le]
        · have hj : ¬ ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom j ≤ 1 := by
            intro hj
            exact hi (((ordinalJoinLeft ⦋0⦌).map t).toOrderHom.monotone hij |>.trans hj)
          simp only [hi, hj, ↓reduceIte]
          exact hij }

/-- Every contraction operator fixes the actual prefix vertex. -/
theorem contractionOperator_zero (n : SimplexCategory) (t : n ⟶ ⦋1⦌) :
    (contractionOperator n t).toOrderHom 0 = 0 := by
  change (if ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom 0 ≤ 1 then 0 else 0) = 0
  simp

/-- The original fixed prefix is retained under the contraction. -/
theorem prefix_comp_contractionOperator (n : SimplexCategory) (t : n ⟶ ⦋1⦌) :
    AugmentedSimplexCategory.inl' ⦋0⦌ n ≫ contractionOperator n t =
      AugmentedSimplexCategory.inl' ⦋0⦌ n := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  fin_cases i
  have hi : (AugmentedSimplexCategory.inl' ⦋0⦌ n).toOrderHom 0 = 0 := by
    apply Fin.ext
    rw [AugmentedSimplexCategory.inl'_eval]
    rfl
  change (contractionOperator n t).toOrderHom
      ((AugmentedSimplexCategory.inl' ⦋0⦌ n).toOrderHom 0) =
    (AugmentedSimplexCategory.inl' ⦋0⦌ n).toOrderHom 0
  rw [hi]
  exact contractionOperator_zero n t

/-- The contraction commutes with every native joined simplex operator. -/
theorem contractionOperator_naturality {a b : SimplexCategory} (f : a ⟶ b)
    (t : b ⟶ ⦋1⦌) :
    (ordinalJoinLeft ⦋0⦌).map f ≫ contractionOperator b t =
      contractionOperator a (f ≫ t) ≫ (ordinalJoinLeft ⦋0⦌).map f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  have hc := congrArg (fun g ↦ g.toOrderHom j) ((ordinalJoinLeft ⦋0⦌).map_comp f t)
  change ((ordinalJoinLeft ⦋0⦌).map (f ≫ t)).toOrderHom j =
    ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map f).toOrderHom j) at hc
  change (if ((ordinalJoinLeft ⦋0⦌).map t).toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map f).toOrderHom j) ≤ 1 then 0
      else ((ordinalJoinLeft ⦋0⦌).map f).toOrderHom j) =
    ((ordinalJoinLeft ⦋0⦌).map f).toOrderHom
      (if ((ordinalJoinLeft ⦋0⦌).map (f ≫ t)).toOrderHom j ≤ 1 then 0 else j)
  rw [← hc]
  split_ifs <;> simp only [joined_map_zero]

/-- At the zero endpoint every joined vertex collapses to the actual first vertex. -/
theorem contractionOperator_const_zero (n : SimplexCategory) :
    contractionOperator n (n.const ⦋1⦌ 0) =
      ((ordinalJoinLeft ⦋0⦌).obj n).const ((ordinalJoinLeft ⦋0⦌).obj n) 0 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  change (if ((ordinalJoinLeft ⦋0⦌).map (n.const ⦋1⦌ 0)).toOrderHom j ≤ 1
    then 0 else j) = 0
  by_cases hj : j = 0
  · subst j
    simp
  · obtain ⟨k, rfl⟩ := exists_rightVertex n j hj
    have hc : ((ordinalJoinLeft ⦋0⦌).map (n.const ⦋1⦌ 0)).toOrderHom
        (rightVertex n k) = 1 := by
      rw [joined_map_rightVertex]
      rfl
    simp only [hc, le_refl, ↓reduceIte]

/-- At the one endpoint every original joined vertex is retained. -/
theorem contractionOperator_const_one (n : SimplexCategory) :
    contractionOperator n (n.const ⦋1⦌ 1) = 𝟙 ((ordinalJoinLeft ⦋0⦌).obj n) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  change (if ((ordinalJoinLeft ⦋0⦌).map (n.const ⦋1⦌ 1)).toOrderHom j ≤ 1
    then 0 else j) = j
  by_cases hj : j = 0
  · subst j
    simp
  · obtain ⟨k, rfl⟩ := exists_rightVertex n j hj
    have hc : ((ordinalJoinLeft ⦋0⦌).map (n.const ⦋1⦌ 1)).toOrderHom
        (rightVertex n k) = 2 := by
      rw [joined_map_rightVertex]
      rfl
    simp only [hc]
    have h : ¬ (2 : Fin 3) ≤ 1 := by decide
    rw [if_neg h]

end DaggerOriginalCosliceContractionOperators
