import NativeOppositeLeftMappingSimplex

/-! The exact original opposite-left/right-simplex comparison is bijective in every degree. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerNativeVertexJoinReversal DaggerNativeRightConeSimplexPresentation
open DaggerActualQuasicategoryMappingFibres
universe u
namespace DaggerNativeOppositeLeftMappingSimplex
noncomputable section
variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

theorem forward_injective (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((forward X a b).app q) := by
  intro s t he
  have hh : raw X a b q s = raw X a b q t :=
    SSet.yonedaEquiv.symm.injective (congrArg Subtype.val he)
  have hmap : IsIso (X.map (joinIso q.unop).inv.op) := by infer_instance
  have hi := ((isIso_iff_bijective _).mp hmap).1 hh
  apply SSet.opObjEquiv.injective
  apply Subtype.ext
  apply Subtype.ext
  apply SSet.opObjEquiv.injective
  exact hi

def unraw (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    X.obj (op ((ordinalJoinLeft ⦋0⦌).obj q.unop)) :=
  X.map (joinIso q.unop).hom.op (SSet.yonedaEquiv s.val)

theorem unraw_prefix (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q.unop)).op
      (unraw X a b q s) = b := by
  have h := congrArg SSet.yonedaEquiv s.property.2
  simp only [lastVertex_eq_inr, SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_const] at h
  simp only [AugmentedSimplexCategory.tensorObjOf, SimplexCategory.len_mk, Nat.add_zero] at h
  calc
    _ = X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q.unop) ≫
        (joinIso q.unop).hom).op (SSet.yonedaEquiv s.val) :=
      (congrFun (X.map_comp _ _) _).symm
    _ = _ := by rw [reverse_prefix]; exact h

theorem unraw_suffix (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q.unop)).op
      (unraw X a b q s) = X.map (SimplexCategory.const q.unop ⦋0⦌ 0).op a := by
  have h := congrArg SSet.yonedaEquiv s.property.1
  simp only [face_eq_inl, SSet.yonedaEquiv_map_comp, yoneda_const] at h
  simp only [AugmentedSimplexCategory.tensorObjOf, SimplexCategory.len_mk, Nat.add_zero] at h
  calc
    _ = X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q.unop) ≫
        (joinIso q.unop).hom).op (SSet.yonedaEquiv s.val) :=
      (congrFun (X.map_comp _ _) _).symm
    _ = _ := by rw [reverse_suffix]; exact h

theorem forward_surjective (q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((forward X a b).app q) := by
  intro s
  let t : (simplexCoslice ⦋0⦌ X.op (SSet.opObjEquiv.symm b)).obj q :=
    ⟨SSet.opObjEquiv.symm (unraw X a b q s), unraw_prefix X a b q s⟩
  have ht : t ∈ (SSet.Subcomplex.fiber
      (cosliceProjection ⦋0⦌ X.op (SSet.opObjEquiv.symm b))
      (SSet.opObjEquiv.symm a)).obj q := by
    change (cosliceProjection ⦋0⦌ X.op (SSet.opObjEquiv.symm b)).app q t ∈
      (SSet.Subcomplex.ofSimplex (SSet.opObjEquiv.symm a)).obj q
    rw [SSet.Subcomplex.mem_ofSimplex_obj_iff]
    refine ⟨SimplexCategory.const q.unop ⦋0⦌ 0, ?_⟩
    change X.map (SimplexCategory.rev.map (SimplexCategory.const q.unop ⦋0⦌ 0)).op a =
      X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q.unop)).op
        (unraw X a b q s)
    rw [reverse_const]
    exact (unraw_suffix X a b q s).symm
  let v : (oppositeLeft X a b).obj q := SSet.opObjEquiv.symm ⟨t, ht⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm (raw X a b q v)) = SSet.yonedaEquiv s.val
  rw [Equiv.apply_symm_apply]
  change X.map (joinIso q.unop).inv.op
      (X.map (joinIso q.unop).hom.op (SSet.yonedaEquiv s.val)) = SSet.yonedaEquiv s.val
  exact congrFun (X.mapIso (joinIso q.unop).op).hom_inv_id _

theorem forward_isIso : IsIso (forward X a b) :=
  (NatTrans.isIso_iff_isIso_app _).mpr (fun q ↦
    (isIso_iff_bijective _).mpr ⟨forward_injective X a b q, forward_surjective X a b q⟩)

def comparisonIso : oppositeLeft X a b ≅ simplexSpace X a b := by
  have := forward_isIso X a b
  exact asIso (forward X a b)

end
end DaggerNativeOppositeLeftMappingSimplex
