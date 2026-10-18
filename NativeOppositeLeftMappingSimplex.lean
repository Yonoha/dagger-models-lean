import NativeVertexJoinReversalNaturality
import NativeRightConeSimplexPresentation
import ActualMappingCoreVertexCharacterization

/-! Original left mapping simplices in the opposite have the original right constant face. -/
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

def oppositeLeft : SSet.{u} :=
  (leftMapping X.op (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a)).op

def rawLeft (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    X.obj (op ((ordinalJoinLeft ⦋0⦌).obj q.unop)) :=
  SSet.opObjEquiv (SSet.opObjEquiv s).val.val

def raw (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    X.obj (op ⦋q.unop.len + 1⦌) := X.map (joinIso q.unop).inv.op (rawLeft X a b q s)

theorem prefix_inv (q : SimplexCategory) :
    AugmentedSimplexCategory.inl' q ⦋0⦌ ≫ (joinIso q).inv =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q) := by
  apply (cancel_mono (joinIso q).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, reverse_suffix]

theorem suffix_inv (q : SimplexCategory) :
    AugmentedSimplexCategory.inr' q ⦋0⦌ ≫ (joinIso q).inv =
      SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q) := by
  apply (cancel_mono (joinIso q).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, reverse_prefix]

theorem reverse_const (q : SimplexCategory) :
    SimplexCategory.rev.map (SimplexCategory.const q ⦋0⦌ 0) =
      SimplexCategory.const q ⦋0⦌ 0 := by
  ext i : 3
  apply Fin.ext
  have h1 := ((SimplexCategory.rev.map (SimplexCategory.const q ⦋0⦌ 0)).toOrderHom i).isLt
  have h2 := ((SimplexCategory.const q ⦋0⦌ 0).toOrderHom i).isLt
  simp only [SimplexCategory.rev_obj, SimplexCategory.len_mk] at h1 h2
  omega

theorem raw_prefix (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    X.map (AugmentedSimplexCategory.inl' q.unop ⦋0⦌).op (raw X a b q s) =
      X.map (SimplexCategory.const q.unop ⦋0⦌ 0).op a := by
  have h := DaggerActualMappingCoreVertexCharacterization.suffix_eq_const X.op
    (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a) q (SSet.opObjEquiv s)
  simp only [SSet.const_app] at h
  change X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inr' ⦋0⦌ q.unop)).op
      (rawLeft X a b q s) =
    X.map (SimplexCategory.rev.map (SimplexCategory.const q.unop ⦋0⦌ 0)).op a at h
  rw [reverse_const] at h
  calc
    _ = X.map (AugmentedSimplexCategory.inl' q.unop ⦋0⦌ ≫ (joinIso q.unop).inv).op
        (rawLeft X a b q s) := (congrFun (X.map_comp _ _) _).symm
    _ = _ := by rw [prefix_inv]; exact h

theorem raw_suffix (q : SimplexCategoryᵒᵖ) (s : (oppositeLeft X a b).obj q) :
    X.map (AugmentedSimplexCategory.inr' q.unop ⦋0⦌).op (raw X a b q s) = b := by
  have h : X.map (SimplexCategory.rev.map (AugmentedSimplexCategory.inl' ⦋0⦌ q.unop)).op
      (rawLeft X a b q s) = b := (SSet.opObjEquiv s).val.property
  calc
    _ = X.map (AugmentedSimplexCategory.inr' q.unop ⦋0⦌ ≫ (joinIso q.unop).inv).op
        (rawLeft X a b q s) := (congrFun (X.map_comp _ _) _).symm
    _ = _ := by rw [suffix_inv]; exact h

theorem join_inv_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    (joinIso m).inv ≫
        SimplexCategory.rev.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α)) =
      joinHom α ≫ (joinIso n).inv := by
  apply (cancel_mono (joinIso n).hom).mp
  rw [Category.assoc, join_naturality, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem raw_naturality {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (oppositeLeft X a b).obj q) :
    raw X a b r ((oppositeLeft X a b).map α s) =
      X.map (joinHom α.unop).op (raw X a b q s) := by
  change X.map (joinIso r.unop).inv.op
      (X.map (SimplexCategory.rev.map
        ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α.unop))).op
        (rawLeft X a b q s)) = _
  calc
    _ = X.map ((joinIso r.unop).inv ≫ SimplexCategory.rev.map
          ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.rev.map α.unop))).op
        (rawLeft X a b q s) := (congrFun (X.map_comp _ _) _).symm
    _ = X.map (joinHom α.unop ≫ (joinIso q.unop).inv).op
        (rawLeft X a b q s) := by rw [join_inv_naturality]
    _ = _ := congrFun (X.map_comp _ _) _

theorem yoneda_const (q : SimplexCategory) (v : X.obj (op ⦋0⦌)) :
    SSet.yonedaEquiv (SSet.const v : SSet.stdSimplex.obj q ⟶ X) =
      X.map (SimplexCategory.const q ⦋0⦌ 0).op v := by
  have hc : SSet.stdSimplex.map (SimplexCategory.const q ⦋0⦌ 0) ≫
      SSet.yonedaEquiv.symm v = (SSet.const v : SSet.stdSimplex.obj q ⟶ X) := by
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  rw [← hc, SSet.yonedaEquiv_map_comp, Equiv.apply_symm_apply]

def forward : oppositeLeft X a b ⟶ simplexSpace X a b where
  app q s := ⟨SSet.yonedaEquiv.symm (raw X a b q s), by
    constructor
    · apply SSet.yonedaEquiv.injective
      rw [face_eq_inl, SSet.yonedaEquiv_map_comp]
      simp only [AugmentedSimplexCategory.tensorObjOf, SimplexCategory.len_mk,
        Nat.add_zero, Equiv.apply_symm_apply]
      rw [yoneda_const]
      exact raw_prefix X a b q s
    · apply SSet.yonedaEquiv.injective
      rw [lastVertex_eq_inr, SSet.yonedaEquiv_map_comp]
      simp only [AugmentedSimplexCategory.tensorObjOf, SimplexCategory.len_mk,
        Nat.add_zero, Equiv.apply_symm_apply]
      rw [SSet.yonedaEquiv_const]
      exact raw_suffix X a b q s⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    apply SSet.yonedaEquiv.injective
    change SSet.yonedaEquiv
        (SSet.yonedaEquiv.symm (raw X a b r ((oppositeLeft X a b).map α s))) =
      SSet.yonedaEquiv (joinMap α.unop ≫ SSet.yonedaEquiv.symm (raw X a b q s))
    rw [Equiv.apply_symm_apply, joinMap, SSet.yonedaEquiv_map_comp]
    simp only [Equiv.apply_symm_apply]
    exact raw_naturality X a b α s

end
end DaggerNativeOppositeLeftMappingSimplex
