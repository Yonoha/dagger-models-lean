import ActualIteratedConeFibreData

/-! Identify the actual costructured-arrow fibre with the full actual right-cone simplex index. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData DaggerActualIteratedRightConeIndex
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualIteratedConeFibreData
universe u
namespace DaggerActualIteratedConeFibreEquivalence
noncomputable section

variable (D : SimplicialCat.{u, u}) (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
variable (P : BaseCode) (k : ℕ) (σ : spaceAt.{u} P (k + 1) ⟶ coherentNerve.obj D)
variable (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
variable (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b)

theorem toMapping_obj_map (A : Fibre D a b P k σ ha hb) :
    (uliftYonedaEquiv ((toMappingIndex D a b P k σ ha hb).obj A).hom).val =
      A.hom.hom.map :=
  congrArg Subtype.val
    ((uliftYonedaEquiv (F := MappingSpace P k) (X := A.left.left)).apply_symm_apply _)

theorem overSimplex_obj_map (A : MappingIndex P k) :
    (uliftYonedaEquiv (overSimplexObj D a b P k σ ha hb A).hom).val =
      (uliftYonedaEquiv A.hom).val ≫ σ :=
  congrArg Subtype.val
    ((uliftYonedaEquiv (F := rightConeSimplices D a b) (X := A.left)).apply_symm_apply _)

/-- The roundtrip keeps both the original degree and the entire mapping simplex. -/
def mappingRoundtrip : fromMappingIndex D a b P k σ ha hb ⋙
    toMappingIndex D a b P k σ ha hb ≅ 𝟭 (MappingIndex P k) :=
  NatIso.ofComponents (fun A ↦ CostructuredArrow.isoMk (Iso.refl A.left) (by
    simp only [Iso.refl_hom]
    apply uliftYonedaEquiv.injective
    apply Subtype.ext
    exact (toMapping_obj_map D a b P k σ ha hb
      ((fromMappingIndex D a b P k σ ha hb).obj A)).symm)) (by
    intro A B f
    apply CostructuredArrow.hom_ext
    change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
    simp)

/-- The original cone-index object is recovered using its literal full triangle over N(D). -/
def fibreLeftRoundtripIso (A : Fibre D a b P k σ ha hb) :
    ((fromMappingIndex D a b P k σ ha hb).obj
      ((toMappingIndex D a b P k σ ha hb).obj A)).left ≅ A.left :=
  CostructuredArrow.isoMk (Iso.refl A.left.left) (by
    simp only [Iso.refl_hom]
    apply uliftYonedaEquiv.injective
    apply Subtype.ext
    change (uliftYonedaEquiv A.left.hom).val =
      (uliftYonedaEquiv
        (overSimplexObj D a b P k σ ha hb
          ((toMappingIndex D a b P k σ ha hb).obj A)).hom).val
    rw [overSimplex_obj_map, toMapping_obj_map]
    exact A.hom.w.symm)

/-- The roundtrip retains each full comma arrow and every original operator. -/
def fibreRoundtrip : toMappingIndex D a b P k σ ha hb ⋙
    fromMappingIndex D a b P k σ ha hb ≅ 𝟭 (Fibre D a b P k σ ha hb) :=
  NatIso.ofComponents (fun A ↦ CostructuredArrow.isoMk
    (fibreLeftRoundtripIso D a b P k σ ha hb A) (by
      apply Over.Hom.ext
      apply Hom.ext
      change coneMap (𝟙 A.left.left) ≫ A.hom.hom.map =
        (uliftYonedaEquiv ((toMappingIndex D a b P k σ ha hb).obj A).hom).val
      rw [show coneMap (𝟙 A.left.left) = 𝟙 (cone A.left.left.len) from
        coneFunctor.map_id A.left.left, Category.id_comp, toMapping_obj_map])) (by
    intro A B f
    apply CostructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
    simp)

/-- This is an actual equivalence, with no contractibility or cofinality premise supplied. -/
def equivalence : Fibre D a b P k σ ha hb ≌ MappingIndex P k :=
  CategoryTheory.Equivalence.mk (toMappingIndex D a b P k σ ha hb)
    (fromMappingIndex D a b P k σ ha hb) (fibreRoundtrip D a b P k σ ha hb).symm
    (mappingRoundtrip D a b P k σ ha hb)

end
end DaggerActualIteratedConeFibreEquivalence
