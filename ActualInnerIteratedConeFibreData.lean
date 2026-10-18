import ActualInnerIteratedRightConeIndex

/-! The actual cone-index comma fibre keeps every whole cone map into a positive-level gadget. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualInnerIteratedGadgetData DaggerActualInnerIteratedRightConeIndex
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u
namespace DaggerActualInnerIteratedConeFibreData
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
variable (P : BaseCode) (k : ℕ) (σ : spaceAt.{u} P (k + 1) ⟶ X)
variable (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
variable (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b)

def targetOver : Over X a b := ⟨⟨P, k + 1⟩, σ, ha, hb⟩

abbrev MappingSpace := DaggerActualGeneralRightConeMapping.rightMapping
  (spaceAt.{u} P (k + 1)) (alphaAt P (k + 1)) (omegaAt P (k + 1))

abbrev MappingIndex := SimplexIndex (MappingSpace.{u} P k)
abbrev Fibre := CostructuredArrow (index X a b) (targetOver X a b P k σ ha hb)

/-- Restrict only the target to the actual native inner positive gadget,
retaining the full original map. -/
def toMappingIndex : Fibre X a b P k σ ha hb ⥤ MappingIndex P k where
  obj A := CostructuredArrow.mk (uliftYonedaEquiv.symm
    (⟨A.hom.hom.map, A.hom.hom.first, A.hom.hom.last⟩ :
      (MappingSpace P k).obj (op A.left.left)))
  map {A B} f := CostructuredArrow.homMk f.left.left (by
    apply uliftYonedaEquiv.injective
    have h := congrArg
      (fun z : (index X a b).obj A.left ⟶ targetOver X a b P k σ ha hb ↦ z.hom.map)
      (CostructuredArrow.w f)
    have ht : (MappingSpace P k).map f.left.left.op
        (⟨B.hom.hom.map, B.hom.hom.first, B.hom.hom.last⟩ :
          (MappingSpace P k).obj (op B.left.left)) =
        (⟨A.hom.hom.map, A.hom.hom.first, A.hom.hom.last⟩ :
          (MappingSpace P k).obj (op A.left.left)) := Subtype.ext h
    have hn := uliftYonedaEquiv_naturality (F := MappingSpace P k)
      ((uliftYonedaEquiv.symm
        (⟨B.hom.hom.map, B.hom.hom.first, B.hom.hom.last⟩ :
          (MappingSpace P k).obj (op B.left.left))) :
        uliftYoneda.obj B.left.left ⟶ MappingSpace P k) f.left.left.op
    have hc := (uliftYonedaEquiv (F := MappingSpace P k) (X := B.left.left)).apply_symm_apply
      (⟨B.hom.hom.map, B.hom.hom.first, B.hom.hom.last⟩ :
        (MappingSpace P k).obj (op B.left.left))
    rw [hc] at hn
    have hcA := (uliftYonedaEquiv (F := MappingSpace P k) (X := A.left.left)).apply_symm_apply
      (⟨A.hom.hom.map, A.hom.hom.first, A.hom.hom.last⟩ :
        (MappingSpace P k).obj (op A.left.left))
    simpa only [Quiver.Hom.unop_op] using (hn.symm.trans ht).trans hcA.symm)
  map_id _ := by apply CostructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply CostructuredArrow.hom_ext; rfl

/-- A mapping simplex composes with the entire target map to give its original cone-index object. -/
def overSimplexObj (A : MappingIndex P k) :
    SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b) :=
  CostructuredArrow.mk (uliftYonedaEquiv.symm
    (⟨(uliftYonedaEquiv A.hom).val ≫ σ, by
      constructor
      · change σ.app _ ((uliftYonedaEquiv A.hom).val.app _ (alpha A.left.len)) = a
        rw [(uliftYonedaEquiv A.hom).property.1, ha]
      · change σ.app _ ((uliftYonedaEquiv A.hom).val.app _ (omega A.left.len)) = b
        rw [(uliftYonedaEquiv A.hom).property.2, hb]⟩ :
      (DaggerActualGeneralRightConeMapping.rightMapping X a b).obj (op A.left)))

theorem overSimplexObj_val (A : MappingIndex P k) :
    (uliftYonedaEquiv (overSimplexObj X a b P k σ ha hb A).hom).val =
      (uliftYonedaEquiv A.hom).val ≫ σ :=
  congrArg Subtype.val
    ((uliftYonedaEquiv (F := DaggerActualGeneralRightConeMapping.rightMapping X a b)
      (X := A.left)).apply_symm_apply _)

def overSimplex : MappingIndex P k ⥤
    SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b) where
  obj := overSimplexObj X a b P k σ ha hb
  map {A B} f := CostructuredArrow.homMk f.left (by
    apply uliftYonedaEquiv.injective
    have hs : (MappingSpace P k).map f.left.op (uliftYonedaEquiv B.hom) =
        uliftYonedaEquiv A.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := MappingSpace P k) B.hom f.left.op)
    have hn := uliftYonedaEquiv_naturality
      (F := DaggerActualGeneralRightConeMapping.rightMapping X a b)
      (overSimplexObj X a b P k σ ha hb B).hom f.left.op
    simp only [Quiver.Hom.unop_op] at hn
    refine hn.symm.trans ?_
    apply Subtype.ext
    change coneMap f.left ≫
        (uliftYonedaEquiv (overSimplexObj X a b P k σ ha hb B).hom).val =
      (uliftYonedaEquiv (overSimplexObj X a b P k σ ha hb A).hom).val
    rw [overSimplexObj_val, overSimplexObj_val, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ σ) (congrArg Subtype.val hs))
  map_id _ := by apply CostructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply CostructuredArrow.hom_ext; rfl

/-- Recover the full comma arrow, with its literal triangle over the original X. -/
def fromMappingIndex : MappingIndex P k ⥤ Fibre X a b P k σ ha hb where
  obj A := CostructuredArrow.mk
    (Y := overSimplexObj X a b P k σ ha hb A)
    (⟨⟨(uliftYonedaEquiv A.hom).val, (uliftYonedaEquiv A.hom).property.1,
      (uliftYonedaEquiv A.hom).property.2⟩, by
      change (uliftYonedaEquiv A.hom).val ≫ σ =
        (uliftYonedaEquiv (overSimplexObj X a b P k σ ha hb A).hom).val
      exact (congrArg Subtype.val
        ((uliftYonedaEquiv (F := DaggerActualGeneralRightConeMapping.rightMapping X a b)
          (X := A.left)).apply_symm_apply
          (⟨(uliftYonedaEquiv A.hom).val ≫ σ, by
            constructor
            · change σ.app _ ((uliftYonedaEquiv A.hom).val.app _ (alpha A.left.len)) = a
              rw [(uliftYonedaEquiv A.hom).property.1, ha]
            · change σ.app _ ((uliftYonedaEquiv A.hom).val.app _ (omega A.left.len)) = b
              rw [(uliftYonedaEquiv A.hom).property.2, hb]⟩ :
            (DaggerActualGeneralRightConeMapping.rightMapping X a b).obj (op A.left)))).symm⟩ :
      (index X a b).obj (overSimplexObj X a b P k σ ha hb A) ⟶
        targetOver X a b P k σ ha hb)
  map {A B} f := CostructuredArrow.homMk ((overSimplex X a b P k σ ha hb).map f) (by
    apply Over.Hom.ext
    apply Hom.ext
    have hs : (MappingSpace P k).map f.left.op (uliftYonedaEquiv B.hom) =
        uliftYonedaEquiv A.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := MappingSpace P k) B.hom f.left.op)
    exact congrArg Subtype.val hs)
  map_id _ := by apply CostructuredArrow.hom_ext; exact (overSimplex X a b P k σ ha hb).map_id _
  map_comp _ _ := by
    apply CostructuredArrow.hom_ext
    exact (overSimplex X a b P k σ ha hb).map_comp _ _

end
end DaggerActualInnerIteratedConeFibreData
