import ActualIteratedFibrantInclusion

/-! A unit into a full subcategory contracts every structured-arrow category into it. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
open DaggerOriginalFlagFlankification
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePositiveStructuredArrowContraction
noncomputable section

variable {E : Type u} [Category.{u} E] (P : ObjectProperty E)
variable (G : E ⥤ E) (η : 𝟭 E ⟶ G) (hG : ∀ x, P (G.obj x)) (O : E)

abbrev All := StructuredArrow O (𝟭 E)
abbrev Selected := StructuredArrow O P.ι

/-- Forget only the full-subcategory property, keeping the entire arrow from O. -/
def inclusion : Selected P O ⥤ All O where
  obj A := StructuredArrow.mk (Y := A.right.obj) A.hom
  map f := StructuredArrow.homMk f.right.hom (StructuredArrow.w f)
  map_id _ := by apply StructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply StructuredArrow.hom_ext; rfl

/-- Extend the target by the unit; the source O and the entire original arrow are retained. -/
def extend : All O ⥤ Selected P O where
  obj A := StructuredArrow.mk (Y := (⟨G.obj A.right, hG A.right⟩ : P.FullSubcategory))
    (A.hom ≫ η.app A.right)
  map {A B} f := StructuredArrow.homMk (ObjectProperty.homMk (G.map f.right)) (by
    change (A.hom ≫ η.app A.right) ≫ G.map f.right = B.hom ≫ η.app B.right
    rw [Category.assoc, ← η.naturality, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ η.app B.right) (StructuredArrow.w f))
  map_id _ := by apply StructuredArrow.hom_ext; apply ObjectProperty.hom_ext; exact G.map_id _
  map_comp _ _ := by
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact G.map_comp _ _

/-- Both composites retain the original source arrow through the same unit. -/
def allUnit : 𝟭 (All O) ⟶ extend P G η hG O ⋙ inclusion P O where
  app A := StructuredArrow.homMk (η.app A.right) rfl
  naturality {A B} f := by apply StructuredArrow.hom_ext; exact η.naturality f.right

def selectedUnit : 𝟭 (Selected P O) ⟶ inclusion P O ⋙ extend P G η hG O where
  app A := StructuredArrow.homMk (ObjectProperty.homMk (η.app A.right.obj)) rfl
  naturality {A B} f := by
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact η.naturality f.right.hom

include G η hG in
/-- The actual structured-arrow inclusion is weak, with no finality premise supplied. -/
theorem inclusion_GW : GW (nerveMap (inclusion P O)) :=
  nerveMap_geometricW (inclusion P O) (extend P G η hG O)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨selectedUnit P G η hG O⟩))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨allUnit P G η hG O⟩))

/-- The identity arrow from O is the actual initial object of the unrestricted category. -/
def initial : All O := StructuredArrow.mk (𝟙 O)

def collapse : All O ⥤ Discrete PUnit.{u + 1} :=
  (Functor.const _).obj (Discrete.mk PUnit.unit)

def center : Discrete PUnit.{u + 1} ⥤ All O := (Functor.const _).obj (initial O)

def centerToId : collapse O ⋙ center O ⟶ 𝟭 (All O) where
  app A := StructuredArrow.homMk A.hom (Category.id_comp _)
  naturality {A B} f := by
    apply StructuredArrow.hom_ext
    change (𝟙 O) ≫ B.hom = A.hom ≫ f.right
    rw [Category.id_comp]
    exact (StructuredArrow.w f).symm

def collapseToId : center O ⋙ collapse O ⟶ 𝟭 (Discrete PUnit.{u + 1}) where
  app _ := eqToHom (Subsingleton.elim _ _)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Initiality gives weak contractibility of the whole unrestricted arrow category. -/
theorem all_point_GW : GW (pointMap (nerve (All O))) := by
  have : WeakEquivalence (nerveMap (collapse O)) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW (collapse O) (center O)
      (Relation.EqvGen.rel _ _ ⟨centerToId O⟩)
      (Relation.EqvGen.rel _ _ ⟨collapseToId O⟩))
  have he : nerveMap (collapse O) ≫ (nerveDiscreteIso PUnit).hom =
      pointMap (nerve (All O)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

include G η hG in
/-- Every actual structured-arrow category into the selected full subcategory is contractible. -/
theorem selected_point_GW : GW (pointMap (nerve (Selected P O))) := by
  have : WeakEquivalence (nerveMap (inclusion P O)) :=
    (weakEquivalence_iff_GW _).mpr (inclusion_GW P G η hG O)
  have : WeakEquivalence (pointMap (nerve (All O))) :=
    (weakEquivalence_iff_GW _).mpr (all_point_GW O)
  have he : nerveMap (inclusion P O) ≫ pointMap (nerve (All O)) =
      pointMap (nerve (Selected P O)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerNativePositiveStructuredArrowContraction
