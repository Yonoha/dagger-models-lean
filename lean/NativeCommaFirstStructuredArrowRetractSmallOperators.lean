import ProofActualIteratedFibrantStructuredArrows

/-! The structured-arrow comma of the first projection retracts to its actual fibre. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCommaFirstStructuredArrowRetractSmallOperators
noncomputable section

variable {A B E : Type u} [Category.{0} A] [Category.{u} B] [Category.{u} E]
variable (F : A ⥤ E) (J : B ⥤ E) (c : A)
abbrev Source := StructuredArrow c (Comma.fst F J)
abbrev Fibre := StructuredArrow (F.obj c) J

/-- Compose the entire original source arrow with the actual comma arrow. -/
def toFibre : Source F J c ⥤ Fibre F J c where
  obj P := StructuredArrow.mk (Y := P.right.right) (F.map P.hom ≫ P.right.hom)
  map {P Q} f := StructuredArrow.homMk f.right.right (by
    change (F.map P.hom ≫ P.right.hom) ≫ J.map f.right.right = F.map Q.hom ≫ Q.right.hom
    rw [Category.assoc, ← f.right.w, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun z ↦ F.map z ≫ Q.right.hom) (StructuredArrow.w f))
  map_id _ := by apply StructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply StructuredArrow.hom_ext; rfl

/-- Insert the same fibre arrow at the identity source c. -/
def fromFibre : Fibre F J c ⥤ Source F J c where
  obj P := StructuredArrow.mk (Y := (⟨c, P.right, P.hom⟩ : Comma F J)) (𝟙 c)
  map {P Q} f := StructuredArrow.homMk
    (⟨𝟙 c, f.right, by
      exact (congrArg (fun z ↦ z ≫ Q.hom) (F.map_id c)).trans
        ((Category.id_comp Q.hom).trans (StructuredArrow.w f).symm)⟩ :
        (⟨c, P.right, P.hom⟩ : Comma F J) ⟶ ⟨c, Q.right, Q.hom⟩)
    (by change (𝟙 c) ≫ 𝟙 c = 𝟙 c; exact Category.id_comp _)
  map_id _ := by apply StructuredArrow.hom_ext; apply Comma.hom_ext <;> simp
  map_comp _ _ := by apply StructuredArrow.hom_ext; apply Comma.hom_ext <;> simp

/-- The actual source arrow gives the homotopy retraction back to every original comma object. -/
def sourceUnit : toFibre F J c ⋙ fromFibre F J c ⟶ 𝟭 (Source F J c) where
  app P := StructuredArrow.homMk
    (⟨P.hom, 𝟙 P.right.right, by
      change F.map P.hom ≫ P.right.hom = (F.map P.hom ≫ P.right.hom) ≫ J.map (𝟙 _)
      exact ((congrArg (fun z ↦ (F.map P.hom ≫ P.right.hom) ≫ z)
        (J.map_id P.right.right)).trans (Category.comp_id _)).symm⟩ :
        ((fromFibre F J c).obj ((toFibre F J c).obj P)).right ⟶ P.right)
    (Category.id_comp P.hom)
  naturality {P Q} f := by
    apply StructuredArrow.hom_ext
    apply Comma.hom_ext
    · change (𝟙 c) ≫ Q.hom = P.hom ≫ f.right.left
      rw [Category.id_comp]
      exact (StructuredArrow.w f).symm
    · change f.right.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right.right
      simp

/-- The fibre roundtrip is the identity on the whole original arrow up to its canonical isomorphism. -/
def fibreRoundtrip : fromFibre F J c ⋙ toFibre F J c ≅ 𝟭 (Fibre F J c) :=
  NatIso.ofComponents (fun P ↦ StructuredArrow.isoMk (Iso.refl P.right) (by
    change (F.map (𝟙 c) ≫ P.hom) ≫ J.map (𝟙 _) = P.hom
    calc
      _ = (𝟙 (F.obj c) ≫ P.hom) ≫ J.map (𝟙 _) :=
        congrArg (fun z ↦ (z ≫ P.hom) ≫ J.map (𝟙 _)) (F.map_id c)
      _ = P.hom ≫ J.map (𝟙 _) := congrArg (fun z ↦ z ≫ J.map (𝟙 _))
        (Category.id_comp P.hom)
      _ = P.hom ≫ 𝟙 _ := congrArg (fun z ↦ P.hom ≫ z) (J.map_id P.right)
      _ = P.hom := Category.comp_id _)) (by
    intro P Q f
    apply StructuredArrow.hom_ext
    change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right
    simp)

/-- This literal fibre comparison is weak on nerves, without a finality assumption. -/
theorem toFibre_GW : GW (nerveMap (toFibre F J c)) :=
  nerveMap_geometricW (toFibre F J c) (fromFibre F J c)
    (Relation.EqvGen.rel _ _ ⟨sourceUnit F J c⟩)
    (Relation.EqvGen.rel _ _ ⟨(fibreRoundtrip F J c).hom⟩)

/-- Weak contractibility of the actual fibre implies that of the full structured-arrow comma. -/
theorem source_point_GW (h : GW (pointMap (nerve (Fibre F J c)))) :
    GW (pointMap (nerve (Source F J c))) := by
  have : WeakEquivalence (nerveMap (toFibre F J c)) := (weakEquivalence_iff_GW _).mpr
    (toFibre_GW F J c)
  have : WeakEquivalence (pointMap (nerve (Fibre F J c))) :=
    (weakEquivalence_iff_GW _).mpr h
  have he : nerveMap (toFibre F J c) ≫ pointMap (nerve (Fibre F J c)) =
      pointMap (nerve (Source F J c)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerNativeCommaFirstStructuredArrowRetractSmallOperators
