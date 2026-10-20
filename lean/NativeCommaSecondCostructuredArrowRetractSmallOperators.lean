import ActualIteratedConeFibreComparison

/-! The second projection's costructured comma retracts onto the literal original fibre.
The simplex operators remain in their original small hom universe. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCommaSecondCostructuredArrowRetractSmallOperators
noncomputable section

variable {A B E : Type u} [Category.{0} A] [Category.{u} B] [Category.{u} E]
variable (F : A ⥤ E) (J : B ⥤ E) (q : B)
abbrev Source := CostructuredArrow (Comma.snd F J) q
abbrev Fibre := CostructuredArrow F (J.obj q)

/-- Compose the entire original comma arrow with the image of its target arrow. -/
def toFibre : Source F J q ⥤ Fibre F J q where
  obj P := CostructuredArrow.mk (Y := P.left.left) (P.left.hom ≫ J.map P.hom)
  map {P Q} f := CostructuredArrow.homMk f.left.left (by
    change F.map f.left.left ≫ (Q.left.hom ≫ J.map Q.hom) = P.left.hom ≫ J.map P.hom
    rw [← Category.assoc, f.left.w, Category.assoc, ← J.map_comp]
    exact congrArg (fun z ↦ P.left.hom ≫ J.map z) (CostructuredArrow.w f))
  map_id _ := by apply CostructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply CostructuredArrow.hom_ext; rfl

/-- Insert the same original fibre arrow at the identity of q. -/
def fromFibre : Fibre F J q ⥤ Source F J q where
  obj P := CostructuredArrow.mk (Y := (⟨P.left, q, P.hom⟩ : Comma F J)) (𝟙 q)
  map {P Q} f := CostructuredArrow.homMk
    (⟨f.left, 𝟙 q, by
      exact (CostructuredArrow.w f).trans
        ((congrArg (fun z ↦ P.hom ≫ z) (J.map_id q)).trans
          (Category.comp_id P.hom)).symm⟩ :
        (⟨P.left, q, P.hom⟩ : Comma F J) ⟶ ⟨Q.left, q, Q.hom⟩)
    (by change (𝟙 q) ≫ 𝟙 q = 𝟙 q; exact Category.id_comp _)
  map_id _ := by apply CostructuredArrow.hom_ext; apply Comma.hom_ext <;> simp
  map_comp _ _ := by apply CostructuredArrow.hom_ext; apply Comma.hom_ext <;> simp

/-- Every original target arrow supplies the natural homotopy retraction. -/
def sourceUnit : 𝟭 (Source F J q) ⟶ toFibre F J q ⋙ fromFibre F J q where
  app P := CostructuredArrow.homMk
    (⟨𝟙 P.left.left, P.hom, by
      exact (congrArg (fun z ↦ z ≫ (P.left.hom ≫ J.map P.hom))
        (F.map_id P.left.left)).trans (Category.id_comp _)⟩ :
        P.left ⟶ ((fromFibre F J q).obj ((toFibre F J q).obj P)).left)
    (Category.comp_id P.hom)
  naturality {P Q} f := by
    apply CostructuredArrow.hom_ext
    apply Comma.hom_ext
    · change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
      simp
    · change f.left.right ≫ Q.hom = P.hom ≫ 𝟙 q
      exact (CostructuredArrow.w f).trans (Category.comp_id P.hom).symm

/-- The original fibre roundtrip keeps its entire arrow. -/
def fibreRoundtrip : fromFibre F J q ⋙ toFibre F J q ≅ 𝟭 (Fibre F J q) :=
  NatIso.ofComponents (fun P ↦ CostructuredArrow.isoMk (Iso.refl P.left) (by
    change F.map (𝟙 P.left) ≫ P.hom = P.hom ≫ J.map (𝟙 q)
    exact ((congrArg (fun z ↦ z ≫ P.hom) (F.map_id P.left)).trans
      (Category.id_comp P.hom)).trans
        ((congrArg (fun z ↦ P.hom ≫ z) (J.map_id q)).trans
          (Category.comp_id P.hom)).symm)) (by
    intro P Q f
    apply CostructuredArrow.hom_ext
    change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
    simp)

end
end DaggerNativeCommaSecondCostructuredArrowRetractSmallOperators
