import ActualNecklaceConeGadgetComparison

/-! Connect the common gadget category to the actual original rigidification Hom.
Both legs of this explicit P2 span are proved weak without a supplied comparison premise. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy DaggerBisimplicialDiagonal
open DaggerOriginalFlagFlankification DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualNecklaceConeP2Span
noncomputable section
open DaggerActualNecklaceConeGadgets

def toOriginalHom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    diag (originalB X a b) ⟶ (RV X a ⟶[SSet.{u}] RV X b) :=
  originalEpsilon X a b ≫ (flagOriginalHomIso X a b).hom

def toGadgets (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    diag (originalB X a b) ⟶ nerve (Over X a b) :=
  originalPi X a b ≫ nerveMap (inclusion X a b)

theorem toOriginalHom_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (toOriginalHom X a b) := by
  have : WeakEquivalence (originalEpsilon X a b) :=
    (weakEquivalence_iff_GW _).2 (originalP2_both_GW X a b).1
  exact (weakEquivalence_iff_GW _).1
    (show WeakEquivalence (originalEpsilon X a b ≫ (flagOriginalHomIso X a b).hom)
      from inferInstance)

theorem toGadgets_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (toGadgets X a b) := by
  have : WeakEquivalence (originalPi X a b) :=
    (weakEquivalence_iff_GW _).2 (originalP2_both_GW X a b).2
  have : WeakEquivalence (nerveMap (inclusion X a b)) :=
    (weakEquivalence_iff_GW _).2
      (DaggerActualNecklaceConeGadgetComparison.inclusion_GW X a b)
  exact (weakEquivalence_iff_GW _).1
    (show WeakEquivalence (originalPi X a b ≫ nerveMap (inclusion X a b))
      from inferInstance)

theorem both_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (toOriginalHom X a b) ∧ GW (toGadgets X a b) :=
  ⟨toOriginalHom_GW X a b, toGadgets_GW X a b⟩

theorem inclusion_postcomp_nerve {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (f : X ⟶ Y) :
    nerveMap (NecklacesOver.postcomp (a := a) (b := b) f) ≫
        nerveMap (inclusion Y (f.app _ a) (f.app _ b)) =
      nerveMap (inclusion X a b) ≫ nerveMap (Over.postcomp f) := rfl

theorem toGadgets_postcomp {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    originalDMap f a b ≫ toGadgets Y (f.app _ a) (f.app _ b) =
      toGadgets X a b ≫ nerveMap (Over.postcomp f) := by
  unfold toGadgets
  rw [← Category.assoc, originalPi_postcomp, Category.assoc,
    inclusion_postcomp_nerve, ← Category.assoc]

end
end DaggerActualNecklaceConeP2Span
