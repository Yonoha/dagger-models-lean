import NativeSmallHomNerveLift

/-! A weak comparison on the full original nerves, with both hom universes preserved. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
open DaggerNativeCommaSecondCostructuredArrowRetractSmallOperators
open DaggerNativeSmallHomNerveLift
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCommaSecondNerveComparison
noncomputable section

variable {A B E : Type u} [Category.{0} A] [Category.{u} B] [Category.{u} E]
variable (F : A ⥤ E) (J : B ⥤ E) (q : B)

def liftedToFibre : Source F J q ⥤ ULiftHom.{u} (Fibre F J q) :=
  toFibre F J q ⋙ ULiftHom.up.{0, u, u}

def liftedFromFibre : ULiftHom.{u} (Fibre F J q) ⥤ Source F J q :=
  ULiftHom.down.{0, u, u} ⋙ fromFibre F J q

def liftedSourceUnit : 𝟭 (Source F J q) ⟶ liftedToFibre F J q ⋙ liftedFromFibre F J q :=
  sourceUnit F J q

def liftedFibreRoundtrip : liftedFromFibre F J q ⋙ liftedToFibre F J q ≅
    𝟭 (ULiftHom.{u} (Fibre F J q)) :=
  NatIso.ofComponents (fun P ↦ (ULiftHom.up.{0, u, u} (C := Fibre F J q)).mapIso
    ((fibreRoundtrip F J q).app (ULiftHom.down.{0, u, u}.obj P))) (by
    intro P Q f
    apply ULift.ext
    apply CostructuredArrow.hom_ext
    change f.down.left ≫ 𝟙 _ = 𝟙 _ ≫ f.down.left
    simp)

/-- The only universe lift is the explicit nerve isomorphism, without mathematical premises. -/
theorem liftedToFibre_GW : GW (nerveMap (liftedToFibre F J q)) :=
  nerveMap_geometricW (liftedToFibre F J q) (liftedFromFibre F J q)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨liftedSourceUnit F J q⟩))
    (Relation.EqvGen.rel _ _ ⟨(liftedFibreRoundtrip F J q).hom⟩)

/-- This is the literal chain map of the original functor, into its original small-hom fibre. -/
theorem toFibre_GW : GW (mixedMap (toFibre F J q)) := by
  have : IsIso (upMap (Fibre F J q)) := (iso (Fibre F J q)).isIso_hom
  have : WeakEquivalence (nerveMap (liftedToFibre F J q)) :=
    (weakEquivalence_iff_GW _).mpr (liftedToFibre_GW F J q)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_postcomp_iff _ (upMap (Fibre F J q))).mp
  rw [mixedMap_up]
  change WeakEquivalence (nerveMap (liftedToFibre F J q))
  infer_instance

/-- Contractibility of the actual small-hom fibre transfers to the actual second-projection comma. -/
theorem source_point_GW (h : GW (pointMap (nerve (Fibre F J q)))) :
    GW (pointMap (nerve (Source F J q))) := by
  have : WeakEquivalence (mixedMap (toFibre F J q)) :=
    (weakEquivalence_iff_GW _).mpr (toFibre_GW F J q)
  have : WeakEquivalence (pointMap (nerve (Fibre F J q))) :=
    (weakEquivalence_iff_GW _).mpr h
  have he : mixedMap (toFibre F J q) ≫ pointMap (nerve (Fibre F J q)) =
      pointMap (nerve (Source F J q)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerNativeCommaSecondNerveComparison
