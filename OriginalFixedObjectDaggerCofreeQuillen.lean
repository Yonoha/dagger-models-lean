import OriginalFixedObjectStrictModel
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual original dagger forget/cofree Quillen adjunction

Both original fixed-object model structures have been constructed unconditionally.
Binary product base change preserves the exact ordinary fibrations, and the original
counit carries this result to cofree daggers. Native adjunction lifting gives precisely
the original canonical cofibrations. This comparison is not a Quillen equivalence.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
open DaggerOriginalFixedObjectDaggerCofreeTransfer
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictModel DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalFixedObjectDaggerCofreeQuillen
noncomputable section

/-- Forgetting only the dagger preserves and detects the full original fibration class. -/
theorem forget_fibration_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    Fibration F ↔ Fibration ((fixedStrictDaggerForget O).map F) := by
  rw [strictDagger_fibration_iff, strict_fibration_iff]
  rfl

/-- The original native binary product preserves the exact ordinary fibration class. -/
theorem strict_prodMap_fibration {O : Type u} {A B C D : FixedStrictGroupoids O}
    (F : A ⟶ B) (G : C ⟶ D) (hF : Fibration F) (hG : Fibration G) :
    Fibration (prod.map F G) := by
  let P := fibrations (FixedStrictGroupoids O)
  have h₁ : P (prod.map F (𝟙 C)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id F C) ((fibration_iff F).1 hF)
  have hs : P (prod.map G (𝟙 B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id G B) ((fibration_iff G).1 hG)
  have h₂ : P (prod.map (𝟙 B) G) := by
    have h := P.comp_mem _ _
      (P.comp_mem _ _ (P.of_isIso (prod.braiding B C).hom) hs)
      (P.of_isIso (prod.braiding D B).hom)
    convert h using 1
    apply prod.hom_ext <;> simp
  apply (fibration_iff _).2
  have h := P.comp_mem _ _ h₁ h₂
  convert h using 1
  apply prod.hom_ext <;> simp

/-- The full original cofree dagger functor preserves the original Homwise fibrations. -/
theorem daggerCofree_fibration {O : Type u} {C D : FixedStrictGroupoids O}
    (F : C ⟶ D) (hF : Fibration F) : Fibration ((daggerCofree O).map F) := by
  apply (forget_fibration_iff _).2
  apply (fibration_iff _).2
  let E := fixedDaggerActionEquivalence O
  let V := Action.forget (FixedStrictGroupoids O) C2.{u}
  let R := DaggerOriginalC2BinaryCofreeAdjunction.cofreeFunctor (FixedStrictGroupoids O)
  let eC := V.mapIso (E.counitIso.app (R.obj C))
  let eD := V.mapIso (E.counitIso.app (R.obj D))
  have hc := congrArg (fun k ↦ V.map k) (E.counitIso.hom.naturality (R.map F))
  change (fixedStrictDaggerForget O).map ((daggerCofree O).map F) ≫ eD.hom =
    eC.hom ≫ prod.map F F at hc
  exact ((fibrations (FixedStrictGroupoids O)).arrow_mk_iso_iff
    (Arrow.isoMk eC eD hc.symm)).2 ((fibration_iff _).1 (strict_prodMap_fibration F F hF hF))

/-- The actual original dagger forget/cofree adjunction is native Quillen. -/
theorem daggerForgetCofree_isQuillen (O : Type u) :
    (daggerForgetCofreeAdjunction O).IsQuillenAdjunction where
  cofibration_map i := by
    intro hi
    exact (cofibration_iff _).2 (forget_cofibration i ((cofibration_iff i).1 hi))
  fibration_map p := daggerCofree_fibration p inferInstance

end
end DaggerOriginalFixedObjectDaggerCofreeQuillen
