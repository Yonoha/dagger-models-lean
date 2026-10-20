import NativeJoyalMappingCoproduct
import NativeJoyalMappingWeakProperties
import OriginalFreeAntiSimplicialHomotopyEquivalence

/-!
# Every original free anti-involutive map preserves mapping weakness

Compare the entire concrete two-copy simplicial set with the native coproduct,
then transport through the existing natural isomorphism to the literal freeAnti.
No homotopy-equivalence witness or model-structure input is required.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite DaggerModels
open DaggerModels.OriginalAntiInvolutiveFreePair
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerActualFreeAntiJoyalMappingWeak
noncomputable section

def second (A : SSet.{u}) : A.op ⟶ pairSSet A where
  app _ x := (x, true)
  naturality _ _ _ := by funext x; rfl

def pairToCoprod (A : SSet.{u}) : pairSSet A ⟶ A ⨿ A.op where
  app n p := if p.2 then (coprod.inr : A.op ⟶ A ⨿ A.op).app n p.1
    else (coprod.inl : A ⟶ A ⨿ A.op).app n p.1
  naturality n m i := by
    funext p
    rcases p with ⟨x, b⟩
    cases b
    · exact congrFun ((coprod.inl : A ⟶ A ⨿ A.op).naturality i) x
    · exact congrFun ((coprod.inr : A.op ⟶ A ⨿ A.op).naturality i) x

def coproductPairIso (A : SSet.{u}) : A ⨿ A.op ≅ pairSSet A where
  hom := coprod.desc (first A) (second A)
  inv := pairToCoprod A
  hom_inv_id := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc]
      apply NatTrans.ext
      funext n x
      rfl
    · simp only [coprod.inr_desc_assoc]
      apply NatTrans.ext
      funext n x
      rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n p
    rcases p with ⟨x, b⟩
    cases b
    · exact congrFun (NatTrans.congr_app (coprod.inl_desc (first A) (second A)) n) x
    · exact congrFun (NatTrans.congr_app (coprod.inr_desc (first A) (second A)) n) x

theorem coproductPairIso_natural {A B : SSet.{u}} (f : A ⟶ B) :
    coprod.map f (SSet.opFunctor.map f) ≫ (coproductPairIso B).hom =
      (coproductPairIso A).hom ≫ (pairMap f).hom := by
  apply coprod.hom_ext
  · simp only [coproductPairIso, coprod.inl_map_assoc, coprod.inl_desc,
      coprod.inl_desc_assoc]
    apply NatTrans.ext
    funext n x
    rfl
  · simp only [coproductPairIso, coprod.inr_map_assoc, coprod.inr_desc,
      coprod.inr_desc_assoc]
    apply NatTrans.ext
    funext n x
    rfl

/-- Transport exactly the fixed weak predicate across the supplied strict iso square. -/
theorem weak_iso_square_iff {X Y X' Y' : SSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (h : f ≫ eY.hom = eX.hom ≫ g) :
    weakCategoricalEquivalences f ↔ weakCategoricalEquivalences g := by
  let e : Arrow.mk f ≅ Arrow.mk g := Arrow.isoMk eX eY h.symm
  constructor
  · exact fun hf ↦ weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm) hf
  · exact fun hg ↦ weakCategoricalEquivalences.of_retract (Retract.ofIso e) hg

theorem pair_map_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) : weakCategoricalEquivalences (pairMap f).hom :=
  (weak_iso_square_iff (coprod.map f (SSet.opFunctor.map f)) (pairMap f).hom
    (coproductPairIso A) (coproductPairIso B) (coproductPairIso_natural f)).1
      (DaggerNativeJoyalMappingCoproduct.weak_coprod_op_map f hf)

/-- The full literal freeAnti underlying map is weak for every original mapping-weak map. -/
theorem freeAnti_map_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) :
    weakCategoricalEquivalences (freeAnti.map f).hom := by
  exact (weak_iso_square_iff (pairMap f).hom (freeAnti.map f).hom
    (DaggerOriginalFreeAntiSimplicialHomotopyEquivalence.underlyingPairIso A)
    (DaggerOriginalFreeAntiSimplicialHomotopyEquivalence.underlyingPairIso B)
    (congrArg AntiInvolutiveSSet.Hom.hom (pairIsoFreeAnti.hom.naturality f))).1
      (pair_map_weak f hf)

/-- The actual free-forgetful composite preserves both inputs used in the DCH transfer. -/
theorem freeAnti_map_normal_and_weak {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : weakCategoricalEquivalences f) :
    AntiInvolutiveSSet.NormalMono (freeAnti.map f) ∧
      weakCategoricalEquivalences (freeAnti.map f).hom :=
  ⟨DaggerModels.OriginalAntiInvolutiveFreePairMono.freeAnti_map_normal f,
    freeAnti_map_weak f hf⟩

end
end DaggerActualFreeAntiJoyalMappingWeak
