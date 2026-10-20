import NativeIhomHoObjects
import NativeIhomQuasicategories

/-!
# The unchanged mapping weak test yields full inverse data between quasi-categories

The literal target test at A supplies a whole original map g and an isomorphism
in native ho of ihom A A. The literal test at B lifts the postcomposed isomorphism
by full faithfulness. Both endomorphism categories and the actual f are retained.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeWalkingRetractionMappingEquivalence DaggerNativeIhomHoObjects
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeJoyalWeakQuasiInverse
noncomputable section

structure InverseData {A B : SSet.{u}} (f : A ⟶ B) where
  inv : B ⟶ A
  leftIso : homObject (f ≫ inv) ≅ homObject (𝟙 A)
  rightIso : homObject (inv ≫ f) ≅ homObject (𝟙 B)

def fromWeak {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory] (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) : InverseData f := by
  let FA := preHoFunctor f A
  haveI : FA.IsEquivalence := hf A
  let x := FA.objPreimage (homObject (𝟙 A))
  let g := (homObjectEquiv B A).symm x
  have hg : homObject g = x := (homObjectEquiv B A).apply_symm_apply x
  let eA : homObject (f ≫ g) ≅ homObject (𝟙 A) :=
    (eqToIso (pre_obj f g)).symm ≪≫ eqToIso (congrArg FA.obj hg) ≪≫
      FA.objObjPreimageIso (homObject (𝟙 A))
  let FB := preHoFunctor f B
  haveI : FB.IsEquivalence := hf B
  let eFB : FB.obj (homObject (g ≫ f)) ≅ FB.obj (homObject (𝟙 B)) := by
    change (preHoFunctor f B).obj (homObject (g ≫ f)) ≅
      (preHoFunctor f B).obj (homObject (𝟙 B))
    rw [pre_obj, pre_obj, Category.comp_id]
    exact eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.assoc f g f).symm) ≪≫
      (eqToIso (post_obj (f ≫ g) f)).symm ≪≫ (postHoFunctor A f).mapIso eA ≪≫
      eqToIso (post_obj (𝟙 A) f) ≪≫
      eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.id_comp f))
  exact ⟨g, eA, FB.preimageIso eFB⟩

theorem exists_inverse_data {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) (hf : weakCategoricalEquivalences f) : Nonempty (InverseData f) :=
  ⟨fromWeak f hf⟩

end
end DaggerNativeJoyalWeakQuasiInverse
