import NativeJoyalWeakInverseRecognition

/-!
# Two covariant native internal-Hom tests give a whole inverse

Retain both exact postcomposition functors, the original map, and native ho.
This does not assume a model structure or a quasi-category source or target.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeIhomHoObjects DaggerNativeJoyalWeakQuasiInverse
open DaggerNativeWalkingRetractionMappingEquivalence
open DaggerNativeJoyalWeakInverseRecognition DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeHoCovariantInverseRecognition
noncomputable section

def fromPostEquivalences {A B : SSet.{u}} (f : A ⟶ B)
    (hA : (postHoFunctor A f).IsEquivalence)
    (hB : (postHoFunctor B f).IsEquivalence) : InverseData f := by
  let FA := postHoFunctor A f
  let FB := postHoFunctor B f
  have : FA.IsEquivalence := hA
  have : FB.IsEquivalence := hB
  let x := FB.objPreimage (homObject (𝟙 B))
  let g := (homObjectEquiv B A).symm x
  have hg : homObject g = x := (homObjectEquiv B A).apply_symm_apply x
  let eB : homObject (g ≫ f) ≅ homObject (𝟙 B) :=
    (eqToIso (post_obj g f)).symm ≪≫ eqToIso (congrArg FB.obj hg) ≪≫
      FB.objObjPreimageIso (homObject (𝟙 B))
  let eFA : FA.obj (homObject (f ≫ g)) ≅ FA.obj (homObject (𝟙 A)) := by
    change (postHoFunctor A f).obj (homObject (f ≫ g)) ≅
      (postHoFunctor A f).obj (homObject (𝟙 A))
    rw [post_obj, post_obj, Category.id_comp]
    exact eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.assoc f g f)) ≪≫
      (eqToIso (pre_obj f (g ≫ f))).symm ≪≫ (preHoFunctor f B).mapIso eB ≪≫
      eqToIso (pre_obj f (𝟙 B)) ≪≫
      eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.comp_id f))
  exact ⟨g, FA.preimageIso eFA, eB⟩

theorem weak_of_post_equivalences {A B : SSet.{u}} (f : A ⟶ B)
    (hA : (postHoFunctor A f).IsEquivalence)
    (hB : (postHoFunctor B f).IsEquivalence) : weakCategoricalEquivalences f :=
  inverse_data_weak f (fromPostEquivalences f hA hB)

end
end DaggerNativeHoCovariantInverseRecognition
