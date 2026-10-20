import NativeConnectedFamilyHom
import NativePiZeroProductEquivalence
import NativeConnectedHornsAndSimplex

/-! Internal Hom from a nonempty preconnected parameter preserves the entire old family. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite MonoidalCategory MonoidalClosed
open DaggerOriginalProductGadget DaggerNativeConnectedFamilyHom
open DaggerNativePiZeroProductEquivalence DaggerNativeStandardSimplexContraction
universe u
namespace DaggerNativeConnectedIhomFamily
noncomputable section

instance tensor_components_subsingleton (K L : SSet.{u})
    [Subsingleton K.π₀] [Subsingleton L.π₀] : Subsingleton ((K ⊗ L).π₀) :=
  ⟨fun a b ↦ (productComponentsEquiv K L).injective
    (Subsingleton.elim (productComponentsEquiv K L a) (productComponentsEquiv K L b))⟩

def ihomDegreeEquiv (K X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((ihom K).obj X).obj n ≃ (K ⊗ SSet.stdSimplex.obj n.unop ⟶ X) where
  toFun s := uncurry (SSet.yonedaEquiv.symm s)
  invFun f := SSet.yonedaEquiv (curry f)
  left_inv s := by
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm s))) = s
    rw [curry_uncurry, Equiv.apply_symm_apply]
  right_inv f := by
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry f))) = f
    rw [Equiv.symm_apply_apply, uncurry_curry]

theorem ihomDegreeEquiv_natural (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (s : ((ihom K).obj X).obj n) :
    ihomDegreeEquiv K Y n (((ihom K).map f).app n s) = ihomDegreeEquiv K X n s ≫ f := by
  change uncurry (SSet.yonedaEquiv.symm (((ihom K).map f).app n s)) =
    uncurry (SSet.yonedaEquiv.symm s) ≫ f
  rw [← SSet.yonedaEquiv_symm_comp, uncurry_natural_right]

def familyIhomMap {I : Type u} (K : SSet.{u}) (X : I → SSet.{u}) :
    familySSet (fun i ↦ (ihom K).obj (X i)) ⟶ (ihom K).obj (familySSet X) where
  app n a := ((ihom K).map (familyInclusion X a.1)).app n a.2
  naturality n m α := by
    funext a
    exact congrFun (((ihom K).map (familyInclusion X a.1)).naturality α) a.2

theorem familyIhomMap_app_bijective {I : Type u} (K : SSet.{u})
    [Subsingleton K.π₀] (v : K _⦋0⦌) (X : I → SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((familyIhomMap K X).app n) := by
  let L := SSet.stdSimplex.obj n.unop
  letI : Subsingleton L.π₀ := by
    change Subsingleton ((Δ[n.unop.len] : SSet.{u}).π₀)
    infer_instance
  let w : L _⦋0⦌ := firstVertex n.unop.len
  have hb := familyHomMap_bijective X (K := K ⊗ L) (v, w)
  constructor
  · rintro ⟨i, s⟩ ⟨j, t⟩ h
    have he := congrArg (ihomDegreeEquiv K (familySSet X) n) h
    change ihomDegreeEquiv K (familySSet X) n (((ihom K).map (familyInclusion X i)).app n s)
      = ihomDegreeEquiv K (familySSet X) n
        (((ihom K).map (familyInclusion X j)).app n t) at he
    rw [ihomDegreeEquiv_natural, ihomDegreeEquiv_natural] at he
    have hs : (⟨i, ihomDegreeEquiv K (X i) n s⟩ : Σ i, K ⊗ L ⟶ X i) =
        ⟨j, ihomDegreeEquiv K (X j) n t⟩ := hb.1 he
    have hij := (Sigma.mk.inj hs).1
    cases hij
    have hst : s = t := (ihomDegreeEquiv K (X i) n).injective
      (eq_of_heq (Sigma.mk.inj hs).2)
    cases hst
    rfl
  · intro f
    obtain ⟨⟨i, g⟩, hg⟩ := hb.2 (ihomDegreeEquiv K (familySSet X) n f)
    refine ⟨⟨i, (ihomDegreeEquiv K (X i) n).symm g⟩,
      (ihomDegreeEquiv K (familySSet X) n).injective ?_⟩
    change ihomDegreeEquiv K (familySSet X) n
      (((ihom K).map (familyInclusion X i)).app n
        ((ihomDegreeEquiv K (X i) n).symm g)) = _
    rw [ihomDegreeEquiv_natural, Equiv.apply_symm_apply]
    exact hg

theorem familyIhomMap_isIso {I : Type u} (K : SSet.{u})
    [Subsingleton K.π₀] (v : K _⦋0⦌) (X : I → SSet.{u}) :
    IsIso (familyIhomMap K X) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro n
  exact (isIso_iff_bijective _).mpr (familyIhomMap_app_bijective K v X n)

def familyIhomIso {I : Type u} (K : SSet.{u})
    [Subsingleton K.π₀] (v : K _⦋0⦌) (X : I → SSet.{u}) :
    familySSet (fun i ↦ (ihom K).obj (X i)) ≅ (ihom K).obj (familySSet X) := by
  letI := familyIhomMap_isIso K v X
  exact asIso (familyIhomMap K X)

end
end DaggerNativeConnectedIhomFamily
