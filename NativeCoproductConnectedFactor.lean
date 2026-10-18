import NativePiZeroFamilyEquivalence
import NativeSSetCoproductSummandFibration

/-! Actual maps from a preconnected simplicial set stay in their specified native summand. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerOriginalProductGadget DaggerNativePiZeroFamilyEquivalence
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
universe u
namespace DaggerNativeCoproductConnectedFactor
noncomputable section

def coproductComponentsEquiv {I : Type u} (X : I → SSet.{u}) :
    (∐ X).π₀ ≃ Σ i, (X i).π₀ :=
  (SSet.π₀Functor.mapIso (familySigmaIso X)).toEquiv.trans (familyComponentsEquiv I X)

theorem coproductComponentsEquiv_mk {I : Type u} (X : I → SSet.{u}) (i : I)
    (a : (X i) _⦋0⦌) :
    coproductComponentsEquiv X (SSet.π₀.mk ((Sigma.ι X i).app (op ⦋0⦌) a)) =
      ⟨i, SSet.π₀.mk a⟩ := by
  change familyComponentsEquiv I X
    (SSet.mapπ₀ (familySigmaIso X).hom (SSet.π₀.mk ((Sigma.ι X i).app (op ⦋0⦌) a))) = _
  rw [SSet.mapπ₀_mk]
  have h := congrFun (NatTrans.congr_app (familySigmaIso_ι X i) (op ⦋0⦌)) a
  change (familySigmaIso X).hom.app (op ⦋0⦌) ((Sigma.ι X i).app (op ⦋0⦌) a) = ⟨i, a⟩ at h
  rw [h]
  exact familyComponentsEquiv_mk X i a

theorem connected_factor_fixed_summand {I : Type u} (X : I → SSet.{u}) (i : I)
    {Z : SSet.{u}} [Subsingleton Z.π₀] (f : Z ⟶ ∐ X)
    (z : Z _⦋0⦌) (a : (X i) _⦋0⦌)
    (hz : f.app (op ⦋0⦌) z = (Sigma.ι X i).app (op ⦋0⦌) a) :
    ∃ g : Z ⟶ X i, g ≫ Sigma.ι X i = f := by
  have he (d : SimplexCategoryᵒᵖ) (s : Z.obj d) :
      ∃ t : (X i).obj d, (Sigma.ι X i).app d t = f.app d s := by
    obtain ⟨⟨j, t⟩, ht⟩ := (coproductDegreeEquiv X d).surjective (f.app d s)
    let α := (⦋0⦌ : SimplexCategory).const d.unop 0
    have hc : SSet.π₀.mk (Z.map α.op s) = SSet.π₀.mk z := Subsingleton.elim _ _
    have hi : (coproductComponentsEquiv X
        (SSet.π₀.mk (f.app (op ⦋0⦌) (Z.map α.op s)))).1 = i := by
      change (coproductComponentsEquiv X (SSet.mapπ₀ f (SSet.π₀.mk (Z.map α.op s)))).1 = i
      rw [hc, SSet.mapπ₀_mk, hz, coproductComponentsEquiv_mk]
    have hn := congrFun (f.naturality α.op) s
    change f.app (op ⦋0⦌) (Z.map α.op s) = (∐ X).map α.op (f.app d s) at hn
    rw [← ht, coproductDegreeEquiv_map] at hn
    rw [hn] at hi
    change (coproductComponentsEquiv X
      (SSet.π₀.mk ((Sigma.ι X j).app (op ⦋0⦌) ((X j).map α.op t)))).1 = i at hi
    rw [coproductComponentsEquiv_mk] at hi
    cases hi
    exact ⟨t, ht⟩
  let g : Z ⟶ X i :=
    { app d s := (he d s).choose
      naturality d e α := by
        funext s
        apply (CategoryTheory.mono_iff_injective ((Sigma.ι X i).app e)).mp inferInstance
        change (Sigma.ι X i).app e ((he e (Z.map α s)).choose) =
          (Sigma.ι X i).app e ((X i).map α ((he d s).choose))
        have hn := congrFun ((Sigma.ι X i).naturality α) ((he d s).choose)
        change (Sigma.ι X i).app e ((X i).map α ((he d s).choose)) =
          (∐ X).map α ((Sigma.ι X i).app d ((he d s).choose)) at hn
        rw [(he e (Z.map α s)).choose_spec, hn, (he d s).choose_spec]
        exact congrFun (f.naturality α) s }
  refine ⟨g, ?_⟩
  apply NatTrans.ext
  funext d s
  exact (he d s).choose_spec

end
end DaggerNativeCoproductConnectedFactor
