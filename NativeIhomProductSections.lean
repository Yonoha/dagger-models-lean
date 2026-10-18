import NativeIhomRelativeSectionsWeak

/-! The exact fibre over the identity parameter is the original internal Hom. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open HomotopicalAlgebra Simplicial
open DaggerNativeIhomRelativeSectionsWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeIhomProductSections
noncomputable section

def identityPoint (K : SSet.{u}) : 𝟙_ SSet.{u} ⟶ (ihom K).obj K := curry (fst K _)

theorem product_terminal_isPullback (K X : SSet.{u}) :
    IsPullback (snd K X) (fst K X) (toUnit X) (toUnit K) := by
  let c : PullbackCone (toUnit X) (toUnit K) :=
    PullbackCone.mk (snd K X) (fst K X) (isTerminalTensorUnit.hom_ext _ _)
  apply IsPullback.of_isLimit (c := c)
  refine PullbackCone.IsLimit.mk c.condition (fun s ↦ lift s.snd s.fst) ?_ ?_ ?_
  · intro s
    apply NatTrans.ext
    rfl
  · intro s
    apply NatTrans.ext
    rfl
  · intro s m hm hn
    apply NatTrans.ext
    funext q x
    exact Prod.ext (congrFun (NatTrans.congr_app hn q) x)
      (congrFun (NatTrans.congr_app hm q) x)

theorem ihom_product_isPullback (K X : SSet.{u}) :
    IsPullback ((ihom K).map (snd K X)) ((ihom K).map (fst K X))
      ((ihom K).map (toUnit X)) ((ihom K).map (toUnit K)) := by
  letI : PreservesLimitsOfSize.{0, 0} (ihom K) := (ihom.adjunction K).rightAdjoint_preservesLimits
  exact (product_terminal_isPullback K X).map (ihom K)

def graph (K X : SSet.{u}) : (ihom K).obj X ⟶ (ihom K).obj (K ⊗ X) :=
  (ihom_product_isPullback K X).lift (𝟙 _) (toUnit _ ≫ identityPoint K)
    ((IsTerminal.isTerminalObj (ihom K) _ isTerminalTensorUnit).hom_ext _ _)

theorem graph_snd (K X : SSet.{u}) :
    graph K X ≫ (ihom K).map (snd K X) = 𝟙 _ :=
  (ihom_product_isPullback K X).lift_fst _ _ _

theorem graph_fst (K X : SSet.{u}) :
    graph K X ≫ (ihom K).map (fst K X) = toUnit _ ≫ identityPoint K :=
  (ihom_product_isPullback K X).lift_snd _ _ _

theorem graph_isPullback (K X : SSet.{u}) :
    IsPullback (graph K X) (toUnit ((ihom K).obj X)) ((ihom K).map (fst K X))
      (identityPoint K) := by
  let c := PullbackCone.mk (graph K X) (toUnit _) (graph_fst K X)
  apply IsPullback.of_isLimit (c := c)
  refine PullbackCone.IsLimit.mk c.condition
    (fun s ↦ s.fst ≫ (ihom K).map (snd K X)) ?_ ?_ ?_
  · intro s
    change (s.fst ≫ (ihom K).map (snd K X)) ≫ graph K X = s.fst
    apply (ihom_product_isPullback K X).hom_ext
    · rw [Category.assoc, graph_snd, Category.comp_id]
    · rw [Category.assoc, graph_fst]
      have ht : (s.fst ≫ (ihom K).map (snd K X)) ≫ toUnit _ = s.snd :=
        isTerminalTensorUnit.hom_ext _ _
      calc
        _ = s.snd ≫ identityPoint K := by rw [← Category.assoc, ht]
        _ = _ := s.condition.symm
  · intro s
    exact isTerminalTensorUnit.hom_ext _ _
  · intro s m hm hn
    dsimp only [c] at m hm hn ⊢
    change m = s.fst ≫ (ihom K).map (snd K X)
    change m ≫ graph K X = s.fst at hm
    rw [← hm, Category.assoc, graph_snd]
    exact (Category.comp_id m).symm

def productSectionIso (K X : SSet.{u}) :
    (ihom K).obj X ≅ pullback ((ihom K).map (fst K X)) (identityPoint K) :=
  (graph_isPullback K X).isoPullback

end
end DaggerNativeIhomProductSections
