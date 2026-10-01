import DaggerModels.TwoObjectCellReductionChosen
import DaggerModels.SimplicialColimits

/-! Unconditional Part I `bg.lem.reduction`.
Both ordinary pushouts use the constructed semantic colimits. The dagger pushout uses the
proved dagger cocompleteness, and its ordinary preservation uses the actual cofree adjunction.
No monicity, nonempty edge space, or distinctness of the target endpoints is assumed. -/

open CategoryTheory Limits

universe u

namespace DaggerModels.TwoObjectCellReduction

noncomputable section

attribute [local instance] DaggerModels.simplicialCatHasColimits

variable {K L : SSet.{u}} {C : DaggerSimplicialCat.{u, u}}
  (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C)

/-- The chosen first attachment, with its existence premise discharged. -/
def ordinaryFirstAttachment : SimplicialCat.{u, u} := firstAttachment i a

/-- The two chosen successive attachments, with both existence premises discharged. -/
def ordinarySuccessiveAttachment : SimplicialCat.{u, u} := successiveAttachment i a

def ordinaryOriginalInclusion : C.toSimplicialCat ⟶ ordinarySuccessiveAttachment i a :=
  firstOriginalInclusion i a ≫ secondOriginalInclusion i a

def ordinaryForwardInclusion : OrdinaryTwoObjectCell.cell L ⟶
    ordinarySuccessiveAttachment i a :=
  firstCellInclusion i a ≫ secondOriginalInclusion i a

def ordinaryReverseInclusion : OrdinaryTwoObjectCell.cell L ⟶
    ordinarySuccessiveAttachment i a := secondCellInclusion i a

/-- The original dagger cell attachment and the two successive ordinary ones are isomorphic. -/
def reductionIso : (daggerAttachment i a).toSimplicialCat ≅ ordinarySuccessiveAttachment i a :=
  chosenComparisonIso i a

@[reassoc (attr := simp)]
theorem reductionIso_original :
    DaggerSimplicialCat.forget.map (daggerOriginalInclusion i a) ≫ (reductionIso i a).hom =
      ordinaryOriginalInclusion i a :=
  chosenComparisonIso_original i a

@[reassoc (attr := simp)]
theorem reductionIso_forward : (TwoObjectCellPushout.inl L ≫
    DaggerSimplicialCat.forget.map (daggerCellInclusion i a)) ≫ (reductionIso i a).hom =
      ordinaryForwardInclusion i a :=
  chosenComparisonIso_forward i a

@[reassoc (attr := simp)]
theorem reductionIso_reverse : (TwoObjectCellPushout.inr L ≫
    DaggerSimplicialCat.forget.map (daggerCellInclusion i a)) ≫ (reductionIso i a).hom =
      ordinaryReverseInclusion i a :=
  chosenComparisonIso_reverse i a

/-- The literal two-stage UP, including the prescribed `u` and `u†` attaching maps. -/
theorem exists_reduction (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    ∃ (Q R : SimplicialCat.{u, u})
      (b₀ : OrdinaryTwoObjectCell.cell L ⟶ Q) (c₀ : C.toSimplicialCat ⟶ Q)
      (b₁ : OrdinaryTwoObjectCell.cell L ⟶ R) (c₁ : Q ⟶ R)
      (e : (daggerAttachment i (attaching x y f)).toSimplicialCat ≅ R),
      IsPushout (ordinaryMap i) (OrdinaryTwoObjectCell.fromData K C.toSimplicialCat x y f)
        b₀ c₀ ∧
      IsPushout (ordinaryMap i)
        (OrdinaryTwoObjectCell.fromData K C.toSimplicialCat y x
          (f ≫ DaggerSimplicialStructure.dagger x y) ≫ c₀) b₁ c₁ ∧
      DaggerSimplicialCat.forget.map (daggerOriginalInclusion i (attaching x y f)) ≫
        e.hom = c₀ ≫ c₁ ∧
      (TwoObjectCellPushout.inl L ≫
        DaggerSimplicialCat.forget.map (daggerCellInclusion i (attaching x y f))) ≫
        e.hom = b₀ ≫ c₁ ∧
      (TwoObjectCellPushout.inr L ≫
        DaggerSimplicialCat.forget.map (daggerCellInclusion i (attaching x y f))) ≫
        e.hom = b₁ := by
  let a := attaching x y f
  refine ⟨firstAttachment i a, successiveAttachment i a,
    firstCellInclusion i a, firstOriginalInclusion i a,
    secondCellInclusion i a, secondOriginalInclusion i a,
    chosenComparisonIso i a, ?_, ?_, chosenComparisonIso_original i a,
    chosenComparisonIso_forward i a, chosenComparisonIso_reverse i a⟩
  · simpa only [a, forwardAttaching_data] using firstAttachment_isPushout i a
  · simpa only [a, reverseAttaching_data] using secondAttachment_isPushout i a

end
end DaggerModels.TwoObjectCellReduction
