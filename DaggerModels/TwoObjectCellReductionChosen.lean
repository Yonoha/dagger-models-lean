import DaggerModels.TwoObjectCellReduction

/-! Chosen-object form of the two successive ordinary attachments.
The two local ordinary pushout-existence instances are explicit intermediate hypotheses;
this file alone does not discharge ordinary pushout existence. The dagger pushout exists
by the actual cocompleteness theorem. -/

open CategoryTheory Limits

universe u

namespace DaggerModels.TwoObjectCellReduction

noncomputable section

variable {K L : SSet.{u}} {C : DaggerSimplicialCat.{u, u}}
  (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C)
  [HasPushout (ordinaryMap i) (forwardAttaching a)]

/-- Attach the forward ordinary copy. -/
def firstAttachment : SimplicialCat.{u, u} :=
  pushout (ordinaryMap i) (forwardAttaching a)

def firstCellInclusion : OrdinaryTwoObjectCell.cell L ⟶ firstAttachment i a :=
  pushout.inl (ordinaryMap i) (forwardAttaching a)

def firstOriginalInclusion : C.toSimplicialCat ⟶ firstAttachment i a :=
  pushout.inr (ordinaryMap i) (forwardAttaching a)

/-- Attach the reverse edge after mapping the original category into the first pushout. -/
def secondAttaching : OrdinaryTwoObjectCell.cell K ⟶ firstAttachment i a :=
  reverseAttaching a ≫ firstOriginalInclusion i a

/-- The complete first ordinary pushout UP. -/
theorem firstAttachment_isPushout : IsPushout (ordinaryMap i) (forwardAttaching a)
    (firstCellInclusion i a) (firstOriginalInclusion i a) :=
  IsPushout.of_hasPushout _ _

variable [HasPushout (ordinaryMap i) (secondAttaching i a)]

/-- The actual successive ordinary pushout object, with the order used in the manuscript. -/
def successiveAttachment : SimplicialCat.{u, u} :=
  pushout (ordinaryMap i) (secondAttaching i a)

def secondCellInclusion : OrdinaryTwoObjectCell.cell L ⟶ successiveAttachment i a :=
  pushout.inl (ordinaryMap i) (secondAttaching i a)

def secondOriginalInclusion : firstAttachment i a ⟶ successiveAttachment i a :=
  pushout.inr (ordinaryMap i) (secondAttaching i a)

/-- The complete second ordinary pushout UP. -/
theorem secondAttachment_isPushout : IsPushout (ordinaryMap i)
    (reverseAttaching a ≫ firstOriginalInclusion i a)
    (secondCellInclusion i a) (secondOriginalInclusion i a) := by
  change IsPushout (ordinaryMap i) (secondAttaching i a) _ _
  exact IsPushout.of_hasPushout _ _

/-- The canonical comparison of the actual chosen dagger and successive ordinary pushouts. -/
def chosenComparisonIso : (daggerAttachment i a).toSimplicialCat ≅ successiveAttachment i a :=
  comparisonIso a i (firstAttachment_isPushout i a) (secondAttachment_isPushout i a)
    (daggerAttachment_isPushout i a)

@[reassoc (attr := simp)]
theorem chosenComparisonIso_original :
    DaggerSimplicialCat.forget.map (daggerOriginalInclusion i a) ≫
      (chosenComparisonIso i a).hom =
        firstOriginalInclusion i a ≫ secondOriginalInclusion i a :=
  comparisonIso_original _ _ _ _ _

@[reassoc (attr := simp)]
theorem chosenComparisonIso_forward :
    (TwoObjectCellPushout.inl L ≫
      DaggerSimplicialCat.forget.map (daggerCellInclusion i a)) ≫
      (chosenComparisonIso i a).hom =
        firstCellInclusion i a ≫ secondOriginalInclusion i a :=
  comparisonIso_forward _ _ _ _ _

@[reassoc (attr := simp)]
theorem chosenComparisonIso_reverse :
    (TwoObjectCellPushout.inr L ≫
      DaggerSimplicialCat.forget.map (daggerCellInclusion i a)) ≫
      (chosenComparisonIso i a).hom = secondCellInclusion i a :=
  comparisonIso_reverse _ _ _ _ _

end
end DaggerModels.TwoObjectCellReduction
