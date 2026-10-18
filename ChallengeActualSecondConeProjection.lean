import ActualIteratedRightConeIndex

/-! The actual second-projection comma and every entire original map are fixed. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerActualIteratedGadgetData
open DaggerActualIteratedRightConeIndex
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u
namespace DaggerActualSecondConeProjectionChallenge
noncomputable section

def geometric {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))

def chainMap {A B : Type u} [Category.{u} A] [Category.{0} B] (F : A ⥤ B) :
    nerve A ⟶ nerve B where
  app _ := (F.mapComposableArrows _).obj

def target (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) (P : BaseCode) (k : ℕ)
    (σ : spaceAt.{u} P (k + 1) ⟶ coherentNerve.obj D)
    (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
    (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b) :
    DaggerActualIteratedGadgetShift.FibrantOver D a b :=
  ⟨⟨⟨P, k + 1⟩, σ, ha, hb⟩, Nat.succ_pos k⟩

def mappingSpace (P : BaseCode) (k : ℕ) : SSet.{u} := rightConeSimplices
  (OriginalOrdinaryLocalKanReplacement.replacement.obj (rigidification.obj (spaceAt.{u} P k)))
  (alphaAt P (k + 1)) (omegaAt P (k + 1))

def statement : Prop :=
  (∀ (D : SimplicialCat.{u, u})
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) (P : BaseCode) (k : ℕ)
      (σ : spaceAt.{u} P (k + 1) ⟶ coherentNerve.obj D)
      (ha : σ.app (op ⦋0⦌) (alphaAt P (k + 1)) = a)
      (hb : σ.app (op ⦋0⦌) (omegaAt P (k + 1)) = b),
    ∃ G : CostructuredArrow (toPositive D a b) (target D a b P k σ ha hb) ⥤
        SimplexIndex (mappingSpace P k),
      (∀ A, (G.obj A).left = A.left.left.left) ∧
      (∀ A, HEq (uliftYonedaEquiv (G.obj A).hom).val
        (A.left.hom.hom.map ≫ A.hom.hom.hom.map)) ∧
      (∀ A B (f : A ⟶ B), HEq (G.map f).left f.left.left.left) ∧
      geometric (chainMap G)) ∧
  (∀ (D : SimplicialCat.{u, u})
      (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
      (Q : DaggerActualIteratedGadgetShift.FibrantOver D a b),
    ∃ X : SSet.{u}, X.KanComplex ∧ geometric (toUnit X) ∧
      ∃ G : CostructuredArrow (toPositive D a b) Q ⥤ SimplexIndex X,
        geometric (chainMap G))

end
end DaggerActualSecondConeProjectionChallenge
