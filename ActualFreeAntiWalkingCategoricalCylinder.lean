import ActualWalkingCategoricalIntervalReversal

/-!
# The entire literal free anti-involutive map retains categorical interval cylinders

The second copy uses endpoint-preserving reversal of the original walking
interval. Transport to the actual original freeAnti uses the existing natural
pair comparison. Both copies and every original simplicial operator are retained.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerModels.OriginalAntiInvolutiveFreePair
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerActualWalkingCategoricalIntervalReversal
open DaggerOriginalFreeAntiSimplicialHomotopyEquivalence
universe u
namespace DaggerActualFreeAntiWalkingCategoricalCylinder
noncomputable section

/-- The full endpoint insertion for any original source simplicial set. -/
def intervalEndpoint (X : SSet.{u}) (b : Bool) : X ⟶ X ⊗ J.{u} :=
  lift (𝟙 X) (SSet.const (ComposableArrows.mk₀ (parameterObject b)))

/-- Endpoint insertion commutes with any original source map. -/
theorem intervalEndpoint_natural {X Y : SSet.{u}} (f : X ⟶ Y) (b : Bool) :
    intervalEndpoint X b ≫ (f ⊗ₘ 𝟙 J) = f ≫ intervalEndpoint Y b := by
  apply NatTrans.ext
  funext n x
  rfl

/-- Retain the cylinder on the first copy and reverse the full parameter on the second. -/
def pairCylinder {A B : SSet.{u}} (h : A ⊗ J.{u} ⟶ B) :
    pairSSet A ⊗ J.{u} ⟶ pairSSet B where
  app n p := if p.1.2 then (h.app n (p.1.1, reverseParameter n p.2), true)
    else (h.app n (p.1.1, p.2), false)
  naturality n m i := by
    funext p
    rcases p with ⟨⟨x, b⟩, t⟩
    cases b
    · change (h.app m (A.map i x, J.map i t), false) =
        (B.map i (h.app n (x, t)), false)
      exact Prod.ext (congrFun (h.naturality i) (x, t)) rfl
    · change (h.app m (A.map (SimplexCategory.rev.map i.unop).op x,
          reverseParameter m (J.map i t)), true) =
        (B.map (SimplexCategory.rev.map i.unop).op
          (h.app n (x, reverseParameter n t)), true)
      rw [reverseParameter_natural]
      exact Prod.ext (congrFun (h.naturality (SimplexCategory.rev.map i.unop).op)
        (x, reverseParameter n t)) rfl

/-- Every full endpoint equation is retained on both original copies. -/
theorem pairCylinder_endpoint {A B : SSet.{u}} (h : A ⊗ J.{u} ⟶ B)
    (b : Bool) (f : A ⟶ B) (hf : intervalEndpoint A b ≫ h = f) :
    intervalEndpoint (pairSSet A) b ≫ pairCylinder h = (pairMap f).hom := by
  apply NatTrans.ext
  funext n p
  rcases p with ⟨x, c⟩
  cases c
  · exact Prod.ext (congrFun (NatTrans.congr_app hf n) x) rfl
  · change (h.app n (x, reverseParameter n
        ((SSet.const (ComposableArrows.mk₀ (parameterObject b)) : pairSSet A ⟶ J).app n
          (x, true))), true) = (f.app n x, true)
    rw [reverseParameter_endpoint]
    exact Prod.ext (congrFun (NatTrans.congr_app hf n) x) rfl

/-- Transport the entire pair cylinder to the literal original freeAnti objects. -/
def freeCylinder {A B : SSet.{u}} (h : A ⊗ J.{u} ⟶ B) :
    (freeAnti.obj A).toSSet ⊗ J.{u} ⟶ (freeAnti.obj B).toSSet :=
  ((underlyingPairIso A).inv ⊗ₘ 𝟙 J) ≫ pairCylinder h ≫ (underlyingPairIso B).hom

/-- The transported full endpoint is exactly the original freeAnti map. -/
theorem freeCylinder_endpoint {A B : SSet.{u}} (h : A ⊗ J.{u} ⟶ B)
    (b : Bool) (f : A ⟶ B) (hf : intervalEndpoint A b ≫ h = f) :
    intervalEndpoint (freeAnti.obj A).toSSet b ≫ freeCylinder h = (freeAnti.map f).hom := by
  have hn : (pairMap f).hom ≫ (underlyingPairIso B).hom =
      (underlyingPairIso A).hom ≫ (freeAnti.map f).hom :=
    congrArg AntiInvolutiveSSet.Hom.hom (pairIsoFreeAnti.hom.naturality f)
  calc
    _ = (underlyingPairIso A).inv ≫
        (intervalEndpoint (pairSSet A) b ≫ pairCylinder h) ≫
          (underlyingPairIso B).hom := by
      rw [freeCylinder, ← Category.assoc, ← Category.assoc, intervalEndpoint_natural]
      simp only [Category.assoc]
    _ = (underlyingPairIso A).inv ≫ (pairMap f).hom ≫
        (underlyingPairIso B).hom := by rw [pairCylinder_endpoint h b f hf]
    _ = _ := by
      rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end
end DaggerActualFreeAntiWalkingCategoricalCylinder
