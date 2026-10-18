import OriginalFixedObjectGroupoidAcyclicity
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full simplicial pullbacks as pairs with an exact equality constraint

All simplex degrees and operators are retained. The pair construction has
Mathlib's complete pullback universal property for the original two maps.
-/

set_option autoImplicit false
open CategoryTheory Limits
universe u
namespace DaggerOriginalSimplicialPullbackPairs
noncomputable section

/-- The same-degree pair fiber, with every original simplicial operator. -/
def pairedPullback {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : SSet.{u} where
  obj n := {p : X.obj n × Y.obj n // f.app n p.1 = g.app n p.2}
  map {n m} i p := ⟨(X.map i p.1.1, Y.map i p.1.2), by
    exact (congrFun (f.naturality i) p.1.1).trans
      ((congrArg (Z.map i) p.2).trans (congrFun (g.naturality i) p.1.2).symm)⟩
  map_id n := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (X.map_id n) p.1.1
    · exact congrFun (Y.map_id n) p.1.2
  map_comp i j := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (X.map_comp i j) p.1.1
    · exact congrFun (Y.map_comp i j) p.1.2

/-- The entire original first simplicial projection. -/
def pairedFst {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : pairedPullback f g ⟶ X where
  app _ p := p.1.1
  naturality _ _ _ := by funext p; rfl

/-- The entire original second simplicial projection. -/
def pairedSnd {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : pairedPullback f g ⟶ Y where
  app _ p := p.1.2
  naturality _ _ _ := by funext p; rfl

/-- Exact commutativity of the full simplicial square. -/
theorem paired_comm {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pairedFst f g ≫ f = pairedSnd f g ≫ g := by
  apply NatTrans.ext
  funext n p
  exact p.2

/-- Pair any two full simplicial maps satisfying the same exact constraint. -/
def pairedLift {W X Y Z : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : W ⟶ pairedPullback f g where
  app n w := ⟨(a.app n w, b.app n w), congrFun (NatTrans.congr_app h n) w⟩
  naturality _ _ i := by
    funext w
    apply Subtype.ext
    exact Prod.ext (congrFun (a.naturality i) w) (congrFun (b.naturality i) w)

/-- The first leg of pairing is exactly the full specified first map. -/
theorem pairedLift_fst {W X Y Z : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    pairedLift a b h ≫ pairedFst f g = a := rfl

/-- The second leg of pairing is exactly the full specified second map. -/
theorem pairedLift_snd {W X Y Z : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    pairedLift a b h ≫ pairedSnd f g = b := rfl

/-- Both full projections determine the entire map to the simplicial pair fiber. -/
theorem paired_ext {W X Y Z : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a b : W ⟶ pairedPullback f g}
    (h₁ : a ≫ pairedFst f g = b ≫ pairedFst f g)
    (h₂ : a ≫ pairedSnd f g = b ≫ pairedSnd f g) : a = b := by
  apply NatTrans.ext
  funext n w
  apply Subtype.ext
  exact Prod.ext (congrFun (NatTrans.congr_app h₁ n) w)
    (congrFun (NatTrans.congr_app h₂ n) w)

/-- The pair fiber is an actual native pullback of the unchanged full simplicial maps. -/
def pairedIsLimit {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (PullbackCone.mk (pairedFst f g) (pairedSnd f g) (paired_comm f g)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ pairedLift s.fst s.snd s.condition)
    (fun s ↦ pairedLift_fst s.fst s.snd s.condition)
    (fun s ↦ pairedLift_snd s.fst s.snd s.condition) (by
      intro s m h₁ h₂
      apply paired_ext
      · exact h₁.trans (pairedLift_fst s.fst s.snd s.condition).symm
      · exact h₂.trans (pairedLift_snd s.fst s.snd s.condition).symm)

/-- The full native IsPullback witness identifies all four original legs. -/
theorem pairedIsPullback {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (pairedFst f g) (pairedSnd f g) f g :=
  IsPullback.of_isLimit (pairedIsLimit f g)

end
end DaggerOriginalSimplicialPullbackPairs
