import DaggerModels.DaggerGraphPresentable
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Pointwise pullbacks of Type-valued accessible functors

The literal fiber product, with its complete pullback universal property,
is finitely accessible when its three factor functors are finitely accessible.
-/

open CategoryTheory Limits

universe u v w

namespace DaggerModels.TypeFunctorPullback

variable {C : Type v} [Category.{w} C] {F G H : C ⥤ Type u}
  (p : F ⟶ H) (q : G ⟶ H)

def functor : C ⥤ Type u where
  obj X := {e : F.obj X × G.obj X // p.app X e.1 = q.app X e.2}
  map {X Y} f e := ⟨(F.map f e.1.1, G.map f e.1.2), by
    calc
      p.app Y (F.map f e.1.1) = H.map f (p.app X e.1.1) :=
        congrFun (p.naturality f) e.1.1
      _ = H.map f (q.app X e.1.2) := congrArg (H.map f) e.2
      _ = q.app Y (G.map f e.1.2) := (congrFun (q.naturality f) e.1.2).symm⟩
  map_id X := by
    funext e
    apply Subtype.ext
    change (F.map (𝟙 X) e.1.1, G.map (𝟙 X) e.1.2) = e.1
    simp
  map_comp f g := by
    funext e
    apply Subtype.ext
    change (F.map (f ≫ g) e.1.1, G.map (f ≫ g) e.1.2) =
      (F.map g (F.map f e.1.1), G.map g (G.map f e.1.2))
    simp

def fst : functor p q ⟶ F where
  app _ e := e.1.1

def snd : functor p q ⟶ G where
  app _ e := e.1.2

def cone : PullbackCone p q := PullbackCone.mk (fst p q) (snd p q) (by
  ext X e
  exact e.2)

def lift (s : PullbackCone p q) : s.pt ⟶ functor p q where
  app X e := ⟨(s.fst.app X e, s.snd.app X e),
    congrArg (fun t : s.pt ⟶ H ↦ t.app X e) s.condition⟩
  naturality {X Y} f := by
    funext e
    apply Subtype.ext
    exact Prod.ext (congrFun (s.fst.naturality f) e) (congrFun (s.snd.naturality f) e)

def isLimit : IsLimit (cone p q) := PullbackCone.IsLimit.mk _ (lift p q)
  (fun _ ↦ by ext X e; rfl)
  (fun _ ↦ by ext X e; rfl)
  (fun s m h₁ h₂ ↦ by
    ext X e
    apply Subtype.ext
    exact Prod.ext (congrArg (fun t : s.pt ⟶ F ↦ t.app X e) h₁)
      (congrArg (fun t : s.pt ⟶ G ↦ t.app X e) h₂))

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A pointwise fiber product of finitely accessible functors is finitely accessible. -/
theorem isCardinalAccessible
    [F.IsCardinalAccessible Cardinal.aleph0.{u}]
    [G.IsCardinalAccessible Cardinal.aleph0.{u}]
    [H.IsCardinalAccessible Cardinal.aleph0.{u}] :
    (functor p q).IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI : ∀ k, ((cospan p q).obj k).IsCardinalAccessible Cardinal.aleph0.{u} := fun k ↦ by
    cases k with
    | none => exact inferInstanceAs (H.IsCardinalAccessible Cardinal.aleph0)
    | some k =>
      cases k
      · exact inferInstanceAs (F.IsCardinalAccessible Cardinal.aleph0)
      · exact inferInstanceAs (G.IsCardinalAccessible Cardinal.aleph0)
  exact Functor.isCardinalAccessible_of_isLimit (cone p q) (isLimit p q)
    Cardinal.aleph0 (hasCardinalLT_of_finite (Arrow WalkingCospan) Cardinal.aleph0 le_rfl)

end DaggerModels.TypeFunctorPullback
