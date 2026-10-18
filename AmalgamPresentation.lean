import AmalgamOrdinaryPresentation
import DaggerModels.DaggerOrdinaryColimitCreation

/-! Lift the actual ordinary presentation by the existing colimit-creation theorem.
Both original full dagger factor functors and arbitrary-target pushout UP are retained. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerAmalgamPresentation

noncomputable section

namespace Dagger

variable (B B' : DaggerSimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

abbrev diagram := span (DaggerDiscreteObjects.fromPoint B b)
  (DaggerDiscreteObjects.fromPoint B' b')

def ordinaryCocone : Cocone (diagram B B' b b' ⋙ DaggerSimplicialCat.forget) :=
  (Cocones.precompose (spanCompIso DaggerSimplicialCat.forget
    (DaggerDiscreteObjects.fromPoint B b) (DaggerDiscreteObjects.fromPoint B' b')).hom).obj
      (cocone B.toSimplicialCat B'.toSimplicialCat b b')

def ordinaryIsColimit : IsColimit (ordinaryCocone B B' b b') :=
  (IsColimit.precomposeHomEquiv (spanCompIso DaggerSimplicialCat.forget
    (DaggerDiscreteObjects.fromPoint B b) (DaggerDiscreteObjects.fromPoint B' b'))
      (cocone B.toSimplicialCat B'.toSimplicialCat b b')).symm
        (isColimit B.toSimplicialCat B'.toSimplicialCat b b')

/-- Exactly the tagged-object path quotient, with the canonical induced dagger. -/
def presentation : DaggerSimplicialCat.{u, u} :=
  DaggerSimplicialCat.OrdinaryColimit.point (diagram B B' b b')
    (ordinaryCocone B B' b b') (ordinaryIsColimit B B' b b')

abbrev left : B ⟶ presentation B B' b b' :=
  DaggerSimplicialCat.OrdinaryColimit.leg (diagram B B' b b')
    (ordinaryCocone B B' b b') (ordinaryIsColimit B B' b b') .left
abbrev right : B' ⟶ presentation B B' b b' :=
  DaggerSimplicialCat.OrdinaryColimit.leg (diagram B B' b b')
    (ordinaryCocone B B' b b') (ordinaryIsColimit B B' b b') .right

theorem presentation_underlying : (presentation B B' b b').toSimplicialCat =
    Q B.toSimplicialCat B'.toSimplicialCat b b' := rfl

theorem left_underlying : DaggerSimplicialCat.forget.map (left B B' b b') =
    leftLeg B.toSimplicialCat B'.toSimplicialCat b b' :=
  Category.id_comp _

theorem right_underlying : DaggerSimplicialCat.forget.map (right B B' b b') =
    rightLeg B.toSimplicialCat B'.toSimplicialCat b b' :=
  Category.id_comp _

/-- Full actual dagger pushout, not an assumed universal property. -/
theorem isPushout : IsPushout (DaggerDiscreteObjects.fromPoint B b)
    (DaggerDiscreteObjects.fromPoint B' b') (left B B' b b') (right B B' b b') :=
  IsPushout.of_isColimit_cocone
    (DaggerSimplicialCat.OrdinaryColimit.isColimit (diagram B B' b b')
      (ordinaryCocone B B' b b') (ordinaryIsColimit B B' b b'))

theorem condition : DaggerDiscreteObjects.fromPoint B b ≫ left B B' b b' =
    DaggerDiscreteObjects.fromPoint B' b' ≫ right B B' b b' :=
  (isPushout B B' b b').w

variable {E : DaggerSimplicialCat.{u, u}}

def desc (F : B ⟶ E) (F' : B' ⟶ E)
    (h : DaggerDiscreteObjects.fromPoint B b ≫ F =
      DaggerDiscreteObjects.fromPoint B' b' ≫ F') : presentation B B' b b' ⟶ E :=
  (isPushout B B' b b').desc F F' h

theorem left_desc (F : B ⟶ E) (F' : B' ⟶ E)
    (h : DaggerDiscreteObjects.fromPoint B b ≫ F =
      DaggerDiscreteObjects.fromPoint B' b' ≫ F') : left B B' b b' ≫ desc B B' b b' F F' h = F :=
  (isPushout B B' b b').inl_desc F F' h

theorem right_desc (F : B ⟶ E) (F' : B' ⟶ E)
    (h : DaggerDiscreteObjects.fromPoint B b ≫ F =
      DaggerDiscreteObjects.fromPoint B' b' ≫ F') : right B B' b b' ≫ desc B B' b b' F F' h = F' :=
  (isPushout B B' b b').inr_desc F F' h

theorem desc_unique (F : B ⟶ E) (F' : B' ⟶ E)
    (h : DaggerDiscreteObjects.fromPoint B b ≫ F =
      DaggerDiscreteObjects.fromPoint B' b' ≫ F') (H : presentation B B' b b' ⟶ E)
    (hl : left B B' b b' ≫ H = F) (hr : right B B' b b' ≫ H = F') :
    H = desc B B' b b' F F' h :=
  (isPushout B B' b b').hom_ext (hl.trans (left_desc B B' b b' F F' h).symm)
    (hr.trans (right_desc B B' b b' F F' h).symm)

/-- Both complete arbitrary target functors and their full gluing equation. -/
abbrev Data (E : DaggerSimplicialCat.{u, u}) :=
  Σ F : B ⟶ E, {F' : B' ⟶ E // DaggerDiscreteObjects.fromPoint B b ≫ F =
    DaggerDiscreteObjects.fromPoint B' b' ≫ F'}

theorem data_ext {F G : Data B B' b b' E} (h : F.1 = G.1)
    (h' : F.2.val = G.2.val) : F = G := by
  rcases F with ⟨F, F', hF⟩
  rcases G with ⟨G, G', hG⟩
  cases h
  apply congrArg (Sigma.mk F)
  exact Subtype.ext h'

def homEquiv (E : DaggerSimplicialCat.{u, u}) :
    (presentation B B' b b' ⟶ E) ≃ Data B B' b b' E where
  toFun H := ⟨left B B' b b' ≫ H, right B B' b b' ≫ H, by
    rw [← Category.assoc, ← Category.assoc, condition]⟩
  invFun F := desc B B' b b' F.1 F.2.val F.2.property
  left_inv H := by
    symm
    exact desc_unique B B' b b' _ _ _ H rfl rfl
  right_inv F := by
    exact data_ext B B' b b' (left_desc B B' b b' F.1 F.2.val F.2.property)
      (right_desc B B' b b' F.1 F.2.val F.2.property)

variable {P : DaggerSimplicialCat.{u, u}} (i : B ⟶ P) (i' : B' ⟶ P)
  (sq : IsPushout (DaggerDiscreteObjects.fromPoint B b)
    (DaggerDiscreteObjects.fromPoint B' b') i i')

/-- The whole enriched dagger iso with any original pushout apex and both original legs. -/
def originalIso : presentation B B' b b' ≅ P :=
  (isPushout B B' b b').isoIsPushout B B' sq

theorem left_originalIso_hom : left B B' b b' ≫ (originalIso B B' b b' i i' sq).hom = i :=
  IsPushout.inl_isoIsPushout_hom B B' (isPushout B B' b b') sq

theorem right_originalIso_hom : right B B' b b' ≫ (originalIso B B' b b' i i' sq).hom = i' :=
  IsPushout.inr_isoIsPushout_hom B B' (isPushout B B' b b') sq

theorem left_originalIso_inv : i ≫ (originalIso B B' b b' i i' sq).inv = left B B' b b' :=
  IsPushout.inl_isoIsPushout_inv B B' (isPushout B B' b b') sq

theorem right_originalIso_inv : i' ≫ (originalIso B B' b b' i i' sq).inv = right B B' b b' :=
  IsPushout.inr_isoIsPushout_inv B B' (isPushout B B' b b') sq

end Dagger
end
end DaggerAmalgamPresentation
