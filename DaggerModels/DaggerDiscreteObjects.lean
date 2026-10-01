import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! Actual discrete dagger simplicial categories and the object generator in
Part I `bg.lem.I-inj`. Homs are constant lifted equality types: all diagonal
simplices are identities, and distinct objects have no arrows. The empty and
one-object categories have their actual initial and terminal universal
properties. No Kan or model-category assertion is made. -/

open CategoryTheory MonoidalCategory Limits

universe o v

namespace DaggerModels.DaggerDiscreteObjects

noncomputable section

/-- Equality reversal supplies the dagger on the existing discrete enrichment. -/
def discreteDagger (V : Type o) :
    @DaggerSimplicialStructure.{o, v} (SimplicialCat.discrete.{o, v} V).Obj
      (SimplicialCat.discrete V).enriched where
  dagger x y := { app := fun _ p ↦ ⟨⟨p.down.down.symm⟩⟩ }
  dagger_involutive x y := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (x = y))) inferInstance _ _
  dagger_id x := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (x = x))) inferInstance _ _
  dagger_comp x y z := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (z = x))) inferInstance _ _

/-- The actual discrete dagger category on V, with independent object/hom universes. -/
def discrete (V : Type o) : DaggerSimplicialCat.{o, v} :=
  ⟨SimplicialCat.discrete V, discreteDagger V⟩

/-- An arbitrary object function lifts to a dagger enriched functor. -/
def lift (V : Type o) (C : DaggerSimplicialCat.{o, v}) (f : V → C.Obj) :
    discrete V ⟶ C where
  toEnrichedFunctor := SimplicialCat.discreteLift V C.toSimplicialCat f
  map_dagger x y := by
    ext n p
    obtain ⟨⟨h⟩⟩ := p
    subst y
    exact DaggerSimplicialStructure.dagger_id_app (f x) n

/-- Full dagger functors from the discrete category are exactly object functions. -/
def homEquiv (V : Type o) (C : DaggerSimplicialCat.{o, v}) :
    (discrete V ⟶ C) ≃ (V → C.Obj) where
  toFun F := F.obj
  invFun := lift V C
  left_inv F := by
    apply DaggerSimplicialCat.Hom.ext
    exact (SimplicialCat.discreteHomEquiv V C.toSimplicialCat).left_inv F.toEnrichedFunctor
  right_inv _ := rfl

@[simp]
theorem lift_obj (V : Type o) (C : DaggerSimplicialCat.{o, v})
    (f : V → C.Obj) (x : V) : (lift V C f).obj x = f x := rfl

/-- Every diagonal simplex in the concrete discrete category is the enriched identity. -/
theorem discrete_identity_only (V : Type o) (x : V) (n : SimplexCategoryᵒᵖ)
    (a : ((discrete.{o, v} V).enriched.Hom x x).obj n) :
    a = ((discrete V).enriched.id x).app n PUnit.unit :=
  @Subsingleton.elim (ULift.{v} (PLift (x = x))) inferInstance _ _

/-- There are no simplices between distinct objects of the concrete discrete category. -/
theorem discrete_hom_empty (V : Type o) {x y : V} (h : x ≠ y)
    (n : SimplexCategoryᵒᵖ) :
    IsEmpty (((discrete.{o, v} V).enriched.Hom x y).obj n) :=
  ⟨fun p ↦ h p.down.down⟩

/-- The actual empty dagger simplicial category. -/
def empty : DaggerSimplicialCat.{o, v} := discrete PEmpty.{o + 1}

/-- The actual one-object identity-only dagger simplicial category. -/
def point : DaggerSimplicialCat.{o, v} := discrete PUnit.{o + 1}

/-- The unique map from the actual empty category. -/
def emptyMap (C : DaggerSimplicialCat.{o, v}) : empty ⟶ C :=
  lift PEmpty C PEmpty.elim

theorem emptyMap_unique {C : DaggerSimplicialCat.{o, v}} (F : empty ⟶ C) :
    F = emptyMap C := by
  apply (homEquiv PEmpty C).injective
  funext x
  exact PEmpty.elim x

/-- Full categorical initiality, without a colimit-existence premise. -/
def emptyIsInitial : IsInitial empty.{o, v} :=
  IsInitial.ofUniqueHom emptyMap (fun _ F ↦ emptyMap_unique F)

/-- The unique actual map from the empty category to the identity-only point. -/
def emptyToPoint : empty.{o, v} ⟶ point := emptyMap point

/-- Select an arbitrary object by its unique identity-preserving point functor. -/
def fromPoint (C : DaggerSimplicialCat.{o, v}) (x : C.Obj) : point ⟶ C :=
  lift PUnit C (fun _ ↦ x)

/-- Point functors classify all actual target objects. -/
def pointHomEquiv (C : DaggerSimplicialCat.{o, v}) : (point ⟶ C) ≃ C.Obj where
  toFun F := F.obj PUnit.unit
  invFun := fromPoint C
  left_inv F := by
    apply (homEquiv PUnit C).injective
    funext x
    cases x
    rfl
  right_inv _ := rfl

/-- The unique full dagger functor into the concrete one-object category. -/
def toPoint (C : DaggerSimplicialCat.{o, v}) : C ⟶ point where
  obj _ := PUnit.unit
  map _ _ := { app := fun _ _ ↦ ⟨⟨rfl⟩⟩ }
  map_id _ := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (PUnit.unit = PUnit.unit))) inferInstance _ _
  map_comp _ _ _ := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (PUnit.unit = PUnit.unit))) inferInstance _ _
  map_dagger _ _ := by
    ext n p
    exact @Subsingleton.elim (ULift.{v} (PLift (PUnit.unit = PUnit.unit))) inferInstance _ _

theorem toPoint_unique {C : DaggerSimplicialCat.{o, v}} (F : C ⟶ point) :
    F = toPoint C := by
  apply DaggerSimplicialCat.Hom.ext
  apply EnrichedFunctor.ext SSet (F := F.toEnrichedFunctor)
    (G := (toPoint C).toEnrichedFunctor)
    (fun _ ↦ @Subsingleton.elim PUnit.{o + 1} inferInstance _ _)
  intro x y
  ext n p
  exact @Subsingleton.elim (ULift.{v} (PLift (PUnit.unit = PUnit.unit))) inferInstance _ _

/-- Full categorical terminality of the concrete identity-only point. -/
def pointIsTerminal : IsTerminal point.{o, v} :=
  IsTerminal.ofUniqueHom toPoint (fun _ F ↦ toPoint_unique F)

/-- Object surjectivity is exactly lifting against the actual empty-to-point map. -/
theorem hasLiftingProperty_iff_surjective {C D : DaggerSimplicialCat.{o, v}} (p : C ⟶ D) :
    HasLiftingProperty emptyToPoint.{o, v} p ↔ Function.Surjective p.obj := by
  constructor
  · intro h y
    have sq : CommSq (emptyMap C) emptyToPoint p (fromPoint D y) :=
      ⟨emptyIsInitial.hom_ext _ _⟩
    have : sq.HasLift := h.sq_hasLift sq
    refine ⟨sq.lift.obj PUnit.unit, ?_⟩
    exact congrArg (fun F : point ⟶ D ↦ F.obj PUnit.unit) sq.fac_right
  · intro h
    refine ⟨fun {F G} sq ↦ ?_⟩
    obtain ⟨x, hx⟩ := h (G.obj PUnit.unit)
    refine CommSq.HasLift.mk'
      { l := fromPoint C x
        fac_left := emptyIsInitial.hom_ext _ _
        fac_right := ?_ }
    apply (pointHomEquiv D).injective
    exact hx

end
end DaggerModels.DaggerDiscreteObjects
