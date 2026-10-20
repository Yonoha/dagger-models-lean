import DaggerModels.DaggerLimitOpposite
import DaggerModels.DaggerOppositeHom
import Mathlib.CategoryTheory.Limits.Creates

/-!
Part I `bg.lem.creation`: the original ordinary
simplicial-category forgetful functor creates limits. The construction takes
a given ordinary limit cone; no ordinary HasLimits hypothesis is required.
-/

open CategoryTheory Limits Opposite Functor

universe o v w w'

noncomputable section

namespace DaggerModels.DaggerSimplicialCat.OrdinaryLimitCreation

variable {J : Type w} [Category.{w'} J] (K : J ⥤ DaggerSimplicialCat.{o, v})
  (c : Cone (K ⋙ forget)) (hc : IsLimit c)

/-- Equip the unchanged ordinary apex with its induced actual dagger. -/
def point : DaggerSimplicialCat.{o, v} :=
  ⟨c.pt, DaggerSimplicialStructure.ofOppositeFunctor c.pt
    (LimitOpposite.induced K c hc) (LimitOpposite.induced_obj K c hc)
      (LimitOpposite.induced_square K c hc)⟩

theorem point_dagger : daggerNatural.app (point K c hc) = LimitOpposite.induced K c hc :=
  DaggerSimplicialStructure.ofOppositeFunctor_daggerFunctor c.pt
    (LimitOpposite.induced K c hc) (LimitOpposite.induced_obj K c hc)
      (LimitOpposite.induced_square K c hc)

/-- Each original ordinary projection lifts without changing its enriched functor. -/
def projection (j : J) : point K c hc ⟶ K.obj j :=
  Hom.ofCommutingOpposite (c.π.app j) (by
    rw [point_dagger]
    exact (LimitOpposite.induced_fac K c hc j).symm)

def liftedCone : Cone K where
  pt := point K c hc
  π :=
    { app := projection K c hc
      naturality := by
        intro i j f
        apply forget.map_injective
        change 𝟙 c.pt ≫ c.π.app j = c.π.app i ≫ (K ⋙ forget).map f
        exact c.π.naturality f }

/-- The entire original cone, including its actual enriched projections, is retained. -/
theorem forget_liftedCone : forget.mapCone (liftedCone K c hc) = c := rfl

/-- The ordinary universal map commutes with the induced opposite dagger. -/
theorem lift_commuting (s : Cone K) :
    hc.lift (forget.mapCone s) ≫ daggerNatural.app (point K c hc) =
      daggerNatural.app s.pt ≫
        SimplicialCat.oppositeFunctor.map (hc.lift (forget.mapCone s)) := by
  rw [point_dagger]
  apply (LimitOpposite.oppositeIsLimit K c hc).hom_ext
  intro j
  let l := hc.lift (forget.mapCone s)
  let π := c.π.app j
  let d := LimitOpposite.induced K c hc
  let δ := daggerNatural.app (K.obj j)
  have hl : l ≫ π = forget.map (s.π.app j) := hc.fac (forget.mapCone s) j
  have hd : d ≫ SimplicialCat.oppositeMap π = π ≫ δ :=
    LimitOpposite.induced_fac K c hc j
  change (l ≫ d) ≫ SimplicialCat.oppositeMap π =
    (daggerNatural.app s.pt ≫ SimplicialCat.oppositeFunctor.map l) ≫
      SimplicialCat.oppositeMap π
  calc
    _ = l ≫ (π ≫ δ) := by rw [Category.assoc, hd]
    _ = forget.map (s.π.app j) ≫ δ := by rw [← Category.assoc, hl]
    _ = daggerNatural.app s.pt ≫
        SimplicialCat.oppositeFunctor.map (forget.map (s.π.app j)) :=
      (s.π.app j).commutingOpposite
    _ = daggerNatural.app s.pt ≫ SimplicialCat.oppositeFunctor.map (l ≫ π) := by rw [hl]
    _ = _ := by rw [Functor.map_comp, Category.assoc]; rfl

/-- The universal enriched map lifts to the actual dagger-functor bundle. -/
def lift (s : Cone K) : s.pt ⟶ point K c hc :=
  Hom.ofCommutingOpposite (hc.lift (forget.mapCone s)) (lift_commuting K c hc s)

/-- The actual lifted cone satisfies the complete limit universal property. -/
def isLimit : IsLimit (liftedCone K c hc) :=
  IsLimit.ofFaithful forget (by simpa only [forget_liftedCone] using hc)
    (lift K c hc) (fun _ ↦ rfl)

def liftsToLimit : LiftsToLimit K forget c hc where
  liftedCone := liftedCone K c hc
  validLift := eqToIso (forget_liftedCone K c hc)
  makesLimit := isLimit K c hc

/-- Actual ordinary dagger forgetting creates the limit of every diagram. -/
def createsLimit : CreatesLimit K forget :=
  createsLimitOfReflectsIso (fun c hc ↦ liftsToLimit K c hc)

/-- Creation holds for arbitrary independent diagram, object and hom universes. -/
def forgetCreatesLimitsOfSize : CreatesLimitsOfSize.{w', w} forget.{o, v} where
  CreatesLimitsOfShape := { CreatesLimit := createsLimit _ }

end DaggerModels.DaggerSimplicialCat.OrdinaryLimitCreation
