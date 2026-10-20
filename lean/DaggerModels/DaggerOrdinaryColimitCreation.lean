import DaggerModels.DaggerColimitOpposite
import DaggerModels.DaggerOppositeHom
import Mathlib.CategoryTheory.Limits.Creates

/-! Lift every given ordinary simplicial-category colimit to the original
dagger category, including the complete enriched universal property. -/

open CategoryTheory Limits

universe o v w w'

namespace DaggerModels.DaggerSimplicialCat.OrdinaryColimit

variable {J : Type w} [Category.{w'} J] (K : J ⥤ DaggerSimplicialCat.{o, v})
  (c : Cocone (K ⋙ forget)) (hc : IsColimit c)

noncomputable def point : DaggerSimplicialCat.{o, v} where
  toSimplicialCat := c.pt
  daggerStructure := DaggerSimplicialStructure.ofOppositeFunctor c.pt
    (toOpposite K c hc) (toOpposite_obj K c hc) (toOpposite_square K c hc)

theorem point_dagger : daggerNatural.app (point K c hc) = toOpposite K c hc :=
  DaggerSimplicialStructure.ofOppositeFunctor_daggerFunctor c.pt
    (toOpposite K c hc) (toOpposite_obj K c hc) (toOpposite_square K c hc)

noncomputable def leg (j : J) : K.obj j ⟶ point K c hc :=
  Hom.ofCommutingOpposite (C := K.obj j) (D := point K c hc) (c.ι.app j) (by
    rw [point_dagger]
    exact toOpposite_fac K c hc j)

noncomputable def cocone : Cocone K where
  pt := point K c hc
  ι :=
    { app := leg K c hc
      naturality := by
        intro i j a
        apply forget.map_injective
        change forget.map (K.map a) ≫ c.ι.app j = c.ι.app i ≫ 𝟙 c.pt
        simpa only [Category.comp_id] using c.w a }

theorem map_cocone : forget.mapCocone (cocone K c hc) = c := rfl

/-- Any ordinary factorization into a dagger cocone preserves the induced dagger. -/
theorem factorization_commutes (s : Cocone K) (m : c.pt ⟶ forget.obj s.pt)
    (hm : ∀ j, c.ι.app j ≫ m = forget.map (s.ι.app j)) :
    m ≫ daggerNatural.app s.pt = toOpposite K c hc ≫ SimplicialCat.oppositeFunctor.map m := by
  apply hc.hom_ext
  intro j
  calc
    c.ι.app j ≫ m ≫ daggerNatural.app s.pt =
        forget.map (s.ι.app j) ≫ daggerNatural.app s.pt := by rw [← Category.assoc, hm]
    _ = daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (forget.map (s.ι.app j)) :=
      daggerNatural.naturality (s.ι.app j)
    _ = daggerNatural.app (K.obj j) ≫
        SimplicialCat.oppositeFunctor.map (c.ι.app j ≫ m) := by rw [hm]
    _ = (c.ι.app j ≫ toOpposite K c hc) ≫
        SimplicialCat.oppositeFunctor.map m := by
      rw [Functor.map_comp, toOpposite_fac]
      simp only [Category.assoc]
    _ = c.ι.app j ≫ toOpposite K c hc ≫ SimplicialCat.oppositeFunctor.map m :=
      Category.assoc _ _ _

noncomputable def desc (s : Cocone K) : point K c hc ⟶ s.pt :=
  Hom.ofCommutingOpposite (C := point K c hc) (D := s.pt)
    (hc.desc (forget.mapCocone s)) (by
      rw [point_dagger]
      exact factorization_commutes K c hc s _ (hc.fac (forget.mapCocone s)))

theorem leg_desc (s : Cocone K) (j : J) : leg K c hc j ≫ desc K c hc s = s.ι.app j := by
  apply forget.map_injective
  change c.ι.app j ≫ hc.desc (forget.mapCocone s) = forget.map (s.ι.app j)
  exact hc.fac (forget.mapCocone s) j

noncomputable def isColimit : IsColimit (cocone K c hc) where
  desc := desc K c hc
  fac := leg_desc K c hc
  uniq s m hm := by
    apply forget.map_injective
    apply hc.hom_ext
    intro j
    change c.ι.app j ≫ forget.map m = c.ι.app j ≫ hc.desc (forget.mapCocone s)
    rw [hc.fac]
    exact congrArg (forget.map) (hm j)

noncomputable def lifts : LiftsToColimit K forget c hc where
  liftedCocone := cocone K c hc
  validLift := Iso.refl _
  makesColimit := isColimit K c hc

/-- The actual ordinary forgetful functor creates the colimit of every dagger diagram. -/
noncomputable def createsColimit : CreatesColimit K forget :=
  createsColimitOfReflectsIso (fun c hc ↦ lifts K c hc)

/-- Creation holds at independent object, hom, and diagram universes. -/
noncomputable def forgetCreatesColimits : CreatesColimitsOfSize.{w', w} forget.{o, v} := by
  constructor
  intro J _
  constructor
  intro K
  exact createsColimit K

end DaggerModels.DaggerSimplicialCat.OrdinaryColimit
