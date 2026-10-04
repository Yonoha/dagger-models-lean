import DaggerModels.DaggerAdjunctionCompatibility
import DaggerModels.DaggerRigidification

/-!
# The original rigidification adjunction lifted to dagger morphisms

The bijection is the restriction of the original ordinary Hom equivalence.
The actual underlying functors, unit, and counit are retained at every common
universe. The free-functor comparison is a separate assertion.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerAdjunction

open DaggerNerve DaggerRigidification

/-- The original Hom equivalence, restricted to the actual dagger hom bundles. -/
def homEquiv (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    (daggerRigidification.obj X ⟶ C) ≃ (X ⟶ daggerCoherentNerve.obj C) where
  toFun f :=
    { hom := rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat
        f.toEnrichedFunctor
      comm := (dagger_compatibility_iff X C f.toEnrichedFunctor).1 (by
        simpa only [daggerRigidification, enrichedDagger, obj_daggerFunctor, daggerToOpposite, Category.assoc]
          using f.commutingOpposite) }
  invFun g := DaggerSimplicialCat.Hom.ofCommutingOpposite
    ((rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat).symm g.hom)
    (by
      have h := (dagger_compatibility_iff X C
        ((rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat).symm
          g.hom)).2 (by simpa only [Equiv.apply_symm_apply] using g.comm)
      simpa only [daggerRigidification, enrichedDagger, obj_daggerFunctor, daggerToOpposite, Category.assoc] using h)
  left_inv f := by
    apply DaggerSimplicialCat.Hom.ext
    exact Equiv.symm_apply_apply _ _
  right_inv g := by
    apply DaggerSSet.Hom.ext
    exact Equiv.apply_symm_apply _ _

/-- Forgetting the restricted forward correspondence gives the original one exactly. -/
theorem homEquiv_hom (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (f : daggerRigidification.obj X ⟶ C) :
    (homEquiv X C f).hom =
      rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat
        f.toEnrichedFunctor := rfl

/-- Forgetting the restricted inverse correspondence also retains the original map. -/
theorem homEquiv_symm_toEnrichedFunctor (X : DaggerSSet.{u})
    (C : DaggerSimplicialCat.{u, u}) (g : X ⟶ daggerCoherentNerve.obj C) :
    ((homEquiv X C).symm g).toEnrichedFunctor =
      (rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat).symm
        g.hom := rfl

/-- Full source naturality is inherited from the original ordinary adjunction. -/
theorem homEquiv_naturality_left_symm {X X' : DaggerSSet.{u}}
    {C : DaggerSimplicialCat.{u, u}} (f : X' ⟶ X) (g : X ⟶ daggerCoherentNerve.obj C) :
    (homEquiv X' C).symm (f ≫ g) = daggerRigidification.map f ≫ (homEquiv X C).symm g := by
  apply DaggerSimplicialCat.Hom.ext
  exact rigidificationCoherentNerveAdjunction.homEquiv_naturality_left_symm f.hom g.hom

/-- Full target naturality is inherited from the original ordinary adjunction. -/
theorem homEquiv_naturality_right {X : DaggerSSet.{u}}
    {C D : DaggerSimplicialCat.{u, u}} (f : daggerRigidification.obj X ⟶ C) (g : C ⟶ D) :
    homEquiv X D (f ≫ g) = homEquiv X C f ≫ daggerCoherentNerve.map g := by
  apply DaggerSSet.Hom.ext
  exact rigidificationCoherentNerveAdjunction.homEquiv_naturality_right
    f.toEnrichedFunctor g.toEnrichedFunctor

/-- The actual rigidification/coherent-nerve adjunction between dagger categories. -/
def daggerRigidificationCoherentNerveAdjunction :
    daggerRigidification.{u} ⊣ daggerCoherentNerve.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm
      homEquiv_naturality_right := homEquiv_naturality_right }

/-- The lifted adjunction uses exactly the restricted original Hom equivalence. -/
theorem adjunction_homEquiv :
    daggerRigidificationCoherentNerveAdjunction.{u}.homEquiv = homEquiv :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The actual dagger unit has the original ordinary unit as its underlying map. -/
theorem adjunction_unit (X : DaggerSSet.{u}) :
    (daggerRigidificationCoherentNerveAdjunction.unit.app X).hom =
      rigidificationCoherentNerveAdjunction.unit.app X.toSSet := by
  rw [← Adjunction.homEquiv_id, adjunction_homEquiv, homEquiv_hom]
  exact rigidificationCoherentNerveAdjunction.homEquiv_id X.toSSet

/-- The actual dagger counit has the original ordinary counit as its enriched functor. -/
theorem adjunction_counit (C : DaggerSimplicialCat.{u, u}) :
    (daggerRigidificationCoherentNerveAdjunction.counit.app C).toEnrichedFunctor =
      rigidificationCoherentNerveAdjunction.counit.app C.toSimplicialCat := by
  rw [← Adjunction.homEquiv_symm_id, adjunction_homEquiv, homEquiv_symm_toEnrichedFunctor]
  exact rigidificationCoherentNerveAdjunction.homEquiv_symm_id C.toSimplicialCat

end DaggerModels.OrdinaryRigidification.DaggerAdjunction
