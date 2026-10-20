import OriginalOrdinaryKanCoreOpposite
import DaggerModels.SimplicialSet

/-!
# Restricting the actual dagger to the original ordinary core candidate

Functoriality and the exact opposite comparison restrict the original dagger
without changing its underlying simplices, involution, or fixed vertex labels.
The candidate's Kan property for quasi-categories remains a separate obligation.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreOpposite
open DaggerOriginalSimplicialSubcomplexOpposite

universe u

namespace DaggerOriginalDaggerCoreCandidate

noncomputable section

/-- The literal original dagger maps the core inclusion into the opposite subcomplex. -/
theorem coreDagger_range (X : DaggerSSet.{u}) :
    SSet.Subcomplex.range ((ordinaryCoreCandidate X.toSSet).ι ≫ X.dagger) ≤
      oppositeSubcomplex (ordinaryCoreCandidate X.toSSet) := by
  intro q s hs
  obtain ⟨t, rfl⟩ := hs
  have ht := mem_ordinaryCoreCandidate_map X.dagger q t.val t.property
  exact mem_ordinaryCoreCandidate_unop X.toSSet q (X.dagger.app q t.val) ht

/-- The original dagger restricted to the same ordinary core candidate. -/
def coreDagger (X : DaggerSSet.{u}) :
    (ordinaryCoreCandidate X.toSSet : SSet.{u}) ⟶
      (ordinaryCoreCandidate X.toSSet : SSet.{u}).op :=
  liftToOpposite (ordinaryCoreCandidate X.toSSet)
    ((ordinaryCoreCandidate X.toSSet).ι ≫ X.dagger) (coreDagger_range X)

/-- The restricted dagger commutes with the exact original subcomplex inclusion. -/
theorem coreDagger_comp_ι (X : DaggerSSet.{u}) :
    coreDagger X ≫ SSet.opFunctor.map (ordinaryCoreCandidate X.toSSet).ι =
      (ordinaryCoreCandidate X.toSSet).ι ≫ X.dagger :=
  liftToOpposite_comp_ι _ _ _

/-- In every degree, the restricted dagger has precisely the original underlying simplex. -/
theorem coreDagger_app_val (X : DaggerSSet.{u}) (q : SimplexCategoryᵒᵖ)
    (s : (ordinaryCoreCandidate X.toSSet : SSet.{u}).obj q) :
    (SSet.opObjEquiv ((coreDagger X).app q s)).val =
      SSet.opObjEquiv (X.dagger.app q s.val) :=
  liftToOpposite_app_val _ _ _ q s

/-- The restricted dagger has exactly the original involution and fixed vertices. -/
def daggerCoreCandidate (X : DaggerSSet.{u}) : DaggerSSet.{u} where
  toSSet := (ordinaryCoreCandidate X.toSSet : SSet.{u})
  dagger := coreDagger X
  involutive n s := by
    apply Subtype.ext
    rw [coreDagger_app_val, coreDagger_app_val]
    exact X.involutive n s.val
  fixedVertices s := by
    apply Subtype.ext
    rw [coreDagger_app_val]
    exact X.fixedVertices s.val

/-- The actual subcomplex inclusion is a dagger-preserving morphism. -/
def daggerCoreInclusion (X : DaggerSSet.{u}) : daggerCoreCandidate X ⟶ X where
  hom := (ordinaryCoreCandidate X.toSSet).ι
  comm := (coreDagger_comp_ι X).symm

/-- Every original dagger-preserving morphism restricts to the same core candidates. -/
def daggerCoreMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    daggerCoreCandidate X ⟶ daggerCoreCandidate Y where
  hom := ordinaryCoreCandidateMap f.hom
  comm := by
    change ordinaryCoreCandidateMap f.hom ≫ coreDagger Y =
      coreDagger X ≫ SSet.opFunctor.map (ordinaryCoreCandidateMap f.hom)
    have : Mono (SSet.opFunctor.map (ordinaryCoreCandidate Y.toSSet).ι) :=
      mono_op_inclusion (ordinaryCoreCandidate Y.toSSet)
    apply (cancel_mono (SSet.opFunctor.map (ordinaryCoreCandidate Y.toSSet).ι)).mp
    calc
      (ordinaryCoreCandidateMap f.hom ≫ coreDagger Y) ≫
          SSet.opFunctor.map (ordinaryCoreCandidate Y.toSSet).ι =
        (ordinaryCoreCandidate X.toSSet).ι ≫ f.hom ≫ Y.dagger := by
          rw [Category.assoc, coreDagger_comp_ι, ← Category.assoc,
            ordinaryCoreCandidateMap_comp_ι, Category.assoc]
      _ = (ordinaryCoreCandidate X.toSSet).ι ≫ X.dagger ≫ SSet.opFunctor.map f.hom := by
        rw [f.comm]
      _ = (coreDagger X ≫ SSet.opFunctor.map (ordinaryCoreCandidateMap f.hom)) ≫
          SSet.opFunctor.map (ordinaryCoreCandidate Y.toSSet).ι := by
        rw [Category.assoc, ← SSet.opFunctor.map_comp, ordinaryCoreCandidateMap_comp_ι,
          SSet.opFunctor.map_comp,
          ← Category.assoc (coreDagger X)
            (SSet.opFunctor.map (ordinaryCoreCandidate X.toSSet).ι) (SSet.opFunctor.map f.hom),
          coreDagger_comp_ι, Category.assoc]

/-- The underlying restricted map commutes with the literal subcomplex inclusions. -/
theorem daggerCoreMap_comp_inclusion {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    (daggerCoreMap f).hom ≫ (daggerCoreInclusion Y).hom =
      (daggerCoreInclusion X).hom ≫ f.hom := ordinaryCoreCandidateMap_comp_ι f.hom

end

end DaggerOriginalDaggerCoreCandidate
