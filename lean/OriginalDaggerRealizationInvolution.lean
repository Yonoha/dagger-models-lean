import OriginalRealizationReversalCoherence
import DaggerModels.SimplicialSet

/-!
# The actual topological involution induced by a dagger simplicial set

The map uses the original dagger and the proved realization comparison.
Its square and naturality are equations of actual TopCat morphisms.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels
open DaggerOriginalRealizationOppositeComparison
open DaggerOriginalRealizationReversalCoherence

universe u

namespace DaggerOriginalDaggerRealizationInvolution

noncomputable section

private abbrev O : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor.{u}
private abbrev R : SSet.{u} ⥤ TopCat.{u} := SSet.toTop.{u}

/-- The original strict dagger equation as a full simplicial-set map. -/
theorem dagger_double (X : DaggerSSet.{u}) :
    X.dagger ≫ O.map X.dagger ≫
      SSet.opFunctorCompOpFunctorIso.hom.app X.toSSet = 𝟙 X.toSSet := by
  ext n x
  change SSet.opObjEquiv (X.dagger.app n
    (SSet.opObjEquiv (X.dagger.app n x))) = x
  exact X.involutive n.unop.len x

/-- The realized self-map from the actual dagger and reversal comparison. -/
def realizationInvolutionHom (X : DaggerSSet.{u}) :
    R.obj X.toSSet ⟶ R.obj X.toSSet :=
  R.map X.dagger ≫ realizationOppositeIso.hom.app X.toSSet

/-- Realizing the original dagger twice gives the identity continuous map. -/
theorem realizationInvolution_sq (X : DaggerSSet.{u}) :
    realizationInvolutionHom X ≫ realizationInvolutionHom X =
      𝟙 (R.obj X.toSSet) := by
  let A : SSet.{u} := X.toSSet
  let d : A ⟶ O.obj A := X.dagger
  let r := realizationOppositeIso.{u}
  have hn : r.hom.app A ≫ R.map d =
      R.map (O.map d) ≫ r.hom.app (O.obj A) := by
    simpa only [Functor.comp_map] using (r.hom.naturality d).symm
  change (R.map d ≫ r.hom.app A) ≫ (R.map d ≫ r.hom.app A) = 𝟙 _
  calc
    _ = R.map d ≫ (r.hom.app A ≫ R.map d) ≫ r.hom.app A := by
      simp only [Category.assoc]
    _ = R.map d ≫ (R.map (O.map d) ≫ r.hom.app (O.obj A)) ≫
          r.hom.app A := by rw [hn]
    _ = R.map d ≫ R.map (O.map d) ≫
          R.map (SSet.opFunctorCompOpFunctorIso.hom.app A) := by
      simp only [Category.assoc]
      rw [realizationOppositeIso_square A]
    _ = R.map (d ≫ O.map d ≫
          SSet.opFunctorCompOpFunctorIso.hom.app A) := by
      simp only [Functor.map_comp]
    _ = 𝟙 (R.obj A) := by
      rw [dagger_double X]
      exact CategoryTheory.Functor.map_id R X.toSSet

/-- Every actual dagger map commutes with the realized involutions. -/
theorem realizationInvolution_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    realizationInvolutionHom X ≫ R.map f.hom =
      R.map f.hom ≫ realizationInvolutionHom Y := by
  let r := realizationOppositeIso.{u}
  have hn : r.hom.app X.toSSet ≫ R.map f.hom =
      R.map (O.map f.hom) ≫ r.hom.app Y.toSSet := by
    simpa only [Functor.comp_map] using (r.hom.naturality f.hom).symm
  change (R.map X.dagger ≫ r.hom.app X.toSSet) ≫ R.map f.hom =
    R.map f.hom ≫ (R.map Y.dagger ≫ r.hom.app Y.toSSet)
  calc
    _ = R.map X.dagger ≫
          (r.hom.app X.toSSet ≫ R.map f.hom) := by
      simp only [Category.assoc]
    _ = R.map X.dagger ≫ R.map (O.map f.hom) ≫
          r.hom.app Y.toSSet := by rw [hn]
    _ = R.map (X.dagger ≫ O.map f.hom) ≫
          r.hom.app Y.toSSet := by
      simp only [Functor.map_comp, Category.assoc]
    _ = R.map (f.hom ≫ Y.dagger) ≫ r.hom.app Y.toSSet := by
      rw [← f.comm]
    _ = R.map f.hom ≫ (R.map Y.dagger ≫
          r.hom.app Y.toSSet) := by
      simp only [Functor.map_comp, Category.assoc]

end

end DaggerOriginalDaggerRealizationInvolution
