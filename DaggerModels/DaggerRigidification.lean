import DaggerModels.RigidificationOpposite
import DaggerModels.RigidificationVertices
import DaggerModels.DaggerOppositeHom
import DaggerModels.SimplicialSet

/-!
# The actual dagger rigidification left functor

The original rigidification object and every original enriched map are retained.
The dagger is F(dagger_X) followed by the original ordinary-opposite comparison.
Canonical unit-based vertices prove fixing of every actual object. Existing opposite
adapters bundle the full hom-level dagger and every commuting enriched functor.
This module does not construct the lifted adjunction or the free-functor comparison.
-/

open CategoryTheory Opposite
open scoped Simplicial

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerRigidification

open RigidificationVertices

private abbrev F : SSet.{u} ⥤ SimplicialCat.{u, u} := rigidification
private abbrev O : SimplicialCat.{u, u} ⥤ SimplicialCat.{u, u} :=
  SimplicialCat.oppositeFunctor
private abbrev S : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor
private abbrev χ : S ⋙ F.{u} ≅ F ⋙ O := RigidificationOpposite.rigidificationOppositeIso

/-- The ordinary comparison has the canonical unit-based vertex formula. -/
theorem chi_vertex (X : SSet.{u}) (x : (S.obj X).obj (op ⦋0⦌)) :
    (χ.hom.app X).obj (vertexEquiv (S.obj X) x) =
      op (vertexEquiv X (SSet.opObjEquiv x)) := by
  have h := congrArg (fun g : S.obj X ⟶ coherentNerve.obj (O.obj (F.obj X)) ↦
    (g.app (op ⦋0⦌) x).down.obj NerveVertices.zeroObject)
      (RigidificationOpposite.rigidificationOpposite_unit X)
  change (χ.hom.app X).obj (vertexEquiv (S.obj X) x) =
    op (((rigidificationCoherentNerveAdjunction.unit.app X).app (op ⦋0⦌)
      (SSet.opObjEquiv x)).down.obj
        (ThickeningReversal.reverseObject ⦋0⦌ NerveVertices.zeroObject)) at h
  rw [NerveVertices.zeroObject_eq
    (ThickeningReversal.reverseObject ⦋0⦌ NerveVertices.zeroObject)] at h
  exact h

private theorem simplicial_dagger_square (X : DaggerSSet.{u}) :
    X.dagger ≫ S.map X.dagger ≫ SSet.opFunctorCompOpFunctorIso.hom.app X.toSSet =
      𝟙 X.toSSet := by
  ext n x
  exact X.involutive n.unop.len x

/-- The full enriched opposite dagger on the original rigidification. -/
def daggerToOpposite (X : DaggerSSet.{u}) : F.obj X.toSSet ⟶ O.obj (F.obj X.toSSet) :=
  F.map X.dagger ≫ χ.hom.app X.toSSet

/-- The constructed dagger fixes every actual rigidification object. -/
theorem daggerToOpposite_obj (X : DaggerSSet.{u}) (i : (F.obj X.toSSet).Obj) :
    (daggerToOpposite X).obj i = op i := by
  obtain ⟨x, rfl⟩ := (vertexEquiv X.toSSet).surjective i
  change (χ.hom.app X.toSSet).obj ((F.map X.dagger).obj (vertexEquiv X.toSSet x)) = _
  rw [vertexEquiv_naturality, chi_vertex, X.fixedVertices]

/-- The actual enriched dagger squares to identity through the actual double opposite. -/
theorem daggerToOpposite_square (X : DaggerSSet.{u}) :
    daggerToOpposite X ≫ O.map (daggerToOpposite X) ≫
        SimplicialCat.doubleOppositeHom (F.obj X.toSSet) = 𝟙 (F.obj X.toSSet) := by
  have hn : F.map (S.map X.dagger) ≫ χ.hom.app (S.obj X.toSSet) =
      χ.hom.app X.toSSet ≫ O.map (F.map X.dagger) := χ.hom.naturality X.dagger
  unfold daggerToOpposite
  rw [CategoryTheory.Functor.map_comp]
  calc
    _ = F.map X.dagger ≫ F.map (S.map X.dagger) ≫
        (χ.hom.app (S.obj X.toSSet) ≫ O.map (χ.hom.app X.toSSet) ≫
          (SimplicialCat.doubleOppositeIso (F.obj X.toSSet)).hom) := by
      simpa only [Category.assoc] using congrArg (fun k ↦ F.map X.dagger ≫ k ≫
        O.map (χ.hom.app X.toSSet) ≫
        (SimplicialCat.doubleOppositeIso (F.obj X.toSSet)).hom) hn.symm
    _ = F.map X.dagger ≫ F.map (S.map X.dagger) ≫
        F.map (SSet.opFunctorCompOpFunctorIso.hom.app X.toSSet) := by
      rw [RigidificationOpposite.rigidificationOppositeIso_coherence]
    _ = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        simplicial_dagger_square]
      exact F.map_id X.toSSet

/-- Bundle the existing F(X), retaining its objects and all enriched hom spaces. -/
def obj (X : DaggerSSet.{u}) : DaggerSimplicialCat.{u, u} where
  toSimplicialCat := F.obj X.toSSet
  daggerStructure := DaggerSimplicialStructure.ofOppositeFunctor (F.obj X.toSSet)
    (daggerToOpposite X) (daggerToOpposite_obj X) (daggerToOpposite_square X)

/-- The existing adapter recovers the entire specified enriched dagger functor. -/
theorem obj_daggerFunctor (X : DaggerSSet.{u}) :
    DaggerSimplicialCat.daggerNatural.app (obj X) = daggerToOpposite X :=
  DaggerSimplicialStructure.ofOppositeFunctor_daggerFunctor (F.obj X.toSSet)
    (daggerToOpposite X) (daggerToOpposite_obj X) (daggerToOpposite_square X)

/-- Every original F-map commutes with the actual full opposite daggers. -/
theorem map_commuting {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    F.map f.hom ≫ daggerToOpposite Y = daggerToOpposite X ≫ O.map (F.map f.hom) := by
  unfold daggerToOpposite
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, f.comm,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn : F.map (S.map f.hom) ≫ χ.hom.app Y.toSSet =
      χ.hom.app X.toSSet ≫ O.map (F.map f.hom) := χ.hom.naturality f.hom
  rw [hn, Category.assoc]

/-- Lift the literal original enriched map using the existing commuting-opposite adapter. -/
def map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  DaggerSimplicialCat.Hom.ofCommutingOpposite (F.map f.hom) (by
    rw [obj_daggerFunctor, obj_daggerFunctor]
    exact map_commuting f)

/-- The actual dagger rigidification on all objects and all dagger simplicial maps. -/
def daggerRigidification : DaggerSSet.{u} ⥤ DaggerSimplicialCat.{u, u} where
  obj := obj
  map := map
  map_id X := by
    apply DaggerSimplicialCat.Hom.ext
    exact F.map_id X.toSSet
  map_comp f g := by
    apply DaggerSimplicialCat.Hom.ext
    exact F.map_comp f.hom g.hom

/-- Forgetting retains the entire original rigidification functor literally. -/
theorem daggerRigidification_forget :
    daggerRigidification.{u} ⋙ DaggerSimplicialCat.forget = DaggerSSet.forget ⋙ rigidification :=
  rfl

end DaggerModels.OrdinaryRigidification.DaggerRigidification
