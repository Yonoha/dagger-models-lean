import DaggerModels.NerveOpposite
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Rigidification and ordinary opposite, with the original adjunction mate

The comparison is the inverse mate of the existing nerve comparison under the actual
uncomposed rigidification/coherent-nerve adjunction. Its invertibility is proved from
the concrete involutive coherence, rather than assumed for a general mate of an iso.
All original functors and the common arbitrary universe are retained. Vertex fixing,
the dagger left functor, and the lifted adjunction are outside this module.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.RigidificationOpposite

private abbrev F : SSet.{u} ⥤ SimplicialCat.{u, u} := rigidification
private abbrev N : SimplicialCat.{u, u} ⥤ SSet.{u} := coherentNerve
private abbrev O : SimplicialCat.{u, u} ⥤ SimplicialCat.{u, u} :=
  SimplicialCat.oppositeFunctor
private abbrev S : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor
private abbrev A : F.{u} ⊣ N := rigidificationCoherentNerveAdjunction
private abbrev Λ : O ⋙ N.{u} ≅ N ⋙ S := NerveOpposite.coherentNerveOppositeIso

/-- The comparison map is the original adjunction's inverse mate of lambda inverse. -/
def rigidificationOppositeHom : S ⋙ F ⟶ F ⋙ O :=
  ((mateEquiv A A).symm Λ.inv).natTrans

/-- The original unit satisfies the literal inverse-mate equation. -/
theorem rigidificationOpposite_unit (X : SSet.{u}) :
    A.unit.app (S.obj X) ≫ N.map (rigidificationOppositeHom.app X) =
      S.map (A.unit.app X) ≫ Λ.inv.app (F.obj X) :=
  (unit_mateEquiv_symm A A Λ.inv X).symm

/-- Ordinary adjunction compatibility holds for every full enriched target functor. -/
theorem rigidificationOpposite_mate (X : SSet.{u}) (C : SimplicialCat.{u, u})
    (f : F.obj X ⟶ C) :
    A.homEquiv (S.obj X) (O.obj C) (rigidificationOppositeHom.app X ≫ O.map f) =
      S.map (A.homEquiv X C f) ≫ Λ.inv.app C := by
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, rigidificationOpposite_unit, Category.assoc]
  have h : S.map (N.map f) ≫ Λ.inv.app C = Λ.inv.app (F.obj X) ≫ N.map (O.map f) :=
    Λ.inv.naturality f
  rw [← h, Category.assoc]

private theorem inverse_nerve_coherence (C : SimplicialCat.{u, u}) :
    S.map (Λ.inv.app C) ≫ Λ.inv.app (O.obj C) ≫
        N.map (SimplicialCat.doubleOppositeIso C).hom =
      SSet.opFunctorCompOpFunctorIso.hom.app (N.obj C) := by
  let e : N.obj (O.obj (O.obj C)) ≅ S.obj (S.obj (N.obj C)) :=
    Λ.app (O.obj C) ≪≫ S.mapIso (Λ.app C)
  have h : e.hom ≫ SSet.opFunctorCompOpFunctorIso.hom.app (N.obj C) =
      N.map (SimplicialCat.doubleOppositeIso C).hom :=
    NerveOpposite.coherentNerveOpposite_coherence C
  change e.inv ≫ N.map (SimplicialCat.doubleOppositeIso C).hom = _
  rw [← h]
  simp

/-- The mate comparison has the fully typed ordinary-opposite involution coherence. -/
theorem rigidificationOppositeHom_coherence (X : SSet.{u}) :
    rigidificationOppositeHom.app (S.obj X) ≫ O.map (rigidificationOppositeHom.app X) ≫
        (SimplicialCat.doubleOppositeIso (F.obj X)).hom =
      F.map (SSet.opFunctorCompOpFunctorIso.hom.app X) := by
  apply (A.homEquiv (S.obj (S.obj X)) (F.obj X)).injective
  rw [← Category.assoc, A.homEquiv_naturality_right,
    rigidificationOpposite_mate, Adjunction.homEquiv_unit,
    rigidificationOpposite_unit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, CategoryTheory.Functor.comp_obj]
  have hc := congrArg (fun k ↦ S.map (S.map (A.unit.app X)) ≫ k)
    (inverse_nerve_coherence (F.obj X))
  dsimp only at hc
  rw [hc]
  have h : S.map (S.map (A.unit.app X)) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (N.obj (F.obj X)) =
      SSet.opFunctorCompOpFunctorIso.hom.app X ≫ A.unit.app X :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality (A.unit.app X)
  rw [h]
  simpa only [Category.comp_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    using (A.homEquiv_naturality_left
      (SSet.opFunctorCompOpFunctorIso.hom.app X) (𝟙 (F.obj X))).symm

private theorem epsilon_op_inv (X : SSet.{u}) :
    S.map (SSet.opFunctorCompOpFunctorIso.inv.app X) =
      SSet.opFunctorCompOpFunctorIso.inv.app (S.obj X) := by
  ext n P
  rfl

private theorem delta_op_hom (C : SimplicialCat.{u, u}) :
    O.map (SimplicialCat.doubleOppositeIso C).hom =
      (SimplicialCat.doubleOppositeIso (O.obj C)).hom := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

/-- The inverse uses the actual epsilon inverse, opposite comparison, and delta hom. -/
def rigidificationOppositeInvApp (X : SSet.{u}) : (F ⋙ O).obj X ⟶ (S ⋙ F).obj X :=
  O.map (F.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
    O.map (rigidificationOppositeHom.app (S.obj X)) ≫
    (SimplicialCat.doubleOppositeIso (F.obj (S.obj X))).hom

/-- The prescribed component inverse is a right inverse of the mate comparison. -/
theorem rigidificationOpposite_hom_inv (X : SSet.{u}) :
    rigidificationOppositeHom.app X ≫ rigidificationOppositeInvApp X =
      𝟙 ((S ⋙ F).obj X) := by
  have hn : F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
      rigidificationOppositeHom.app (S.obj (S.obj X)) =
      rigidificationOppositeHom.app X ≫
        O.map (F.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) :=
    rigidificationOppositeHom.naturality (SSet.opFunctorCompOpFunctorIso.inv.app X)
  unfold rigidificationOppositeInvApp
  calc
    _ = F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
        (rigidificationOppositeHom.app (S.obj (S.obj X)) ≫
          O.map (rigidificationOppositeHom.app (S.obj X)) ≫
          (SimplicialCat.doubleOppositeIso (F.obj (S.obj X))).hom) := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫
        O.map (rigidificationOppositeHom.app (S.obj X)) ≫
        (SimplicialCat.doubleOppositeIso (F.obj (S.obj X))).hom) hn.symm
    _ = F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
        F.map (SSet.opFunctorCompOpFunctorIso.hom.app (S.obj X)) := by
      rw [rigidificationOppositeHom_coherence (S.obj X)]
    _ = 𝟙 _ := by
      rw [epsilon_op_inv, ← CategoryTheory.Functor.map_comp,
        SSet.opFunctorCompOpFunctorIso.inv_hom_id_app]
      exact F.map_id (S.obj X)

/-- The same prescribed component inverse is also a left inverse. -/
theorem rigidificationOpposite_inv_hom (X : SSet.{u}) :
    rigidificationOppositeInvApp X ≫ rigidificationOppositeHom.app X =
      𝟙 ((F ⋙ O).obj X) := by
  have hn : O.map (O.map (rigidificationOppositeHom.app X)) ≫
      (SimplicialCat.doubleOppositeIso (O.obj (F.obj X))).hom =
      (SimplicialCat.doubleOppositeIso (F.obj (S.obj X))).hom ≫
        rigidificationOppositeHom.app X :=
    SimplicialCat.doubleOppositeNatIso.hom.naturality (rigidificationOppositeHom.app X)
  unfold rigidificationOppositeInvApp
  rw [Category.assoc, Category.assoc, ← hn, ← delta_op_hom]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [rigidificationOppositeHom_coherence X]
  rw [← CategoryTheory.Functor.map_comp, SSet.opFunctorCompOpFunctorIso.inv_hom_id_app]
  exact (congrArg O.map (F.map_id X)).trans (O.map_id (F.obj X))

/-- The original rigidification is naturally isomorphic to its opposite comparison. -/
def rigidificationOppositeIso : S ⋙ F ≅ F ⋙ O :=
  NatIso.ofComponents (fun X ↦
    { hom := rigidificationOppositeHom.app X
      inv := rigidificationOppositeInvApp X
      hom_inv_id := rigidificationOpposite_hom_inv X
      inv_hom_id := rigidificationOpposite_inv_hom X })
    (fun f ↦ rigidificationOppositeHom.naturality f)

/-- The constructed isomorphism has the original uncomposed adjunction's mate formula. -/
theorem rigidificationOppositeIso_mate (X : SSet.{u}) (C : SimplicialCat.{u, u})
    (f : F.obj X ⟶ C) :
    A.homEquiv (S.obj X) (O.obj C) (rigidificationOppositeIso.hom.app X ≫ O.map f) =
      S.map (A.homEquiv X C f) ≫ Λ.inv.app C :=
  rigidificationOpposite_mate X C f

/-- The full natural isomorphism has the actual epsilon/delta involution coherence. -/
theorem rigidificationOppositeIso_coherence (X : SSet.{u}) :
    rigidificationOppositeIso.hom.app (S.obj X) ≫
        O.map (rigidificationOppositeIso.hom.app X) ≫
        (SimplicialCat.doubleOppositeIso (F.obj X)).hom =
      F.map (SSet.opFunctorCompOpFunctorIso.hom.app X) :=
  rigidificationOppositeHom_coherence X

end DaggerModels.OrdinaryRigidification.RigidificationOpposite
