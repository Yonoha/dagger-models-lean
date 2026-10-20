import NativeNerveOppositeIso
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Native homotopy category and simplicial opposite

Reuse the proven involutive adjunction-mate construction with Mathlib's actual
ho/nerve adjunction, native Cat opposite, and the exact whole native nerve reversal.
The comparison retains the actual naturality and both inverse equations.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerNativeHoOppositeIso

private abbrev F : SSet.{u} ⥤ Cat.{u, u} := SSet.hoFunctor
private abbrev N : Cat.{u, u} ⥤ SSet.{u} := nerveFunctor
private abbrev O : Cat.{u, u} ⥤ Cat.{u, u} :=
  Cat.opFunctor
private abbrev S : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor
private abbrev A : F.{u} ⊣ N := nerveAdjunction
private abbrev Λ : O ⋙ N.{u} ≅ N ⋙ S := DaggerNativeNerveOppositeIso.nerveOppositeNatIso.symm

/-- The comparison map is the native adjunction's inverse mate of lambda inverse. -/
def hoOppositeHom : S ⋙ F ⟶ F ⋙ O :=
  ((mateEquiv A A).symm Λ.inv).natTrans

/-- The native unit satisfies the literal inverse-mate equation. -/
theorem hoOpposite_unit (X : SSet.{u}) :
    A.unit.app (S.obj X) ≫ N.map (hoOppositeHom.app X) =
      S.map (A.unit.app X) ≫ Λ.inv.app (F.obj X) :=
  (unit_mateEquiv_symm A A Λ.inv X).symm

/-- Ordinary adjunction compatibility holds for every actual category morphism. -/
theorem hoOpposite_mate (X : SSet.{u}) (C : Cat.{u, u})
    (f : F.obj X ⟶ C) :
    A.homEquiv (S.obj X) (O.obj C) (hoOppositeHom.app X ≫ O.map f) =
      S.map (A.homEquiv X C f) ≫ Λ.inv.app C := by
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, hoOpposite_unit, Category.assoc]
  have h : S.map (N.map f) ≫ Λ.inv.app C = Λ.inv.app (F.obj X) ≫ N.map (O.map f) :=
    Λ.inv.naturality f
  rw [← h, Category.assoc]

private theorem inverse_nerve_coherence (C : Cat.{u, u}) :
    S.map (Λ.inv.app C) ≫ Λ.inv.app (O.obj C) ≫
        N.map (Cat.opFunctorInvolutive.app C).hom =
      SSet.opFunctorCompOpFunctorIso.hom.app (N.obj C) :=
  DaggerNativeNerveOppositeIso.nerveOppositeNatIso_coherence C

/-- The mate comparison has the fully typed native ordinary-opposite involution coherence. -/
theorem hoOppositeHom_coherence (X : SSet.{u}) :
    hoOppositeHom.app (S.obj X) ≫ O.map (hoOppositeHom.app X) ≫
        (Cat.opFunctorInvolutive.app (F.obj X)).hom =
      F.map (SSet.opFunctorCompOpFunctorIso.hom.app X) := by
  apply (A.homEquiv (S.obj (S.obj X)) (F.obj X)).injective
  rw [← Category.assoc, A.homEquiv_naturality_right,
    hoOpposite_mate, Adjunction.homEquiv_unit,
    hoOpposite_unit]
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

private theorem delta_op_hom (C : Cat.{u, u}) :
    O.map (Cat.opFunctorInvolutive.app C).hom =
      (Cat.opFunctorInvolutive.app (O.obj C)).hom := rfl

/-- The inverse uses the actual epsilon inverse, opposite comparison, and delta hom. -/
def hoOppositeInvApp (X : SSet.{u}) : (F ⋙ O).obj X ⟶ (S ⋙ F).obj X :=
  O.map (F.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
    O.map (hoOppositeHom.app (S.obj X)) ≫
    (Cat.opFunctorInvolutive.app (F.obj (S.obj X))).hom

/-- The prescribed component inverse is a right inverse of the mate comparison. -/
theorem hoOpposite_hom_inv (X : SSet.{u}) :
    hoOppositeHom.app X ≫ hoOppositeInvApp X =
      𝟙 ((S ⋙ F).obj X) := by
  have hn : F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
      hoOppositeHom.app (S.obj (S.obj X)) =
      hoOppositeHom.app X ≫
        O.map (F.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) :=
    hoOppositeHom.naturality (SSet.opFunctorCompOpFunctorIso.inv.app X)
  unfold hoOppositeInvApp
  calc
    _ = F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
        (hoOppositeHom.app (S.obj (S.obj X)) ≫
          O.map (hoOppositeHom.app (S.obj X)) ≫
          (Cat.opFunctorInvolutive.app (F.obj (S.obj X))).hom) := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫
        O.map (hoOppositeHom.app (S.obj X)) ≫
        (Cat.opFunctorInvolutive.app (F.obj (S.obj X))).hom) hn.symm
    _ = F.map (S.map (SSet.opFunctorCompOpFunctorIso.inv.app X)) ≫
        F.map (SSet.opFunctorCompOpFunctorIso.hom.app (S.obj X)) := by
      rw [hoOppositeHom_coherence (S.obj X)]
    _ = 𝟙 _ := by
      rw [epsilon_op_inv, ← CategoryTheory.Functor.map_comp,
        SSet.opFunctorCompOpFunctorIso.inv_hom_id_app]
      exact F.map_id (S.obj X)

/-- The same prescribed component inverse is also a left inverse. -/
theorem hoOpposite_inv_hom (X : SSet.{u}) :
    hoOppositeInvApp X ≫ hoOppositeHom.app X =
      𝟙 ((F ⋙ O).obj X) := by
  have hn : O.map (O.map (hoOppositeHom.app X)) ≫
      (Cat.opFunctorInvolutive.app (O.obj (F.obj X))).hom =
      (Cat.opFunctorInvolutive.app (F.obj (S.obj X))).hom ≫
        hoOppositeHom.app X :=
    Cat.opFunctorInvolutive.hom.naturality (hoOppositeHom.app X)
  unfold hoOppositeInvApp
  rw [Category.assoc, Category.assoc, ← hn, ← delta_op_hom]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [hoOppositeHom_coherence X]
  rw [← CategoryTheory.Functor.map_comp, SSet.opFunctorCompOpFunctorIso.inv_hom_id_app]
  exact (congrArg O.map (F.map_id X)).trans (O.map_id (F.obj X))

/-- The native homotopy-category functor is naturally isomorphic to its opposite comparison. -/
def hoOppositeIso : S ⋙ F ≅ F ⋙ O :=
  NatIso.ofComponents (fun X ↦
    { hom := hoOppositeHom.app X
      inv := hoOppositeInvApp X
      hom_inv_id := hoOpposite_hom_inv X
      inv_hom_id := hoOpposite_inv_hom X })
    (fun f ↦ hoOppositeHom.naturality f)

/-- The constructed isomorphism has the native uncomposed adjunction's mate formula. -/
theorem hoOppositeIso_mate (X : SSet.{u}) (C : Cat.{u, u})
    (f : F.obj X ⟶ C) :
    A.homEquiv (S.obj X) (O.obj C) (hoOppositeIso.hom.app X ≫ O.map f) =
      S.map (A.homEquiv X C f) ≫ Λ.inv.app C :=
  hoOpposite_mate X C f

/-- The full natural isomorphism has the actual epsilon/delta involution coherence. -/
theorem hoOppositeIso_coherence (X : SSet.{u}) :
    hoOppositeIso.hom.app (S.obj X) ≫
        O.map (hoOppositeIso.hom.app X) ≫
        (Cat.opFunctorInvolutive.app (F.obj X)).hom =
      F.map (SSet.opFunctorCompOpFunctorIso.hom.app X) :=
  hoOppositeHom_coherence X

end DaggerNativeHoOppositeIso
