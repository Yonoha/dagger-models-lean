import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Full factorization and lifting transport through the original categorical equivalence

The functorial image of every counit is an arrow isomorphism, retaining the entire input
arrow. Both endpoint unit maps are included in the transported factorization. No target
factorization or model structure is assumed.
-/
set_option autoImplicit false
open CategoryTheory
universe u v a b
namespace DaggerOriginalEquivalenceFactorizationTransport
noncomputable section
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]

/-- The full counit retains any iso-invariant original arrow class. -/
theorem map_inverse_iff (E : C ≌ D) (P : MorphismProperty D) [P.RespectsIso]
    {X Y : D} (f : X ⟶ Y) : P (E.functor.map (E.inverse.map f)) ↔ P f :=
  P.arrow_mk_iso_iff (Arrow.isoMk (E.counitIso.app X) (E.counitIso.app Y)
    (E.counitIso.hom.naturality f).symm)

/-- Transport the entire factorization, including both original endpoint maps and classes. -/
def inverseImageFactorizationData (E : C ≌ D) (P Q : MorphismProperty D)
    [P.RespectsIso] [Q.RespectsIso] [P.HasFactorization Q] {X Y : C} (f : X ⟶ Y) :
    (P.inverseImage E.functor).MapFactorizationData (Q.inverseImage E.functor) f := by
  let d := MorphismProperty.factorizationData P Q (E.functor.map f)
  refine ⟨E.inverse.obj d.Z, (E.unitIso.app X).hom ≫ E.inverse.map d.i,
    E.inverse.map d.p ≫ (E.unitIso.app Y).inv, ?_, ?_, ?_⟩
  · calc
      ((E.unitIso.app X).hom ≫ E.inverse.map d.i) ≫
          (E.inverse.map d.p ≫ (E.unitIso.app Y).inv) =
          (E.unitIso.app X).hom ≫ E.inverse.map (d.i ≫ d.p) ≫
            (E.unitIso.app Y).inv := by simp only [Functor.map_comp, Category.assoc]
      _ = (E.unitIso.app X).hom ≫ (E.functor ⋙ E.inverse).map f ≫
          (E.unitIso.app Y).inv := by rw [d.fac]; rfl
      _ = f := NatIso.naturality_2 E.unitIso f
  · change P (E.functor.map ((E.unitIso.app X).hom ≫ E.inverse.map d.i))
    rw [E.functor.map_comp]
    exact MorphismProperty.RespectsIso.precomp P _ _ ((map_inverse_iff E P d.i).2 d.hi)
  · change Q (E.functor.map (E.inverse.map d.p ≫ (E.unitIso.app Y).inv))
    rw [E.functor.map_comp]
    exact MorphismProperty.RespectsIso.postcomp Q _ _ ((map_inverse_iff E Q d.p).2 d.hp)

/-- The actual inverse-image arrow classes inherit the full source factorization. -/
def inverseImageHasFactorization (E : C ≌ D) (P Q : MorphismProperty D)
    [P.RespectsIso] [Q.RespectsIso] [P.HasFactorization Q] :
    (P.inverseImage E.functor).HasFactorization (Q.inverseImage E.functor) :=
  ⟨fun f ↦ ⟨inverseImageFactorizationData E P Q f⟩⟩

/-- Reflection of native lifting uses the full unit arrow isomorphism. -/
theorem reflectsLifting (E : C ≌ D) {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    (h : HasLiftingProperty (E.functor.map i) (E.functor.map p)) :
    HasLiftingProperty i p := by
  have hr := (E.toAdjunction.hasLiftingProperty_iff i (E.functor.map p)).1 h
  exact (HasLiftingProperty.iff_of_arrow_iso_right i
    (Arrow.isoMk (E.unitIso.app X) (E.unitIso.app Y)
      (E.unitIso.hom.naturality p).symm)).2 hr

end
end DaggerOriginalEquivalenceFactorizationTransport
