import OriginalFixedObjectDaggerCofreeQuillen

/-!
# Exact projective classes on actions of original fixed-object strict groupoids

Weak equivalences and fibrations are defined on the unchanged underlying ordinary
arrow. The full original dagger/action counit identifies them with the inverse-image
dagger classes. Cofibrations are transported from the proved dagger model; their
canonical projective lifting characterization is established after model transport.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectGroupoidClasses
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictModel DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalFixedObjectStrictActionClasses
noncomputable section

/-- The projective weak class uses precisely the original underlying ordinary arrow. -/
def projectiveWeakEquivalences (O : Type u) :
    MorphismProperty (Action (FixedStrictGroupoids O) C2.{u}) :=
  (weakEquivalences (FixedStrictGroupoids O)).inverseImage
    (Action.forget (FixedStrictGroupoids O) C2.{u})

/-- The projective fibration class uses precisely the same underlying original arrow. -/
def projectiveFibrations (O : Type u) :
    MorphismProperty (Action (FixedStrictGroupoids O) C2.{u}) :=
  (fibrations (FixedStrictGroupoids O)).inverseImage
    (Action.forget (FixedStrictGroupoids O) C2.{u})

/-- Transport the original dagger cofibration class along the full inverse equivalence. -/
def projectiveCofibrations (O : Type u) :
    MorphismProperty (Action (FixedStrictGroupoids O) C2.{u}) :=
  (cofibrations (FixedStrictDaggerGroupoids O)).inverseImage
    (fixedDaggerActionEquivalence O).inverse

scoped instance projectiveWeakStructure (O : Type u) :
    CategoryWithWeakEquivalences (Action (FixedStrictGroupoids O) C2.{u}) :=
  ⟨projectiveWeakEquivalences O⟩

scoped instance projectiveFibStructure (O : Type u) :
    CategoryWithFibrations (Action (FixedStrictGroupoids O) C2.{u}) :=
  ⟨projectiveFibrations O⟩

scoped instance projectiveCofStructure (O : Type u) :
    CategoryWithCofibrations (Action (FixedStrictGroupoids O) C2.{u}) :=
  ⟨projectiveCofibrations O⟩

/-- The full original counit preserves every iso-invariant underlying arrow class. -/
theorem inverse_underlying_iff (O : Type u) (P : MorphismProperty (FixedStrictGroupoids O))
    [P.RespectsIso] {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    P ((fixedStrictDaggerForget O).map ((fixedDaggerActionEquivalence O).inverse.map p)) ↔
      P p.hom := by
  let E := fixedDaggerActionEquivalence O
  let V := Action.forget (FixedStrictGroupoids O) C2.{u}
  let eX := V.mapIso (E.counitIso.app X)
  let eY := V.mapIso (E.counitIso.app Y)
  have h := congrArg (fun k ↦ V.map k) (E.counitIso.hom.naturality p)
  change (fixedStrictDaggerForget O).map (E.inverse.map p) ≫ eY.hom = eX.hom ≫ p.hom at h
  exact P.arrow_mk_iso_iff (Arrow.isoMk eX eY h.symm)

/-- Forgetting only the dagger detects the exact original weak-equivalence class. -/
theorem forget_weakEquivalence_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : WeakEquivalence F ↔
      WeakEquivalence ((fixedStrictDaggerForget O).map F) := by
  rw [strictDagger_weakEquivalence_iff, strict_weakEquivalence_iff]
  rfl

/-- The intended underlying projective weak class is exactly the transported dagger class. -/
theorem projectiveWeak_eq_inverse (O : Type u) :
    projectiveWeakEquivalences O =
      (weakEquivalences (FixedStrictDaggerGroupoids O)).inverseImage
        (fixedDaggerActionEquivalence O).inverse := by
  funext X Y p
  apply propext
  change weakEquivalences (FixedStrictGroupoids O) p.hom ↔
    weakEquivalences (FixedStrictDaggerGroupoids O)
      ((fixedDaggerActionEquivalence O).inverse.map p)
  rw [← weakEquivalence_iff, ← weakEquivalence_iff, forget_weakEquivalence_iff,
    weakEquivalence_iff, weakEquivalence_iff]
  exact (inverse_underlying_iff O (weakEquivalences (FixedStrictGroupoids O)) p).symm

/-- The intended underlying projective fibration class is exactly the transported dagger class. -/
theorem projectiveFib_eq_inverse (O : Type u) :
    projectiveFibrations O =
      (fibrations (FixedStrictDaggerGroupoids O)).inverseImage
        (fixedDaggerActionEquivalence O).inverse := by
  funext X Y p
  apply propext
  change fibrations (FixedStrictGroupoids O) p.hom ↔
    fibrations (FixedStrictDaggerGroupoids O)
      ((fixedDaggerActionEquivalence O).inverse.map p)
  rw [← fibration_iff, ← fibration_iff,
    DaggerOriginalFixedObjectDaggerCofreeQuillen.forget_fibration_iff,
    fibration_iff, fibration_iff]
  exact (inverse_underlying_iff O (fibrations (FixedStrictGroupoids O)) p).symm

open scoped DaggerOriginalFixedObjectStrictActionClasses

/-- Native projective weak equivalences are precisely underlying original weak equivalences. -/
theorem weakEquivalence_iff_underlying {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    WeakEquivalence p ↔ WeakEquivalence p.hom := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  rfl

/-- Native projective fibrations are precisely underlying original fibrations. -/
theorem fibration_iff_underlying {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    Fibration p ↔ Fibration p.hom := by
  rw [fibration_iff, fibration_iff]
  rfl

end
end DaggerOriginalFixedObjectStrictActionClasses
