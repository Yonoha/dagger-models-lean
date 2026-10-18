import OriginalC2BinaryCofreeAdjunction
import OriginalFixedObjectTrivialFibrationProducts
import OriginalFixedObjectStrictDaggerModel

/-!
# The actual dagger forget/cofree adjunction and canonical cofibration transfer

Compose the original dagger/action equivalence with the binary C2 adjunction.
The counit compares the full underlying cofree arrows to the original product maps.
Native adjunction lifting then transfers precisely the specified cofibrations.
No ordinary ModelCategory or ordinary factorization premise is used.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
open DaggerOriginalFixedObjectTrivialFibrationProducts
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
universe u
namespace DaggerOriginalFixedObjectDaggerCofreeTransfer
noncomputable section

/-- The original cofree dagger retains the complete native C2 action via the equivalence. -/
def daggerCofree (O : Type u) : FixedStrictGroupoids O ⥤ FixedStrictDaggerGroupoids O :=
  DaggerOriginalC2BinaryCofreeAdjunction.cofreeFunctor (FixedStrictGroupoids O) ⋙
    (fixedDaggerActionEquivalence O).inverse

/-- Forgetting the original dagger is left adjoint to the full binary cofree construction. -/
def daggerForgetCofreeAdjunction (O : Type u) :
    fixedStrictDaggerForget O ⊣ daggerCofree O :=
  (fixedDaggerActionEquivalence O).toAdjunction.comp
    (DaggerOriginalC2BinaryCofreeAdjunction.forgetCofreeAdjunction (FixedStrictGroupoids O))

/-- Forgetting only the dagger preserves and detects the exact original trivial fibrations. -/
theorem forget_trivialFibration_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : trivialFibrations (FixedStrictDaggerGroupoids O) F ↔
      trivialFibrations (FixedStrictGroupoids O) ((fixedStrictDaggerForget O).map F) := by
  rw [mem_trivialFibrations_iff, mem_trivialFibrations_iff,
    strictDagger_fibration_iff, strictDagger_weakEquivalence_iff,
    strict_fibration_iff, strict_weakEquivalence_iff]
  rfl

/-- The cofree functor preserves the exact full Homwise trivial-fibration class. -/
theorem daggerCofree_trivialFibration {O : Type u} {C D : FixedStrictGroupoids O}
    (F : C ⟶ D) (hF : trivialFibrations (FixedStrictGroupoids O) F) :
    trivialFibrations (FixedStrictDaggerGroupoids O) ((daggerCofree O).map F) := by
  apply (forget_trivialFibration_iff _).2
  let E := fixedDaggerActionEquivalence O
  let V := Action.forget (FixedStrictGroupoids O) C2.{u}
  let R := DaggerOriginalC2BinaryCofreeAdjunction.cofreeFunctor (FixedStrictGroupoids O)
  let eC := V.mapIso (E.counitIso.app (R.obj C))
  let eD := V.mapIso (E.counitIso.app (R.obj D))
  have hc := congrArg (fun k ↦ V.map k) (E.counitIso.hom.naturality (R.map F))
  change (fixedStrictDaggerForget O).map ((daggerCofree O).map F) ≫ eD.hom =
    eC.hom ≫ prod.map F F at hc
  exact ((trivialFibrations (FixedStrictGroupoids O)).arrow_mk_iso_iff
    (Arrow.isoMk eC eD hc.symm)).2 (strict_prodMap_trivialFibration F F hF hF)

/-- The full original dagger cofibrations forget to the exact ordinary canonical LLP class. -/
theorem forget_cofibration {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) (hF : strictDaggerCofibrations O F) :
    strictCofibrations O ((fixedStrictDaggerForget O).map F) := by
  intro X Y p hp
  apply ((daggerForgetCofreeAdjunction O).hasLiftingProperty_iff F p).2
  exact hF _ (daggerCofree_trivialFibration p hp)

end
end DaggerOriginalFixedObjectDaggerCofreeTransfer
