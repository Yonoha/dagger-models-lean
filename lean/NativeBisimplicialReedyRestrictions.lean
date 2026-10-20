import NativeBisimplicialRelativeLifting

/-! Reedy boundary fibrations give every monomorphism restriction, including partial matching. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialRelativeLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialReedyRestrictions
noncomputable section

theorem transverse_restriction_trivialFibration {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) {A B : SSet.{u}} (j : A ⟶ B)
    (hj : SSet.modelCategoryQuillen.J j) :
    trivialFibrations SSet.{u} (relativeRestriction j (flipMap f)) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro K L i hi
  obtain ⟨m⟩ := hi
  apply (relative_lifting_iff (SSet.boundary m).ι j f).mp
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp (hf m) j hj

theorem restriction_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) {K L : SSet.{u}} (i : K ⟶ L) [Mono i] :
    Fibration (relativeRestriction i f) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B j hj
  apply (relative_lifting_iff i j f).mpr
  have ht := transverse_restriction_trivialFibration f hf j hj
  have : Fibration (relativeRestriction j (flipMap f)) :=
    ((mem_trivialFibrations_iff _).mp ht).1
  have : WeakEquivalence (relativeRestriction j (flipMap f)) :=
    ((mem_trivialFibrations_iff _).mp ht).2
  have : Cofibration i := (SSet.modelCategoryQuillen.cofibration_iff i).mpr inferInstance
  infer_instance

theorem horn_matching_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ReedyFibration f) (m : ℕ) (k : Fin (m + 1)) :
    Fibration (relativeRestriction (SSet.horn m k).ι f) :=
  restriction_fibration f hf _

theorem reedy_iff_all_mono_restrictions {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    ReedyFibration f ↔ ∀ (K L : SSet.{u}) (i : K ⟶ L) [Mono i],
      Fibration (relativeRestriction i f) := by
  constructor
  · intro hf K L i hi
    exact restriction_fibration f hf i
  · intro hf m
    exact hf _ _ (SSet.boundary m).ι

end
end DaggerNativeBisimplicialReedyRestrictions
