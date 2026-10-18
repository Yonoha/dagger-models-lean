import ActualFreeAntiJoyalMappingWeak
import ActualAntiForgetAdjointTriple
import ActualAntiJoyalFirstFactorization
import NativeJoyalFirstFactorization

/-!
# Actual free and cofree adjunctions on the fixed Joyal lifting classes

The complete normal and literal mapping-weak classes are retained. Free anti-involutive
trivial cofibrations test the underlying ordinary fibration candidate exactly. Thus the
actual anti-involutive candidate forgets to an ordinary candidate. The cofree functor also
preserves the candidate, by the other adjunction and underlying normality. No ordinary or
DCH Joyal model is assumed. The converse creation statement for arbitrary anti-involutive
maps is not asserted here.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiForgetAdjointTriple DaggerActualAntiJoyalMappingWeakProperties
open DaggerActualFreeAntiJoyalMappingWeak
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerActualAntiJoyalAdjointLifting
noncomputable section

/-- Every full original normal and mapping-weak map has a mono and mapping-weak underlying map. -/
theorem forget_normal_weak {X Y : AntiInvolutiveSSet.{u}} (i : X ⟶ Y)
    (hi : (normalMonos ⊓ weakEquivalences) i) :
    (MorphismProperty.monomorphisms SSet ⊓ weakCategoricalEquivalences) i.hom :=
  ⟨hi.1.1, hi.2⟩

/-- The exact ordinary candidate is recognized by all actual free normal-weak lifting tests. -/
theorem underlying_candidate_iff_free_lifting {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    DaggerNativeJoyalFirstFactorization.candidateFibrations p.hom ↔
      ∀ {A B : SSet.{u}} (i : A ⟶ B), Mono i → weakCategoricalEquivalences i →
        HasLiftingProperty (freeAnti.map i) p := by
  constructor
  · intro hp A B i hm hw
    exact (freeAntiAdjunction.hasLiftingProperty_iff i p).2 (hp i ⟨hm, hw⟩)
  · intro hp A B i hi
    exact (freeAntiAdjunction.hasLiftingProperty_iff i p).1 (hp i hi.1 hi.2)

/-- Forgetting an actual fibration candidate gives the full original ordinary candidate. -/
theorem candidate_forget {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y)
    (hp : DaggerActualAntiJoyalFirstFactorization.candidateFibrations p) :
    DaggerNativeJoyalFirstFactorization.candidateFibrations p.hom := by
  apply (underlying_candidate_iff_free_lifting p).2
  intro A B i hm hw
  haveI := hm
  exact hp (freeAnti.map i) (freeAnti_map_normal_and_weak i hw)

/-- Any actual right adjoint of the original forgetful functor preserves the candidate. -/
theorem candidate_rightAdjoint (R : SSet.{u} ⥤ AntiInvolutiveSSet.{u})
    (adj : antiForget ⊣ R) {A B : SSet.{u}} (p : A ⟶ B)
    (hp : DaggerNativeJoyalFirstFactorization.candidateFibrations p) :
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations (R.map p) := by
  intro X Y i hi
  exact (adj.hasLiftingProperty_iff i p).1 (hp i.hom (forget_normal_weak i hi))

/-- The actual right Kan extension preserves every ordinary fibration candidate. -/
theorem candidate_cofree {A B : SSet.{u}} (p : A ⟶ B)
    (hp : DaggerNativeJoyalFirstFactorization.candidateFibrations p) :
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations (cofreeAnti.map p) :=
  candidate_rightAdjoint cofreeAnti cofreeAntiAdjunction p hp

/-- The entire normal-right class is precisely the underlying ordinary mono-right class. -/
theorem normal_rlp_iff_underlying_mono_rlp {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    normalMonos.rlp p ↔ (MorphismProperty.monomorphisms SSet).rlp p.hom := by
  constructor
  · intro hp
    exact DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_monomorphisms p.hom
      ((DaggerActualAntiNormalBoundaryLifting.normal_rlp_iff_underlying_boundary p).1 hp)
  · intro hp
    apply (DaggerActualAntiNormalBoundaryLifting.normal_rlp_iff_underlying_boundary p).2
    intro n
    exact hp (SSet.boundary n).ι (show Mono (SSet.boundary n).ι from inferInstance)

/-- The cofree functor preserves the full ordinary mono-right class as normal-right maps. -/
theorem normal_rlp_cofree {A B : SSet.{u}} (p : A ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet).rlp p) :
    normalMonos.rlp (cofreeAnti.map p) := by
  intro X Y i hi
  exact (cofreeAntiAdjunction.hasLiftingProperty_iff i p).1 (hp i.hom hi.1)

end
end DaggerActualAntiJoyalAdjointLifting
