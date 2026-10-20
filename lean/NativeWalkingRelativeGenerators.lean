import NativeWalkingSubcomplexCylinder
import NativeJoyalFirstFactorization
import NativeInnerHornFactorization

/-!
# Actual native relative J-cylinder union-product generators

Use the library's full union-product pushout, for every native subcomplex and the
actual zero endpoint of the original interval. These whole maps are mono and
satisfy the unchanged all-quasi-target Joyal mapping weak test. The original full
Joyal candidate lifts against every such map. Its converse recognition and the
full second factorization are separate remaining assertions.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeBoundaryCategoricalCylinder
open DaggerNativeWalkingSubcomplexCylinder DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeWalkingRelativeGenerators
noncomputable section

def zeroSubcomplex : J.{u}.Subcomplex where
  obj q := {t | t = time q false}
  map {q k} α := by
    intro t ht
    change J.map α t = time k false
    rw [ht, time_map]

theorem union_eq_unionProd {X : SSet.{u}} (S : X.Subcomplex) :
    union S = S.unionProd zeroSubcomplex := by
  ext q p
  simp [union, zeroSubcomplex, SSet.Subcomplex.mem_unionProd_iff]

theorem unionProd_zero_weak {X : SSet.{u}} (S : X.Subcomplex) :
    weakCategoricalEquivalences (S.unionProd zeroSubcomplex.{u}).ι := by
  rw [← union_eq_unionProd]
  exact union_inclusion_weak S

theorem pushout_unionProd_zero_weak {X : SSet.{u}} (S : X.Subcomplex) :
    weakCategoricalEquivalences (SSet.PushoutTensor.unionProd S zeroSubcomplex.{u}).ι := by
  rw [SSet.PushoutTensor.ι_unionProd]
  exact unionProd_zero_weak S

theorem unionProd_zero_mono_weak {X : SSet.{u}} (S : X.Subcomplex) :
    (MorphismProperty.monomorphisms SSet ⊓ weakCategoricalEquivalences)
      (S.unionProd zeroSubcomplex.{u}).ι :=
  ⟨(show Mono (S.unionProd zeroSubcomplex.{u}).ι from inferInstance), unionProd_zero_weak S⟩

def generator (n : ℕ) := ((SSet.boundary.{u} n).unionProd zeroSubcomplex.{u}).ι

def generators : MorphismProperty SSet.{u} := MorphismProperty.ofHoms generator

instance generatorsSmall : MorphismProperty.IsSmall.{u} generators.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem generators_le_mono_weak :
    generators.{u} ≤ MorphismProperty.monomorphisms SSet.{u} ⊓
      weakCategoricalEquivalences.{u} := by
  rintro A B f ⟨n⟩
  exact unionProd_zero_mono_weak (SSet.boundary n)

theorem candidate_le_generators_rlp :
    DaggerNativeJoyalFirstFactorization.candidateFibrations.{u} ≤ generators.{u}.rlp :=
  MorphismProperty.antitone_rlp generators_le_mono_weak

end
end DaggerNativeWalkingRelativeGenerators
