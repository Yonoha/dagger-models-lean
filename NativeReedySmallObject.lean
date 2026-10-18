import NativeBisimplicialLocallyPresentable
import NativeBisimplicialBoxUnion
import OriginalSmithCardinalRecovered

/-! Native small-object factorization for actual horizontal-boundary/vertical-horn boxes. -/
set_option autoImplicit false
open CategoryTheory MorphismProperty Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBoxUnion
universe u
namespace DaggerNativeReedySmallObject
noncomputable section

abbrev Index := ℕ × (Σ n : ℕ, Fin (n + 2))

def generator (m n : ℕ) (k : Fin (n + 2)) :=
  unionInclusion (SSet.boundary.{u} m) (SSet.horn.{u} (n + 1) k)

def J : MorphismProperty BiSSet.{u} :=
  ofHoms (fun s : Index ↦ generator.{u} s.1 s.2.1 s.2.2)

instance generators_small : IsSmall.{u} J.{u} := isSmall_ofHoms _

theorem generator_mem (m n : ℕ) (k : Fin (n + 2)) : J.{u} (generator.{u} m n k) := by
  exact (ofHoms_iff _ _).mpr ⟨(m, ⟨n, k⟩), rfl⟩

instance smallObjectArgument : HasSmallObjectArgument.{u} J.{u} :=
  DaggerSmithSolutionSet.smallObjectArgument J

def factorizationData : FunctorialFactorizationData J.{u}.rlp.llp J.{u}.rlp :=
  DaggerSmithSolutionSet.soaFactorization J

end
end DaggerNativeReedySmallObject
