import NativeSpineRootSubcomplex
import TopCatModelCategory.ModelCategorySSet

/-! The actual root-generated subcomplex is isomorphic to the native zero simplex. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerNativeGeneratorSpineSimplices DaggerNativeSpineRootSubcomplex
universe u
namespace DaggerNativeSpineRootPoint
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W] (r : W)

def rootMap : (Δ[0] : SSet.{u}) ⟶ spine W := SSet.yonedaEquiv.symm (vertex W r)

instance rootMapMono : Mono (rootMap r) :=
  ⟨fun f g _ ↦ SSet.stdSimplex.isTerminalObj₀.hom_ext f g⟩

theorem range_rootMap : SSet.Subcomplex.range (rootMap r) = rootComplex r := by
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  simp only [rootMap, Equiv.apply_symm_apply, rootComplex]

def rootIso : (Δ[0] : SSet.{u}) ≅ (rootComplex r).toSSet :=
  asIso (Subfunctor.toRange (rootMap r)) ≪≫ SSet.Subcomplex.isoOfEq (range_rootMap r)

def rootIsTerminal : IsTerminal (rootComplex r).toSSet :=
  SSet.stdSimplex.isTerminalObj₀.ofIso (rootIso r)

end
end DaggerNativeSpineRootPoint
