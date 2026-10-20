import NativeRelativeHomotopyComponents
import TopCatModelCategory.SSet.HomotopyGroup

/-! Native based pi classes are components of the original relative mapping fibre. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet.KanComplex DaggerNativeRelativeHomotopyComponents
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePointedHomotopyComponents
noncomputable section

abbrev pointedMappingSpace (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  SSet.Subcomplex.relativeMorphism (SSet.boundary n) (SSet.Subcomplex.ofSimplex x)
    (SSet.const ⟨x, SSet.Subcomplex.mem_ofSimplex_obj x⟩)

def piComponentsEquiv (n : ℕ) (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) :
    π n X x ≃ (pointedMappingSpace n X x).π₀ :=
  relativeClassComponentsEquiv _ _ _

theorem piComponentsEquiv_mk (n : ℕ) (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌)
    (f : X.PtSimplex n x) :
    piComponentsEquiv n X x (π.mk f) = SSet.π₀.mk (SSet.Subcomplex.RelativeMorphism.equiv f) := rfl

end
end DaggerNativePointedHomotopyComponents
