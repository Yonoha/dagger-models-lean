import NativeFixedDaggerIsomorphismPart
import ActualDaggerIsomorphismPartLocalWeak
import OriginalFixedObjectGroupoidTerminals

/-! Native fibrancy of the SAME original ambient fixed-object dagger category
is exactly Kan on ALL original Homs. The original isomorphism-component part remains fibrant.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidTerminals
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerFibrancy
noncomputable section

def terminalIsTerminal (O : Type u) : IsTerminal (terminalFixedDagger O) :=
  IsTerminal.ofUniqueHom daggerToTerminal (by
    intro C F
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro x y
    exact CartesianMonoidalCategory.toUnit_unique _ _)

theorem fibrant_iff_homs {O : Type u} (C : FixedDaggerCategory O) :
    IsFibrant C ↔ ∀ x y : O, (C.underlying.enriched.Hom x y).KanComplex := by
  rw [isFibrant_iff_of_isTerminal (daggerToTerminal C) (terminalIsTerminal O),
    DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  exact (isFibrant_iff_of_isTerminal
    (CartesianMonoidalCategory.toUnit (C.underlying.enriched.Hom x y))
    CartesianMonoidalCategory.isTerminalTensorUnit).symm

theorem hom_kan {O : Type u} (C : FixedDaggerCategory O) [IsFibrant C] (x y : O) :
    (C.underlying.enriched.Hom x y).KanComplex :=
  (fibrant_iff_homs C).mp inferInstance x y

theorem part_fibrant {O : Type u} (C : FixedDaggerCategory O) [IsFibrant C] :
    IsFibrant (DaggerNativeFixedDaggerIsomorphismPart.part C) := by
  apply (fibrant_iff_homs _).mpr
  intro x y
  exact DaggerActualDaggerIsomorphismPartLocalWeak.locallyKan (originalDagger C)
    (hom_kan C) x y

end
end DaggerNativeAmbientDaggerFibrancy
