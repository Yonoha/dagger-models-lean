import IntervalChosenCenter
import TopCatModelCategory.TopCat.Homotopy
import TopCatModelCategory.TopCat.HornDeformationRetract

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalChosenHom

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open DaggerIntervalNecklaceCompletion

abbrev singRealization : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

def tensorUnitDeltaZero : (𝟙_ SSet.{u}) ≅ Δ[0] :=
  isTerminalTensorUnit.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

def singularTensorUnitDeltaZero : singRealization.obj (𝟙_ SSet.{u}) ≅ Δ[0] :=
  singRealization.mapIso tensorUnitDeltaZero ≪≫ (asIso (sSetTopAdj.unit.app Δ[0])).symm

def originalCollapse (z w : (C.{u}.obj E).Obj) : originalHom z w ⟶ 𝟙_ SSet.{u} :=
  toUnit (originalHom z w)

def originalRealizedHomotopyEquiv (z w : (C.{u}.obj E).Obj) :
    SSet.HomotopyEquiv (singRealization.obj (originalHom z w)) Δ[0] :=
  ((originalIntervalHomContractible z w).toSSetToTop).homotopyEquiv

theorem originalRealizedHomotopyEquiv_hom (z w : (C.{u}.obj E).Obj) :
    (originalRealizedHomotopyEquiv z w).hom =
      SSet.stdSimplex.isTerminalObj₀.from (singRealization.obj (originalHom z w)) := rfl

def originalRealizedHomotopyEquiv_homInvId (z w : (C.{u}.obj E).Obj) :
    SSet.Homotopy
      ((originalRealizedHomotopyEquiv z w).hom ≫ (originalRealizedHomotopyEquiv z w).inv)
      (𝟙 (singRealization.obj (originalHom z w))) :=
  (originalRealizedHomotopyEquiv z w).homInvId

def originalRealizedHomotopyEquiv_invHomId (z w : (C.{u}.obj E).Obj) :
    SSet.Homotopy
      ((originalRealizedHomotopyEquiv z w).inv ≫ (originalRealizedHomotopyEquiv z w).hom)
      (𝟙 (Δ[0] : SSet.{u})) := (originalRealizedHomotopyEquiv z w).invHomId

theorem originalCollapse_terminal_equation (z w : (C.{u}.obj E).Obj) :
    singRealization.map (originalCollapse z w) ≫ singularTensorUnitDeltaZero.hom =
      (originalRealizedHomotopyEquiv z w).hom :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem originalIntervalHom_geometric (z w : (C.{u}.obj E).Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (originalCollapse z w))) := by
  have hterminal := SSet.KanComplex.W.homotopyEquivHom
    (originalRealizedHomotopyEquiv z w)
  have hiso := SSet.KanComplex.W.of_iso singularTensorUnitDeltaZero.{u}.hom
  exact SSet.KanComplex.W.of_postcomp
    (singRealization.map (originalCollapse z w)) singularTensorUnitDeltaZero.hom hiso
    (by rw [originalCollapse_terminal_equation]; exact hterminal)

end

end DaggerOriginalIntervalChosenHom
