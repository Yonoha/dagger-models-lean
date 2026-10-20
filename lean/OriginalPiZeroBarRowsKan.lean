import OriginalBarRowsPiZero
import OriginalPiZeroNerveRowsKan
import NativeOverGroupoidNerveKan

/-! The actual original bar pi0 rows are Kan for the actual original component groupoid. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalBarRowsPiZero DaggerNativeOverGroupoidNerveKan
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalAmbientDaggerPiZeroGroupoid
open OriginalOrdinaryLocalKanReplacement DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalPiZeroBarRowsKan
noncomputable section

theorem barComponentRows_kan (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) : (barComponentRows C z).KanComplex := by
  obtain ⟨G, hG⟩ := hC
  have hN : (nerve (Over (T := componentObjects C) z)).KanComplex := by
    change (@nerve (@Over (componentObjects C) (componentCategory C) z) _).KanComplex
    rw [← hG]
    letI : Groupoid.{u} (componentObjects C) := G
    exact over_nerve_kan (componentObjects C) z
  have := hN
  have : Fibration (barComponentRowsIso C z).hom := inferInstance
  exact isFibrant_of_fibration (barComponentRowsIso C z).hom

theorem replacement_barComponentRows_kan (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) :
    (barComponentRows (replacement.obj C) z).KanComplex :=
  barComponentRows_kan (replacement.obj C) ((replacement_groupoid_iff C).mp hC) z

end
end DaggerOriginalPiZeroBarRowsKan
