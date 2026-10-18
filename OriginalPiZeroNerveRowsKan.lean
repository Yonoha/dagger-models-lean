import OriginalNerveRowsPiZero
import NativeGroupoidNerveKan
import OriginalPiZeroGroupoidLocalWeakInvariance

/-! The actual pi0 row object of an original pi0 groupoid is a native Kan complex. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalNerveRowsPiZero DaggerNativeGroupoidNerveKan
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalAmbientDaggerPiZeroGroupoid
open OriginalOrdinaryLocalKanReplacement DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalPiZeroNerveRowsKan
noncomputable section

theorem componentRows_kan (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (componentRows C).KanComplex := by
  obtain ⟨G, hG⟩ := hC
  have hN : (nerve (componentObjects C)).KanComplex := by
    change (@nerve (componentObjects C) (componentCategory C)).KanComplex
    rw [← hG]
    let g : Groupoid.{u, u} (componentObjects C) := G
    exact nerve_kan (componentObjects C)
  have := hN
  have : Fibration (componentRowsIso C).hom := inferInstance
  exact isFibrant_of_fibration (componentRowsIso C).hom

theorem replacement_componentRows_kan (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) : (componentRows (replacement.obj C)).KanComplex :=
  componentRows_kan (replacement.obj C) ((replacement_groupoid_iff C).mp hC)

end
end DaggerOriginalPiZeroNerveRowsKan
