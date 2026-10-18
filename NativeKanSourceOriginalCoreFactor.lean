import OriginalOrdinaryCoreKan
import OriginalOrdinaryKanCoreCandidateFunctor
import NativeHoIsoTriangles

/-! Maps from native Kan sources factor through the exact original core, preserving the map. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryCoreKan
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes DaggerNativeHoIsoTriangles
universe u
namespace DaggerNativeKanSourceOriginalCoreFactor
noncomputable section

theorem kan_map_mem_core {K X : SSet.{u}} [K.KanComplex] (f : K ⟶ X)
    (q : SimplexCategoryᵒᵖ) (x : K.obj q) :
    f.app q x ∈ (ordinaryCoreCandidate X).obj q := by
  have hx : x ∈ (ordinaryCoreCandidate K).obj q := by
    rw [ordinaryCoreCandidate_eq_top_of_kan K]
    trivial
  exact ((ordinaryCoreCandidateMap f).app q ⟨x, hx⟩).property

def factor {K X : SSet.{u}} [K.KanComplex] (f : K ⟶ X) :
    K ⟶ (ordinaryCoreCandidate X : SSet.{u}) where
  app q x := ⟨f.app q x, kan_map_mem_core f q x⟩
  naturality _ _ α := by
    funext x
    apply Subtype.ext
    exact congrFun (f.naturality α) x

theorem factor_comp {K X : SSet.{u}} [K.KanComplex] (f : K ⟶ X) :
    factor f ≫ (ordinaryCoreCandidate X).ι = f := rfl

theorem factor_unique {K X : SSet.{u}} [K.KanComplex] (f : K ⟶ X)
    (g : K ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (hg : g ≫ (ordinaryCoreCandidate X).ι = f) : g = factor f := by
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  rw [hg, factor_comp]

theorem native_quasi_core_kan (X : SSet.{u}) [X.Quasicategory] :
    (ordinaryCoreCandidate X : SSet.{u}).KanComplex :=
  ordinaryCoreCandidate_kan X (native_inner_fillers X)

end
end DaggerNativeKanSourceOriginalCoreFactor
