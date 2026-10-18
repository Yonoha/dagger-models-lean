import NativeInnerHornFacePostcomposition
import OriginalInnerHornData

/-! The ORIGINAL horn data commute with the ORIGINAL coherent-nerve postcomposition map. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite
open scoped Simplicial
open DaggerOrdinaryRigidificationCof DaggerOrdinaryRigidificationCof.BoundaryData
open DaggerOrdinaryRigidificationCof.PathFacets DaggerOrdinaryRigidificationCof.InnerHornFaces
open DaggerNativeInnerHornFacePostcomposition
universe u
namespace DaggerNativeInnerHornDataPostcomposition
noncomputable section

theorem simplex_post {d : ℕ} {C B : SC.{u}} (K : (Δ[d] : SSet.{u}).Subcomplex)
    (a : (K : SSet.{u}) ⟶ N.obj C) (p : C ⟶ B) {m : SimplexCategory} (φ : m ⟶ ⦋d⦌)
    (hφ : SubcomplexNerveData.Contains K φ) :
    SubcomplexNerveData.simplex K (a ≫ N.map p) φ hφ =
      SubcomplexNerveData.simplex K a φ hφ ≫ p := rfl

theorem ofSubcomplex_post {d : ℕ} {C B : SC.{u}} {P : Finset (Fin (d + 1)) → Prop}
    (K : (Δ[d] : SSet.{u}).Subcomplex) (a : (K : SSet.{u}) ⟶ N.obj C) (p : C ⟶ B)
    (hV : ∀ i : Fin (d + 1), SubcomplexNerveData.Contains K (vertexMap i))
    (hP : ∀ s hs, P s → SubcomplexNerveData.Contains K (faceOrdinal s hs)) :
    post (CompatibleFaceData.ofSubcomplex K a hV hP) p =
      CompatibleFaceData.ofSubcomplex K (a ≫ N.map p) hV hP := by
  rfl

theorem data_post {n : ℕ} {C B : SC.{u}} (k : interior n)
    (a : (SSet.horn.{u} (n + 1) k.val).toSSet ⟶ N.obj C) (p : C ⟶ B) :
    post (InnerHornData.data k a) p = InnerHornData.data k (a ≫ N.map p) :=
  ofSubcomplex_post _ a p _ _

end
end DaggerNativeInnerHornDataPostcomposition
