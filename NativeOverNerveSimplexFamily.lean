import NativeOverChainFixedProjection
import ActualConstantSimplicialCategory
import NativeSimplexPullbackFibrationDetection

/-! A full native base chain trivializes its groupoid over-nerve over the entire simplex. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerUnitaryDiscrete
open DaggerNativeOverChainDecomposition DaggerNativeOverChainFixedProjection
open DaggerNativeSimplexPullbackFibrationDetection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOverNerveSimplexFamily
noncomputable section

def restrictChain {G : Type u} [Category.{u} G] {n : ℕ} (A : Fin (n + 1) ⥤ G)
    {v : SimplexCategoryᵒᵖ} (t : (Δ[n] : SSet.{u}).obj v) : Fin (v.unop.len + 1) ⥤ G :=
  (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv t)).toFunctor ⋙ A

def lastArrow {G : Type u} [Category.{u} G] {n : ℕ} (A : Fin (n + 1) ⥤ G)
    {v : SimplexCategoryᵒᵖ} (t : (Δ[n] : SSet.{u}).obj v) :
    (restrictChain A t).obj (Fin.last v.unop.len) ⟶ A.obj (Fin.last n) :=
  A.map (homOfLE (Fin.le_last _))

def simplexFamily {G : Type u} [Category.{u} G] (z : G) {n : ℕ}
    (A : Fin (n + 1) ⥤ G) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (A.obj (Fin.last n) ⟶ z) ⟶ nerve (Over z) where
  app v p := chainLift (restrictChain A p.1) (lastArrow A p.1 ≫ p.2)
  naturality v w i := by
    funext p
    change chainLift (restrictChain A (Δ[n].map i p.1)) (lastArrow A (Δ[n].map i p.1) ≫ p.2) =
      (SimplexCategory.toCat.map i.unop).toFunctor ⋙
        chainLift (restrictChain A p.1) (lastArrow A p.1 ≫ p.2)
    rw [chainLift_precompose]
    congr 1
    change A.map _ ≫ p.2 = A.map _ ≫ A.map _ ≫ p.2
    rw [← Category.assoc, ← A.map_comp]
    congr 2

theorem simplexFamily_projection {G : Type u} [Category.{u} G] (z : G) {n : ℕ}
    (A : Fin (n + 1) ⥤ G) :
    simplexFamily z A ≫ nerveMap (Over.forget z) =
      fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z)) ≫
        SSet.yonedaEquiv.symm A := by
  apply NatTrans.ext
  funext v p
  change chainLift (restrictChain A p.1) (lastArrow A p.1 ≫ p.2) ⋙ Over.forget z = _
  rw [chainLift_forget]
  rfl

end
end DaggerNativeOverNerveSimplexFamily
