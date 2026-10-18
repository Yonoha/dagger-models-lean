import OriginalSimplicialCategoryBarHomInclusion
import OriginalOverNerveFibreChallengeProof

/-!
# The full strict original Hom fibre of the original DK80 bar projection

The source vertex is the constant chain at the same original object in every
original degree. Its native inverse-image subcomplex under the original bar
projection is isomorphic to the original enriched Hom simplicial set. The
forward map is exactly the previously constructed original Hom inclusion.
The inverse recovers the original final arrow. No homotopy-fibre or
quasifibration assertion is assumed.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarHomInclusion
universe u
namespace DaggerOriginalSimplicialCategoryBarFibre
noncomputable section

/-- The constant chain at the unchanged original source in its original degree category. -/
def constantSourceSimplex (C : SimplicialCat.{u, u}) (x : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (diagonalNerveFunctor.obj C).obj n :=
  (Functor.const (Fin (n.unop.len + 1)) (C := degreeObjects C n)).obj x

/-- All original simplicial operators retain the same constant source vertex. -/
theorem constantSourceSimplex_map (C : SimplicialCat.{u, u}) (x : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (diagonalNerveFunctor.obj C).map i (constantSourceSimplex C x n) =
      constantSourceSimplex C x m := by
  refine Functor.hext
    (F := (diagonalNerveFunctor.obj C).map i (constantSourceSimplex C x n))
    (G := constantSourceSimplex C x m) (fun _ ↦ rfl) ?_
  intro k l f
  exact heq_of_eq ((degreeMap C i).map_id x)

/-- The native vertex map from the actual standard zero-simplex. -/
def sourceVertexMap (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.stdSimplex.obj ⦋0⦌ ⟶ diagonalNerveFunctor.obj C where
  app n _ := constantSourceSimplex C x n
  naturality n m i := by
    funext a
    exact (constantSourceSimplex_map C x i).symm

/-- This map is exactly the native Yoneda map of the unchanged original vertex. -/
theorem sourceVertexMap_yoneda (C : SimplicialCat.{u, u}) (x : C.Obj) :
    sourceVertexMap C x = SSet.yonedaEquiv.symm
      (ComposableArrows.mk₀ (C := degreeObjects C (op ⦋0⦌)) x) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_apply]
  rfl

/-- The subcomplex containing precisely the original constant source vertex in all degrees. -/
def sourceVertexSubcomplex (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (diagonalNerveFunctor.obj C).Subcomplex where
  obj n := {a | a = constantSourceSimplex C x n}
  map i := by
    intro a ha
    change (diagonalNerveFunctor.obj C).map i a = constantSourceSimplex C x _
    rw [show a = constantSourceSimplex C x _ from ha]
    exact constantSourceSimplex_map C x i

/-- The full strict fibre in the original endpoint component, using native inverse image. -/
def barFibre (C : SimplicialCat.{u, u}) (x y : C.Obj) : (barComponent C y).Subcomplex :=
  (sourceVertexSubcomplex C x).preimage (barComponentProjection C y)

/-- Membership retains the exact original projection equation in every degree. -/
theorem barFibre_mem (C : SimplicialCat.{u, u}) (x y : C.Obj) (n : SimplexCategoryᵒᵖ)
    (a : (barComponent C y).obj n) :
    a ∈ (barFibre C x y).obj n ↔
      (barComponentProjection C y).app n a = constantSourceSimplex C x n := Iff.rfl

/-- A fibre simplex is an original over chain projecting to the original constant chain. -/
theorem barFibre_projectionEq (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : ((barFibre C x y).toSSet).obj n) :
    a.val ⋙ Over.forget (T := degreeObjects C n) y =
      (Functor.const (Fin (n.unop.len + 1)) (C := degreeObjects C n)).obj x := a.property

/-- All original Hom simplices and all original fibre simplices correspond bijectively. -/
def barFibreEquiv (C : SimplicialCat.{u, u}) (x y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (C.enriched.Hom x y).obj n ≃ ((barFibre C x y).toSSet).obj n where
  toFun a := ⟨(barHomInclusion C x y).app n a, barHomInclusion_projection C x y n a⟩
  invFun a := DaggerOriginalOverNerveFibreChallengeProof.fibreArrow a.val
    (barFibre_projectionEq C x y n a)
  left_inv a := by
    apply barHomInclusion_injective C x y n
    exact (DaggerOriginalOverNerveFibreChallengeProof.chain_eq_const
      ((barHomInclusion C x y).app n a) (barHomInclusion_projection C x y n a)).symm
  right_inv a := by
    apply Subtype.ext
    exact (DaggerOriginalOverNerveFibreChallengeProof.chain_eq_const a.val
      (barFibre_projectionEq C x y n a)).symm

/-- The whole strict original fibre is the unchanged original enriched Hom simplicial set. -/
def barFibreIso (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    C.enriched.Hom x y ≅ (barFibre C x y).toSSet :=
  NatIso.ofComponents (fun n ↦ (barFibreEquiv C x y n).toIso) (by
    intro n m i
    funext a
    apply Subtype.ext
    exact congrFun ((barHomInclusion C x y).naturality i) a)

/-- Including the fibre isomorphism is precisely the original whole Hom inclusion. -/
theorem barFibreIso_hom_ι (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (barFibreIso C x y).hom ≫ (barFibre C x y).ι = barHomInclusion C x y := by
  apply NatTrans.ext
  funext n
  rfl

/-- The inverse is the original final arrow, with its source transported by the fibre equation. -/
theorem barFibreIso_inv_apply (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : ((barFibre C x y).toSSet).obj n) :
    (barFibreIso C x y).inv.app n a =
      DaggerOriginalOverNerveFibreChallengeProof.fibreArrow a.val
        (barFibre_projectionEq C x y n a) := rfl

end
end DaggerOriginalSimplicialCategoryBarFibre
