import OriginalVertexCosliceContraction
import OriginalKanVertexCosliceFibration
import NativeLabeledStrictPathWeak

/-! Transpose the EXISTING original coslice contraction into the native path object. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerOriginalSimplexCoslice DaggerOriginalVertexCosliceContraction
universe u
namespace DaggerNativeOriginalCoslicePathMap
noncomputable section

def intervalEndpoint (A : SSet.{u}) (v : Fin 2) : A ⟶ A ⊗ Δ[1] where
  app n a := (a, SSet.stdSimplex.const 1 v n)
  naturality _ _ _ := rfl

theorem curry_evaluation {A X : SSet.{u}} (H : A ⊗ Δ[1] ⟶ X) (v : Fin 2) :
    curry ((β_ Δ[1] A).hom ≫ H) ≫
        ((Δ[1] : SSet.{u}).ihomEv (SSet.stdSimplex.obj₀Equiv.symm v)).app X =
      intervalEndpoint A v ≫ H := by
  apply (cancel_mono (SSet.stdSimplex.ihom₀.inv.app X)).mp
  change (curry ((β_ Δ[1] A).hom ≫ H) ≫
      (MonoidalClosed.pre (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm v))).app X) ≫
      SSet.stdSimplex.ihom₀.hom.app X ≫ SSet.stdSimplex.ihom₀.inv.app X = _
  have hi : SSet.stdSimplex.ihom₀.hom.app X ≫ SSet.stdSimplex.ihom₀.inv.app X = 𝟙 _ :=
    NatTrans.congr_app SSet.stdSimplex.ihom₀.hom_inv_id X
  rw [hi, Category.comp_id]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left, SSet.stdSimplex.ihom₀_inv_app,
    MonoidalClosed.uncurry_curry]
  apply NatTrans.ext
  funext n t
  rcases t with ⟨z, a⟩
  have hz : z = SSet.stdSimplex.const 0 0 n := Subsingleton.elim _ _
  subst z
  rfl

def comparison (X : SSet.{u}) (x : X _⦋0⦌) : simplexCoslice ⦋0⦌ X x ⟶ X.path :=
  curry ((β_ Δ[1] (simplexCoslice ⦋0⦌ X x)).hom ≫
    contraction X x ≫ cosliceProjection ⦋0⦌ X x)

theorem comparison_zero (X : SSet.{u}) (x : X _⦋0⦌) :
    comparison X x ≫ X.pathEv₀ = SSet.const x := by
  rw [comparison, SSet.pathEv₀, curry_evaluation]
  change SSet.ι₀ ≫ contraction X x ≫ cosliceProjection ⦋0⦌ X x = _
  rw [← Category.assoc, contraction_zero]
  apply NatTrans.ext
  funext n s
  change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ n.unop).op
    (X.map ((DaggerOriginalOrdinalJoinLeft.ordinalJoinLeft ⦋0⦌).map
      (n.unop.const ⦋0⦌ 0)).op (coslicePoint X x).val) = _
  rw [map_comp_op_apply]
  change X.map _ (X.map _ x) = _
  rw [map_comp_op_apply]
  congr 2

theorem comparison_one (X : SSet.{u}) (x : X _⦋0⦌) :
    comparison X x ≫ X.pathEv₁ = cosliceProjection ⦋0⦌ X x := by
  rw [comparison, SSet.pathEv₁, curry_evaluation]
  change SSet.ι₁ ≫ contraction X x ≫ cosliceProjection ⦋0⦌ X x = _
  rw [← Category.assoc, contraction_one, Category.id_comp]

end
end DaggerNativeOriginalCoslicePathMap
