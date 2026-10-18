import NativeRealEdgewiseSSet
import NativeDaggerUnderlyingIso
import TopCatModelCategory.SSet.StandardSimplex

/-! The ORIGINAL dagger induces the literal strict involution d_(2n+1) on Tw(X).
All original dagger maps and original constant vertices are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSymmetry DaggerNativeRealEdgewiseSSet
universe u
namespace DaggerNativeRealEdgewiseDaggerInvolution
noncomputable section

def involution (X : DaggerSSet.{u}) : edgewise.obj X.toSSet ⟶ edgewise.obj X.toSSet where
  app n := X.dagger.app (epsilon.op.obj n)
  naturality m n f := by
    have h := X.dagger.naturality (epsilon.op.map f)
    change X.toSSet.map (epsilon.map f.unop).op ≫ X.dagger.app (epsilon.op.obj n) =
      X.dagger.app (epsilon.op.obj m) ≫
        X.toSSet.map (SimplexCategory.rev.map (epsilon.map f.unop)).op at h
    rw [epsilon_rev f.unop] at h
    exact h

theorem involution_square (X : DaggerSSet.{u}) : involution X ≫ involution X = 𝟙 _ := by
  ext n z
  exact X.involutive (epsilon.obj n.unop).len z

theorem involution_natural {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    involution X ≫ edgewise.map f.hom = edgewise.map f.hom ≫ involution Y := by
  apply NatTrans.ext
  funext n
  exact (NatTrans.congr_app f.comm (epsilon.op.obj n)).symm

theorem involution_degenerate_vertex (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (involution X).app (op ⦋0⦌) (X.toSSet.σ (0 : Fin 1) x) = X.toSSet.σ (0 : Fin 1) x := by
  change X.dagger.app (op ⦋1⦌) (X.toSSet.σ (0 : Fin 1) x) = X.toSSet.σ (0 : Fin 1) x
  have h := congrArg
    (fun g : X.toSSet.obj (op ⦋0⦌) ⟶ X.toSSet.op.obj (op ⦋1⦌) ↦ g x)
    (X.dagger.naturality (SimplexCategory.σ (0 : Fin 1)).op)
  change X.dagger.app (op ⦋1⦌) (X.toSSet.σ (0 : Fin 1) x) =
    X.toSSet.op.σ (0 : Fin 1) (X.dagger.app (op ⦋0⦌) x) at h
  rw [SSet.op_σ] at h
  change X.dagger.app (op ⦋1⦌) (X.toSSet.σ (0 : Fin 1) x) =
    X.toSSet.σ (0 : Fin 1).rev (X.dagger.app (op ⦋0⦌) x) at h
  have h0 : X.dagger.app (op ⦋0⦌) x = x := X.fixedVertices x
  rw [show (0 : Fin 1).rev = 0 by decide, h0] at h
  exact h

def vertexMap (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{u}) ⟶ edgewise.obj X.toSSet :=
  SSet.yonedaEquiv.symm (X.toSSet.σ (0 : Fin 1) x)

theorem vertexMap_fixed (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    vertexMap X x ≫ involution X = vertexMap X x := by
  unfold vertexMap
  rw [SSet.yonedaEquiv_symm_comp, involution_degenerate_vertex]

end
end DaggerNativeRealEdgewiseDaggerInvolution
