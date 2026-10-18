import NativeFreeMappingComponents
import OriginalCountableContinuousClassesRecovered
import OriginalSphereNullityHomotopyRecovered

/-! Existing continuous homotopy classes are components of the native singular mapping object. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed HomotopicalAlgebra
open DaggerNativeFreeMappingComponents DaggerCountableContinuousClasses DaggerSphereNullity
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGeometricFreeMappingClasses
noncomputable section

def topHomContinuousEquiv (A B : TopCat.{u}) : (A ⟶ B) ≃ C(↑A, ↑B) where
  toFun f := f.hom
  invFun f := TopCat.ofHom f
  left_inv _ := rfl
  right_inv _ := rfl

def continuousAdjointEquiv (K X : SSet.{u}) :
    (K ⟶ TopCat.toSSet.obj (SSet.toTop.obj X)) ≃
      C(↑(SSet.toTop.obj K), ↑(SSet.toTop.obj X)) :=
  (sSetTopAdj.homEquiv K (SSet.toTop.obj X)).symm.trans
    (topHomContinuousEquiv _ _)

theorem adjoint_homotopic_iff (K X : SSet.{u})
    (f g : K ⟶ TopCat.toSSet.obj (SSet.toTop.obj X)) :
    ((continuousAdjointEquiv K X) f).Homotopic ((continuousAdjointEquiv K X) g) ↔
      Nonempty (SSet.Homotopy f g) := by
  constructor
  · rintro ⟨h⟩
    have ht := topCatHomotopy h
    have hs := singularHomotopyAdjoint ht
    change SSet.Homotopy
      ((sSetTopAdj.homEquiv K (SSet.toTop.obj X))
        ((sSetTopAdj.homEquiv K (SSet.toTop.obj X)).symm f))
      ((sSetTopAdj.homEquiv K (SSet.toTop.obj X))
        ((sSetTopAdj.homEquiv K (SSet.toTop.obj X)).symm g)) at hs
    simpa only [Equiv.apply_symm_apply] using Nonempty.intro hs
  · rintro ⟨h⟩
    exact ⟨DaggerFiniteRelativeExtension.continuousHomotopy (realizedHomotopyWithCounit h)⟩

def geometricClassComponent (K X : SSet.{u}) : Classes K X →
    ((ihom K).obj (TopCat.toSSet.obj (SSet.toTop.obj X))).π₀ :=
  Quot.lift (fun f ↦ component ((continuousAdjointEquiv K X).symm f)) (by
    intro f g h
    apply (component_eq_iff _ _).mpr
    apply (adjoint_homotopic_iff K X _ _).mp
    simpa only [Equiv.apply_symm_apply] using h)

theorem geometricClassComponent_mk (K X : SSet.{u})
    (f : C(↑(SSet.toTop.obj K), ↑(SSet.toTop.obj X))) :
    geometricClassComponent K X (Quot.mk ContinuousMap.Homotopic f) =
      component ((continuousAdjointEquiv K X).symm f) := rfl

theorem geometricClassComponent_bijective (K X : SSet.{u}) :
    Function.Bijective (geometricClassComponent K X) := by
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := Quot.mk_surjective f
    obtain ⟨g, rfl⟩ := Quot.mk_surjective g
    apply Quot.sound
    have hs := (component_eq_iff _ _).mp h
    have ht := (adjoint_homotopic_iff K X _ _).mpr hs
    simpa only [Equiv.apply_symm_apply] using ht
  · intro c
    obtain ⟨f, hf⟩ := component_surjective K (TopCat.toSSet.obj (SSet.toTop.obj X)) c
    refine ⟨Quot.mk ContinuousMap.Homotopic ((continuousAdjointEquiv K X) f), ?_⟩
    change component ((continuousAdjointEquiv K X).symm ((continuousAdjointEquiv K X) f)) = c
    rw [Equiv.symm_apply_apply]
    exact hf

def geometricClassesEquiv (K X : SSet.{u}) : Classes K X ≃
    ((ihom K).obj (TopCat.toSSet.obj (SSet.toTop.obj X))).π₀ :=
  Equiv.ofBijective (geometricClassComponent K X) (geometricClassComponent_bijective K X)

end
end DaggerNativeGeometricFreeMappingClasses
