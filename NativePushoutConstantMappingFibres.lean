import NativeIhomPushoutPullback
import NativePullbackFibreIso

/-! Restricting a map from an actual pushout identifies the original constant mapping fibres. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalClosed Simplicial
open DaggerNativePullbackFibreIso
universe u
namespace DaggerNativePushoutConstantMappingFibres
noncomputable section

abbrev constantMappingFibre {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u})
    (x : X _⦋0⦌) : ((ihom B).obj X).Subcomplex :=
  SSet.Subcomplex.fiber ((MonoidalClosed.pre i).app X)
    (SSet.ihom₀Equiv.symm (SSet.const x : A ⟶ X))

theorem constant_restriction_vertex {A C : SSet.{u}} (a : A ⟶ C) (X : SSet.{u})
    (x : X _⦋0⦌) :
    ((MonoidalClosed.pre a).app X).app _
        (SSet.ihom₀Equiv.symm (SSet.const x : C ⟶ X)) =
      SSet.ihom₀Equiv.symm (SSet.const x : A ⟶ X) := by
  rw [← SSet.ihom₀Equiv_symm_comp, SSet.comp_const]

def restrictionFibreMap {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (X : SSet.{u}) (x : X _⦋0⦌) :
    (constantMappingFibre j X x : SSet.{u}) ⟶ (constantMappingFibre i X x : SSet.{u}) :=
  SSet.Subcomplex.mapFiber ((MonoidalClosed.pre j).app X) ((MonoidalClosed.pre i).app X)
    ((MonoidalClosed.pre b).app X) ((MonoidalClosed.pre a).app X)
    (DaggerNativeIhomPushoutPullback.isPullback h X).w _ _
    (constant_restriction_vertex a X x)

instance restrictionFibreMap_isIso {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (X : SSet.{u}) (x : X _⦋0⦌) :
    IsIso (restrictionFibreMap h X x) :=
  mapFiber_isIso_of_isPullback _ _ _ _ (DaggerNativeIhomPushoutPullback.isPullback h X)
    _ _ (constant_restriction_vertex a X x)

def restrictionFibreIso {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (X : SSet.{u}) (x : X _⦋0⦌) :
    (constantMappingFibre j X x : SSet.{u}) ≅ (constantMappingFibre i X x : SSet.{u}) :=
  asIso (restrictionFibreMap h X x)

theorem restrictionFibreIso_hom_ι {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (X : SSet.{u}) (x : X _⦋0⦌) :
    (restrictionFibreIso h X x).hom ≫ (constantMappingFibre i X x).ι =
      (constantMappingFibre j X x).ι ≫ (MonoidalClosed.pre b).app X := rfl

end
end DaggerNativePushoutConstantMappingFibres
