import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

/-! Native relative homotopy classes are the actual components of their native mapping fibre. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open SSet.Subcomplex SSet.Subcomplex.RelativeMorphism
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRelativeHomotopyComponents
noncomputable section

def relativeClassComponent {X Y : SSet.{u}} [IsFibrant Y] (A : X.Subcomplex)
    (B : Y.Subcomplex) (φ : (A : SSet.{u}) ⟶ B) :
    HomotopyClass A B φ → (relativeMorphism A B φ : SSet.{u}).π₀ :=
  Quot.lift (fun f ↦ SSet.π₀.mk (RelativeMorphism.equiv f)) (by
    intro f g h
    exact congr_toπ₀_of_hom (homMk (Homotopy.equiv h.some)))

theorem relativeClassComponent_mk {X Y : SSet.{u}} [IsFibrant Y]
    (A : X.Subcomplex) (B : Y.Subcomplex) (φ : (A : SSet.{u}) ⟶ B)
    (f : RelativeMorphism A B φ) :
    relativeClassComponent A B φ f.homotopyClass = SSet.π₀.mk (RelativeMorphism.equiv f) := rfl

theorem relativeClassComponent_bijective {X Y : SSet.{u}} [IsFibrant Y]
    (A : X.Subcomplex) (B : Y.Subcomplex) (φ : (A : SSet.{u}) ⟶ B) :
    Function.Bijective (relativeClassComponent A B φ) := by
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := HomotopyClass.eq_homotopyClass f
    obtain ⟨g, rfl⟩ := HomotopyClass.eq_homotopyClass g
    obtain ⟨p⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff (RelativeMorphism.equiv f)
      (RelativeMorphism.equiv g)).mp h
    exact Homotopy.eq (Homotopy.equiv.symm p)
  · intro c
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
    refine ⟨(RelativeMorphism.equiv.symm v).homotopyClass, ?_⟩
    exact congrArg SSet.π₀.mk (RelativeMorphism.equiv.apply_symm_apply v)

def relativeClassComponentsEquiv {X Y : SSet.{u}} [IsFibrant Y]
    (A : X.Subcomplex) (B : Y.Subcomplex) (φ : (A : SSet.{u}) ⟶ B) :
    HomotopyClass A B φ ≃ (relativeMorphism A B φ : SSet.{u}).π₀ :=
  Equiv.ofBijective (relativeClassComponent A B φ) (relativeClassComponent_bijective A B φ)

end
end DaggerNativeRelativeHomotopyComponents
