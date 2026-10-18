import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Types.Basic

/-! Native homotopy classes into fibrant objects detect localization isomorphisms. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
universe u v w t

namespace DaggerNativeRightHomotopyClassFunctor
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The native contravariant homotopy-class functor into a fixed target. -/
def homotopyYoneda (Z : C) : Cᵒᵖ ⥤ Type v where
  obj X := RightHomotopyClass X.unop Z
  map f g := g.precomp f.unop
  map_id X := by
    funext g
    obtain ⟨g, rfl⟩ := g.mk_surjective
    simp
  map_comp f g := by
    funext h
    obtain ⟨h, rfl⟩ := h.mk_surjective
    simp [Category.assoc]

variable [∀ X : C, IsCofibrant X]

/-- Mathlib's native Brown lemma inverts all weak maps into a fibrant target. -/
theorem homotopyYoneda_inverts (Z : C) [IsFibrant Z] :
    (weakEquivalences C).op.IsInvertedBy (homotopyYoneda Z) := by
  intro X Y f hf
  have : WeakEquivalence f.unop := ⟨hf⟩
  exact (isIso_iff_bijective _).mpr
    (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z f.unop)

variable {H : Type w} [Category.{t} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- A localization isomorphism induces a bijection on every native fibrant homotopy-class set. -/
theorem precomp_bijective_of_localization_isIso {X Y : C} (f : X ⟶ Y)
    [IsIso (L.map f)] (Z : C) [IsFibrant Z] :
    Function.Bijective (fun g : RightHomotopyClass Y Z ↦ g.precomp f) := by
  let R := Localization.lift (homotopyYoneda Z) (homotopyYoneda_inverts Z) L.op
  let e := Localization.fac (homotopyYoneda Z) (homotopyYoneda_inverts Z) L.op
  have : IsIso (L.op.map f.op) := by
    change IsIso (L.map f).op
    infer_instance
  have : IsIso (R.map (L.op.map f.op)) := inferInstance
  have h : IsIso (e.hom.app _ ≫ (homotopyYoneda Z).map f.op) := by
    rw [← e.hom.naturality f.op]
    change IsIso (R.map (L.op.map f.op) ≫ e.hom.app _)
    infer_instance
  have hIso : IsIso ((homotopyYoneda Z).map f.op) := (isIso_comp_left_iff _ _).mp h
  exact (isIso_iff_bijective ((homotopyYoneda Z).map f.op)).mp hIso

end
end DaggerNativeRightHomotopyClassFunctor
