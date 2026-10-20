import DaggerModels
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! Restrict the original dagger to any stable subcomplex, preserving all original values. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
universe u
namespace DaggerNativeDaggerSubcomplexRestriction
noncomputable section
variable (X : DaggerSSet.{u}) (A : X.toSSet.Subcomplex)
variable (h : ∀ q (s : (A : SSet.{u}).obj q), X.dagger.app q s.val ∈ A.obj q)

def restricted : DaggerSSet.{u} where
  toSSet := (A : SSet.{u})
  dagger :=
    { app := fun q s ↦ ⟨X.dagger.app q s.val, h q s⟩
      naturality := by
        intro q r α
        funext s
        apply Subtype.ext
        exact congrFun (X.dagger.naturality α) s.val }
  involutive n s := by
    apply Subtype.ext
    exact X.involutive n s.val
  fixedVertices s := by
    apply Subtype.ext
    exact X.fixedVertices s.val

theorem restricted_toSSet : (restricted X A h).toSSet = (A : SSet.{u}) := rfl

def inclusion : restricted X A h ⟶ X where
  hom := A.ι
  comm := by
    apply NatTrans.ext
    funext q s
    rfl

theorem inclusion_hom : (inclusion X A h).hom = A.ι := rfl

theorem dagger_val (n : ℕ) (s : (restricted X A h).toSSet _⦋n⦌) :
    ((restricted X A h).dagger.app (op ⦋n⦌) s).val = X.dagger.app (op ⦋n⦌) s.val := rfl

def verticesEquiv (hv : ∀ x : X.toSSet _⦋0⦌, x ∈ A.obj (op ⦋0⦌)) :
    (restricted X A h).toSSet _⦋0⦌ ≃ X.toSSet _⦋0⦌ where
  toFun := Subtype.val
  invFun x := ⟨x, hv x⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv _ := rfl

include h in
theorem exists_restricted :
    ∃ (D : DaggerSSet.{u}) (hD : D.toSSet = (A : SSet.{u})) (i : D ⟶ X),
      i.hom = eqToHom hD ≫ A.ι := by
  refine ⟨restricted X A h, rfl, inclusion X A h, ?_⟩
  rw [eqToHom_refl, Category.id_comp]
  exact inclusion_hom X A h

end
end DaggerNativeDaggerSubcomplexRestriction
