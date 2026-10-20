import OriginalFlagConstantAugmentation
import TopCatModelCategory.SSet.PiZero
import TopCatModelCategory.SSet.SingularConnected
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

/-! Raw simplicial pi-zero for the literal constant target; first P1 bridge. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial

universe u
namespace DaggerOriginalFlagFlankification
noncomputable section
open DaggerChosenRigidificationNecklace

/-- The raw simplicial component quotient of the literal constant simplicial set. -/
def constantPiZeroEquiv (Q : Type u) : SSet.π₀ (constantSSet Q) ≃ Q where
  toFun := Quot.lift (fun t : Q ↦ t) (by
    rintro x y ⟨e, h₀, h₁⟩
    exact h₀.symm.trans h₁)
  invFun := fun t : Q ↦ SSet.π₀.mk (X := constantSSet Q) t
  left_inv c := by
    obtain ⟨t, rfl⟩ := SSet.π₀.mk_surjective c
    rfl
  right_inv _ := rfl

@[simp] theorem constantPiZeroEquiv_mk (Q : Type u) (t : Q) :
    constantPiZeroEquiv Q (SSet.π₀.mk t) = t := rfl

/-- A geometric weak equivalence induces a bijection on raw simplicial pi-zero. -/
theorem geometric_mapPiZero_bijective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f))) :
    Function.Bijective (SSet.mapπ₀ f) := by
  apply (Function.Bijective.of_comp_iff'
    (SSet.bijective_mapπ₀_sSetTopAdj_unit_app Y) (SSet.mapπ₀ f)).mp
  have hR := SSet.KanComplex.W.bijective_mapπ₀ hf
  have hX := SSet.bijective_mapπ₀_sSetTopAdj_unit_app X
  convert hR.comp hX using 1
  funext x
  dsimp
  rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply,
    Adjunction.unit_naturality]

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

/-- The already proved row comparison is bijective on the original raw pi-zero. -/
theorem constantAugmentation_mapPiZero_bijective :
    Function.Bijective (SSet.mapπ₀ (constantAugmentation X a b n)) :=
  geometric_mapPiZero_bijective _ (constantAugmentation_geometric X a b n)

/-- Raw simplicial components of the original degree nerve are the original quotient. -/
def rawPiZeroEquiv : SSet.π₀ (nerve (Degree X a b n)) ≃
    (flagHom X a b).obj (op ⦋n⦌) :=
  (Equiv.ofBijective (SSet.mapπ₀ (constantAugmentation X a b n))
    (constantAugmentation_mapPiZero_bijective X a b n)).trans
    (constantPiZeroEquiv _)

/-- The forward equivalence has the exact supplied quotient representative. -/
theorem rawPiZeroEquiv_mk (p : Degree X a b n) :
    rawPiZeroEquiv X a b n (SSet.π₀.mk (ComposableArrows.mk₀ p)) =
      classOf X a b n p := by
  rfl

end
end DaggerOriginalFlagFlankification
