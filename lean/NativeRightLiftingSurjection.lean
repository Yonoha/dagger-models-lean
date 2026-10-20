import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Comma.Arrow

/-! The original right lifting predicate, expressed by all diagonal maps in the arrow category. -/

set_option autoImplicit false
open CategoryTheory
universe u v t

namespace DaggerNativeRightLiftingSurjection

variable {C : Type u} [Category.{v} C]

/-- A diagonal determines the complete square, retaining both legs and their equation. -/
def diagonalMap (a f : Arrow C) (l : a.right ⟶ f.left) : a ⟶ f :=
  Arrow.homMk (a.hom ≫ l) (l ≫ f.hom) (Category.assoc _ _ _)

@[simp] theorem diagonalMap_left (a f : Arrow C) (l : a.right ⟶ f.left) :
    (diagonalMap a f l).left = a.hom ≫ l := rfl

@[simp] theorem diagonalMap_right (a f : Arrow C) (l : a.right ⟶ f.left) :
    (diagonalMap a f l).right = l ≫ f.hom := rfl

/-- Surjectivity concerns every full commutative square, rather than just its vertices. -/
theorem diagonalMap_surjective_iff (a f : Arrow C) :
    Function.Surjective (diagonalMap a f) ↔ HasLiftingProperty a.hom f.hom := by
  constructor
  · intro h
    refine ⟨fun {top bottom} sq ↦ ?_⟩
    let φ : a ⟶ f := Arrow.homMk top bottom sq.w
    obtain ⟨l, hl⟩ := h φ
    exact ⟨⟨⟨l, congrArg (fun ψ : a ⟶ f ↦ ψ.left) hl,
      congrArg (fun ψ : a ⟶ f ↦ ψ.right) hl⟩⟩⟩
  · intro h φ
    let sq : CommSq φ.left a.hom f.hom φ.right := ⟨φ.w⟩
    letI : HasLiftingProperty a.hom f.hom := h
    obtain ⟨l⟩ := (HasLiftingProperty.sq_hasLift sq).exists_lift
    exact ⟨l.l, Arrow.hom_ext _ _ l.fac_left l.fac_right⟩

/-- Test the literal family, with no change to either endpoint or morphism. -/
theorem ofHoms_rlp_iff_family {I : Type t} {A B : I → C}
    (i : (r : I) → A r ⟶ B r) (f : Arrow C) :
    (MorphismProperty.ofHoms i).rlp f.hom ↔ ∀ r, HasLiftingProperty (i r) f.hom := by
  constructor
  · intro h r
    exact h (i r) (MorphismProperty.ofHoms.mk r)
  · intro h X Y g hg
    cases hg with
    | mk r => exact h r

/-- A family has the original RLP exactly when every diagonal map is surjective. -/
theorem ofHoms_rlp_iff_surjective {I : Type t} {A B : I → C}
    (i : (r : I) → A r ⟶ B r) (f : Arrow C) :
    (MorphismProperty.ofHoms i).rlp f.hom ↔
      ∀ r, Function.Surjective (diagonalMap (Arrow.mk (i r)) f) := by
  rw [ofHoms_rlp_iff_family]
  exact forall_congr' fun r ↦ (diagonalMap_surjective_iff (Arrow.mk (i r)) f).symm

/-- Every commutative square admits a diagonal with both literal triangle equations. -/
theorem ofHoms_rlp_iff_all_squares {I : Type t} {A B : I → C}
    (i : (r : I) → A r ⟶ B r) (f : Arrow C) :
    (MorphismProperty.ofHoms i).rlp f.hom ↔
      ∀ r (φ : Arrow.mk (i r) ⟶ f),
        ∃ l : B r ⟶ f.left, i r ≫ l = φ.left ∧ l ≫ f.hom = φ.right := by
  rw [ofHoms_rlp_iff_surjective]
  constructor
  · intro h r φ
    obtain ⟨l, hl⟩ := h r φ
    exact ⟨l, congrArg (fun ψ : Arrow.mk (i r) ⟶ f ↦ ψ.left) hl,
      congrArg (fun ψ : Arrow.mk (i r) ⟶ f ↦ ψ.right) hl⟩
  · intro h r φ
    obtain ⟨l, hl, hr⟩ := h r φ
    exact ⟨l, Arrow.hom_ext _ _ hl hr⟩

end DaggerNativeRightLiftingSurjection
