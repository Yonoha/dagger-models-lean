import NativeRightLiftingArrowFunctor

/-! Full-square solution factorization transfers the original right lifting condition. -/

set_option autoImplicit false
open CategoryTheory DaggerNativeRightLiftingSurjection DaggerNativeRightLiftingArrowFunctor
universe u v

namespace DaggerNativeSmithRightLifting

variable {C : Type u} [Category.{v} C]

/-- Every original weak square factors through J, so a weak J-injective is I-injective. -/
theorem rlp_of_full_square_factorization (I J W : MorphismProperty C)
    (factor : ∀ (i : I.toSet) (f : Arrow C), W f.hom → ∀ (φ : i.1 ⟶ f),
      ∃ (j : J.toSet) (δ : i.1 ⟶ j.1) (ε : j.1 ⟶ f), δ ≫ ε = φ) :
    J.rlp ⊓ W ≤ I.rlp := by
  intro A B f hf X Y i hi
  apply (diagonalMap_surjective_iff (Arrow.mk i) (Arrow.mk f)).mp
  intro φ
  let a : I.toSet := ⟨Arrow.mk i, hi⟩
  obtain ⟨j, δ, ε, hcomp⟩ := factor a (Arrow.mk f) hf.2 φ
  have hjf : HasLiftingProperty j.1.hom f := hf.1 j.1.hom j.2
  obtain ⟨l, hl⟩ := (diagonalMap_surjective_iff j.1 (Arrow.mk f)).mpr hjf ε
  refine ⟨δ.right ≫ l, ?_⟩
  rw [← diagonalMap_source_naturality δ (Arrow.mk f) l, hl, hcomp]

end DaggerNativeSmithRightLifting
