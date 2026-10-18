import OriginalStrictGroupoidObjectFixedC2Actions
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Actual C2 cofree actions using only binary products

The underlying object is the original chosen binary product. The generator swaps its
two factors. The Hom equivalence retains the first projection and the full paired map,
and proves both inverse laws and both naturality laws. No model or all-limits premise.
-/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
universe u v w
namespace DaggerOriginalC2BinaryCofreeAdjunction
noncomputable section
variable {C : Type v} [Category.{w} C] [HasBinaryProducts C]

/-- The actual original product endomorphism interchanges the two projections. -/
def swap (X : C) : End (X ⨯ X) := prod.lift prod.snd prod.fst

/-- The original product swap is involutive. -/
theorem swap_square (X : C) : swap X * swap X = 1 := by
  change swap X ≫ swap X = 𝟙 _
  apply prod.hom_ext <;> simp [swap]

/-- The exact C2 representation acts by the swap on the full binary product. -/
def cofreeRepresentation (X : C) : C2.{u} →* End (X ⨯ X) where
  toFun g := if g = 1 then 1 else swap X
  map_one' := by simp
  map_mul' g h := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    rcases originalC2_cases h with rfl | rfl
    · simp
    rw [originalGenerator_mul_self, if_pos rfl, if_neg originalGenerator_ne_one]
    exact (swap_square X).symm

/-- The distinguished generator is exactly the original product swap. -/
theorem cofreeRepresentation_generator (X : C) :
    cofreeRepresentation X generator.{u} = swap X := by
  simp [cofreeRepresentation, originalGenerator_ne_one]

/-- The actual cofree C2 object has the unchanged native binary product underneath. -/
def cofreeObject (X : C) : Action C C2.{u} := ⟨X ⨯ X, cofreeRepresentation X⟩

/-- The actual cofree arrow is the original binary product of the same input arrow twice. -/
def cofreeMap {X Y : C} (f : X ⟶ Y) : cofreeObject.{u} X ⟶ cofreeObject Y where
  hom := prod.map f f
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · change cofreeRepresentation X generator ≫ prod.map f f =
        prod.map f f ≫ cofreeRepresentation Y generator
      rw [cofreeRepresentation_generator, cofreeRepresentation_generator]
      apply prod.hom_ext <;> simp [swap]

/-- The full cofree functor requires precisely binary products. -/
def cofreeFunctor (C : Type v) [Category.{w} C] [HasBinaryProducts C] :
    C ⥤ Action C C2.{u} where
  obj := cofreeObject.{u}
  map := cofreeMap.{u}
  map_id _ := by apply Action.Hom.ext; simp [cofreeMap, cofreeObject]
  map_comp _ _ := by
    apply Action.Hom.ext
    apply prod.hom_ext <;> simp [cofreeMap]

omit [HasBinaryProducts C] in
/-- Every original C2 action generator squares to the original identity. -/
theorem actionGenerator_square (A : Action C C2.{u}) : A.ρ generator ≫ A.ρ generator = 𝟙 _ := by
  change A.ρ generator * A.ρ generator = 1
  rw [← A.ρ.map_mul, originalGenerator_mul_self, A.ρ.map_one]

/-- The extension pairs the input map with its actual generator translate. -/
def cofreeHomLift (A : Action C C2.{u}) (X : C) (f : A.V ⟶ X) :
    A ⟶ cofreeObject X where
  hom := prod.lift f (A.ρ generator ≫ f)
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · change A.ρ generator ≫ prod.lift f (A.ρ generator ≫ f) =
        prod.lift f (A.ρ generator ≫ f) ≫ cofreeRepresentation X generator
      rw [cofreeRepresentation_generator]
      apply prod.hom_ext
      · simp [swap]
      · simp [swap, ← Category.assoc, actionGenerator_square]

/-- The full original Hom equivalence has both inverse laws, not only a set-level bijection. -/
def cofreeHomEquiv (A : Action C C2.{u}) (X : C) :
    (A.V ⟶ X) ≃ (A ⟶ cofreeObject X) where
  toFun := cofreeHomLift A X
  invFun F := F.hom ≫ prod.fst
  left_inv f := by simp [cofreeHomLift]
  right_inv F := by
    apply Action.Hom.ext
    apply prod.hom_ext
    · simp [cofreeHomLift]
    · have hc := F.comm generator
      change A.ρ generator ≫ F.hom = F.hom ≫ cofreeRepresentation X generator at hc
      rw [cofreeRepresentation_generator] at hc
      simpa [cofreeHomLift, swap, Category.assoc] using congrArg (fun h ↦ h ≫ prod.fst) hc

/-- Forgetting the action is left adjoint to the actual binary-product cofree functor. -/
def forgetCofreeAdjunction (C : Type v) [Category.{w} C] [HasBinaryProducts C] :
    Action.forget C C2.{u} ⊣ cofreeFunctor C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A X ↦ cofreeHomEquiv.{u} A X
      homEquiv_naturality_left_symm := by
        intro A B X F G
        change (F ≫ G).hom ≫ prod.fst = F.hom ≫ (G.hom ≫ prod.fst)
        exact Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro A X Y F G
        apply Action.Hom.ext
        apply prod.hom_ext <;> simp [cofreeHomEquiv, cofreeHomLift, cofreeFunctor, cofreeMap,
          Category.assoc] }

end
end DaggerOriginalC2BinaryCofreeAdjunction
