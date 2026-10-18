import OriginalFixedObjectGroupoidTerminals

/-!
# Retractions with a full path homotopy from two actual lifting properties

Only a terminal object, a prepath object, its categorical product and lifting
against the terminal and paired path maps are used. No model axioms are assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
universe u v

namespace DaggerOriginalFibrantPathLifting

noncomputable section

/-- An entire categorical retraction and an exact path from its other composite to identity. -/
structure RetractionPathData {C : Type u} [Category.{v} C] {A B : C}
    (i : A ⟶ B) (P : PrepathObject B) where
  r : B ⟶ A
  i_r : i ≫ r = 𝟙 A
  H : B ⟶ P.P
  H_p₀ : H ≫ P.p₀ = r ≫ i
  H_p₁ : H ≫ P.p₁ = 𝟙 B

/-- Two lifts produce the retraction and the path without a model-category premise. -/
def liftingRetractionPath {C : Type u} [Category.{v} C] [HasTerminal C]
    {A B : C} (i : A ⟶ B) (P : PrepathObject B) [HasBinaryProduct B B]
    [HasLiftingProperty i (terminal.from A)] [HasLiftingProperty i P.p] :
    RetractionPathData i P := by
  let sq : CommSq (𝟙 A) i (terminal.from A) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  let r := sq.lift
  have hr : i ≫ r = 𝟙 A := sq.fac_left
  have comm : (i ≫ P.ι) ≫ P.p = i ≫ prod.lift (r ≫ i) (𝟙 B) := by
    apply prod.hom_ext
    · simp only [Category.assoc, P.p_fst, prod.lift_fst, P.ι_p₀, Category.comp_id]
      rw [← Category.assoc, hr, Category.id_comp]
    · simp only [Category.assoc, P.p_snd, prod.lift_snd, P.ι_p₁, Category.comp_id]
  let pathSq : CommSq (i ≫ P.ι) i P.p (prod.lift (r ≫ i) (𝟙 B)) := ⟨comm⟩
  refine ⟨r, hr, pathSq.lift, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f ≫ prod.fst) pathSq.fac_right
    simpa only [Category.assoc, P.p_fst, prod.lift_fst] using h
  · have h := congrArg (fun f ↦ f ≫ prod.snd) pathSq.fac_right
    simpa only [Category.assoc, P.p_snd, prod.lift_snd] using h

end

end DaggerOriginalFibrantPathLifting
