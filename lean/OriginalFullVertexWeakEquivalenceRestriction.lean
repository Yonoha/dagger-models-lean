import OriginalFullVertexPointedHomotopyComparison
import TopCatModelCategory.ModelCategorySSet

/-!
# Weak equivalences restricted to the original full vertex subcomplexes

The original inclusion is injective on components and bijective on positive
pointed homotopy groups. The actual restricted arrow retains the original
ambient map and commutes with both inclusions. Thus an ambient weak
equivalence restricts to a weak equivalence whenever the restricted arrow
is surjective on its actual components. No surjectivity on the selected
vertices themselves or saturation of their selected sets is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalFullVertexSubcomplex DaggerOriginalFullVertexPointedHomotopyComparison
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalFullVertexWeakEquivalenceRestriction

noncomputable section

/-- The original full inclusion reflects equality of actual connected components. -/
theorem inclusion_mapπ₀_injective {X : SSet.{u}} [SSet.KanComplex X]
    (V : Set (X _⦋0⦌)) : Function.Injective (SSet.mapπ₀ (fullVertexSubcomplex X V).ι) := by
  intro p q hpq
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective p
  apply (SSet.KanComplex.π₀EquivπZero a).injective
  apply inclusion_mapπ_injective V a 0
  have hp := congrFun (SSet.KanComplex.mapπ_comp_π₀EquivπZero
    (fullVertexSubcomplex X V).ι a a.val rfl) (SSet.π₀.mk a)
  have hq := congrFun (SSet.KanComplex.mapπ_comp_π₀EquivπZero
    (fullVertexSubcomplex X V).ι a a.val rfl) q
  dsimp only [Function.comp_apply] at hp hq
  rw [hp, hq, hpq]

variable {X Y : SSet.{u}} (V : Set (X _⦋0⦌)) (W : Set (Y _⦋0⦌))
variable (f : X ⟶ Y) (hV : ∀ x, x ∈ V → f.app (op ⦋0⦌) x ∈ W)

/-- The literal ambient arrow restricted to the two original full vertex subcomplexes. -/
def restrictedMap : (fullVertexSubcomplex X V : SSet.{u}) ⟶
    (fullVertexSubcomplex Y W : SSet.{u}) :=
  liftMapOfVertices W ((fullVertexSubcomplex X V).ι ≫ f) (by
    intro a
    exact hV a.val (fullVertex_vertex_mem V a))

/-- The original restricted arrow commutes with both literal original inclusions. -/
theorem restrictedMap_ι : restrictedMap V W f hV ≫ (fullVertexSubcomplex Y W).ι =
    (fullVertexSubcomplex X V).ι ≫ f :=
  liftMapOfVertices_ι _ _ _

/-- The corresponding square of native pointed homotopy maps uses the same basepoint. -/
theorem restrictedMapπ_square (n : ℕ)
    (a : (fullVertexSubcomplex X V : SSet.{u}) _⦋0⦌) :
    SSet.KanComplex.mapπ (fullVertexSubcomplex Y W).ι n
        ((restrictedMap V W f hV).app (op ⦋0⦌) a) (f.app (op ⦋0⦌) a.val) rfl ∘
      SSet.KanComplex.mapπ (restrictedMap V W f hV) n a
        ((restrictedMap V W f hV).app (op ⦋0⦌) a) rfl =
    SSet.KanComplex.mapπ f n a.val (f.app (op ⦋0⦌) a.val) rfl ∘
      SSet.KanComplex.mapπ (fullVertexSubcomplex X V).ι n a a.val rfl := by
  rw [SSet.KanComplex.mapπ_comp_mapπ, SSet.KanComplex.mapπ_comp_mapπ]
  funext p
  obtain ⟨p, rfl⟩ := SSet.KanComplex.π.mk_surjective p
  simp only [SSet.KanComplex.mapπ_mk]
  apply congrArg SSet.KanComplex.π.mk
  apply SSet.Subcomplex.RelativeMorphism.ext
  change p.map ≫ (restrictedMap V W f hV ≫ (fullVertexSubcomplex Y W).ι) =
    p.map ≫ ((fullVertexSubcomplex X V).ι ≫ f)
  rw [restrictedMap_ι]

/-- The actual restricted arrow preserves all positive pointed homotopy groups bijectively. -/
theorem restrictedMapπ_positive_bijective [SSet.KanComplex X] [SSet.KanComplex Y]
    (hf : SSet.KanComplex.W f) (n : ℕ)
    (a : (fullVertexSubcomplex X V : SSet.{u}) _⦋0⦌) :
    Function.Bijective (SSet.KanComplex.mapπ (restrictedMap V W f hV) (n + 1) a
      ((restrictedMap V W f hV).app (op ⦋0⦌) a) rfl) := by
  have hB := inclusion_mapπ_positive_bijective W
    ((restrictedMap V W f hV).app (op ⦋0⦌) a) n
  rw [← Function.Bijective.of_comp_iff' hB]
  change Function.Bijective
    (SSet.KanComplex.mapπ (fullVertexSubcomplex Y W).ι (n + 1)
        ((restrictedMap V W f hV).app (op ⦋0⦌) a) (f.app (op ⦋0⦌) a.val) rfl ∘
      SSet.KanComplex.mapπ (restrictedMap V W f hV) (n + 1) a
        ((restrictedMap V W f hV).app (op ⦋0⦌) a) rfl)
  rw [restrictedMapπ_square]
  exact (hf.bijective _ _ _ rfl).comp (inclusion_mapπ_positive_bijective V a n)

/-- An actual ambient weak equivalence makes the restricted arrow injective on components. -/
theorem restrictedMapπ₀_injective [SSet.KanComplex X] [SSet.KanComplex Y]
    (hf : SSet.KanComplex.W f) : Function.Injective (SSet.mapπ₀ (restrictedMap V W f hV)) := by
  have hfi := ((SSet.KanComplex.isEquivalence_mapFundamentalGroupoid_iff f).1
    hf.isEquivalence).1.1
  intro p q hpq
  apply inclusion_mapπ₀_injective V
  apply hfi
  have h := congrArg (SSet.mapπ₀ (fullVertexSubcomplex Y W).ι) hpq
  simpa only [← SSet.mapπ₀_comp_apply, restrictedMap_ι] using h

/-- The actual restriction is a native Kan weak equivalence if its actual components are covered. -/
theorem restrictedMap_kanWeakEquivalence [SSet.KanComplex X] [SSet.KanComplex Y]
    (hf : SSet.KanComplex.W f)
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (restrictedMap V W f hV))) :
    SSet.KanComplex.W (restrictedMap V W f hV) := by
  have hb : Function.Bijective (SSet.mapπ₀ (restrictedMap V W f hV)) :=
    ⟨restrictedMapπ₀_injective V W f hV hf, hπ₀⟩
  apply SSet.KanComplex.W.mk
  · apply (SSet.KanComplex.isEquivalence_mapFundamentalGroupoid_iff _).2
    refine ⟨hb, ?_⟩
    rintro a _ rfl
    exact restrictedMapπ_positive_bijective V W f hV hf 0 a
  · rintro n a _ rfl
    cases n with
    | zero => exact (SSet.KanComplex.bijective_mapπ₀_iff_bijective_mapπ_zero _ _ _ rfl).2 hb
    | succ n => exact restrictedMapπ_positive_bijective V W f hV hf n a

/-- The exact restricted map is a weak equivalence in the existing simplicial model structure. -/
theorem restrictedMap_weakEquivalence [SSet.KanComplex X] [SSet.KanComplex Y]
    [WeakEquivalence f]
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (restrictedMap V W f hV))) :
    WeakEquivalence (restrictedMap V W f hV) :=
  (SSet.weakEquivalence_iff_kanComplexW _).2
    (restrictedMap_kanWeakEquivalence V W f hV
      ((SSet.weakEquivalence_iff_kanComplexW f).1 inferInstance) hπ₀)

end

end DaggerOriginalFullVertexWeakEquivalenceRestriction
