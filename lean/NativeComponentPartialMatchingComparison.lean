import NativeHorizontalPiCompatibility
import TopCatModelCategory.SSet.PiZero

/-! The canonical component comparison retains every original horizontal evaluation map. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
universe u
namespace DaggerNativeComponentPartialMatchingComparison
noncomputable section

def componentRows (X : BiSSet.{u}) : SSet.{u} := X ⋙ SSet.π₀Functor

def vertexComponents (X : BiSSet.{u}) :
    X ⋙ SSet.evaluation.obj (op ⦋0⦌) ⟶ componentRows X :=
  Functor.whiskerLeft X SSet.toπ₀NatTrans

def componentComparison (K : SSet.{u}) (X : BiSSet.{u}) :
    (horizontalMapping K X).π₀ → (K ⟶ componentRows X) :=
  Quot.lift (fun a ↦ a ≫ vertexComponents X) (by
    rintro a b ⟨e, h₀, h₁⟩
    apply NatTrans.ext
    funext d x
    exact congrArg (SSet.mapπ₀ (evaluation K X d x)) (SSet.π₀.sound e h₀ h₁))

theorem componentComparison_value (K : SSet.{u}) (X : BiSSet.{u})
    (s : (horizontalMapping K X).π₀) (d : SimplexCategoryᵒᵖ) (x : K.obj d) :
    (componentComparison K X s).app d x = SSet.mapπ₀ (evaluation K X d x) s := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective s
  rfl

theorem componentComparison_restrict {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u})
    (s : (horizontalMapping L X).π₀) :
    componentComparison K X (SSet.mapπ₀ (horizontalPre i X) s) =
      i ≫ componentComparison L X s := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective s
  exact Category.assoc _ _ _

def simplexComponentEquiv (X : BiSSet.{u}) (m : ℕ) :
    (horizontalMapping (Δ[m] : SSet.{u}) X).π₀ ≃ ((Δ[m] : SSet.{u}) ⟶ componentRows X) :=
  (SSet.π₀Functor.mapIso (horizontalSimplexIso X m)).toEquiv.trans
    (SSet.yonedaEquiv (X := componentRows X) (n := ⦋m⦌)).symm

theorem simplex_componentComparison_eq (X : BiSSet.{u}) (m : ℕ) :
    componentComparison (Δ[m] : SSet.{u}) X = simplexComponentEquiv X m := by
  funext s
  apply SSet.yonedaEquiv.injective
  change (componentComparison (Δ[m] : SSet.{u}) X s).app (op ⦋m⦌) (topSimplex m) = _
  rw [componentComparison_value, evaluation_top]
  exact ((SSet.yonedaEquiv (X := componentRows X) (n := ⦋m⦌)).apply_symm_apply _).symm

theorem simplex_componentComparison_bijective (X : BiSSet.{u}) (m : ℕ) :
    Function.Bijective (componentComparison (Δ[m] : SSet.{u}) X) := by
  rw [simplex_componentComparison_eq]
  exact (simplexComponentEquiv X m).bijective

end
end DaggerNativeComponentPartialMatchingComparison
