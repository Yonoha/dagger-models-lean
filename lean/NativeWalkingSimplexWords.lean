import NativeWalkingRelativeGenerators
import ThinNerveAdjacentDegeneracy
import TopCatModelCategory.SSet.PairingUnionProd

/-!
# Exact vertex words for the original simplex times walking-isomorphism nerve

Every original simplex is retained, in every dimension, with all simplicial operators.
The first coordinate is monotone; the Boolean coordinate is unrestricted.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory Opposite
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualWalkingIsoCategoricalCylinder
open DaggerNativeBoundaryCategoricalCylinder DaggerNativeWalkingRelativeGenerators
universe u
namespace DaggerNativeWalkingSimplexWords
noncomputable section

abbrev Words (n d : ℕ) :=
  {w : Fin (d + 1) → Fin (n + 1) × Bool // Monotone (fun i ↦ (w i).1)}

def parameterSimplex {d : ℕ} (t : Fin (d + 1) → Bool) : J.{u} _⦋d⦌ where
  obj i := parameterObject (t i)
  map _ := ⟨⟨⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem object_eta (z : walkingIso.{u}) : parameterObject (ULift.down z).as = z := by
  cases z
  rfl

def coordinates {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌) : Words n d :=
  ⟨fun i ↦ (x.1 i, (ULift.down (x.2.obj i)).as), SSet.stdSimplex.monotone_apply x.1⟩

def ofWords {n d : ℕ} (w : Words n d) : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌ :=
  (SSet.stdSimplex.objMk ⟨fun i ↦ (w.val i).1, w.property⟩,
    parameterSimplex (fun i ↦ (w.val i).2))

theorem coordinates_ofWords {n d : ℕ} (w : Words n d) : coordinates (ofWords w) = w := by
  rfl

theorem ofWords_coordinates {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌) :
    ofWords (coordinates x) = x := by
  apply Prod.ext
  · ext i
    rfl
  · apply nerve.ext_of_isThin
    funext i
    exact object_eta (x.2.obj i)

def wordEquiv (n d : ℕ) : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌ ≃ Words n d where
  toFun := coordinates
  invFun := ofWords
  left_inv := ofWords_coordinates
  right_inv := coordinates_ofWords

theorem coordinates_map {n d e : ℕ} (f : ⦋e⦌ ⟶ ⦋d⦌)
    (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌) (i : Fin (e + 1)) :
    (coordinates ((Δ[n] ⊗ J.{u}).map f.op x)).val i =
      (coordinates x).val (f.toOrderHom i) := rfl

theorem zero_iff {d : ℕ} (t : J.{u} _⦋d⦌) :
    t = time _ false ↔ ∀ i, (ULift.down (t.obj i)).as = false := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply nerve.ext_of_isThin
    funext i
    change t.obj i = parameterObject false
    rw [← object_eta (t.obj i), h i]

theorem notMem_relative_iff {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌) :
    x ∉ ((SSet.boundary n).unionProd zeroSubcomplex.{u}).obj _ ↔
      Function.Surjective (fun i ↦ ((coordinates x).val i).1) ∧
        ∃ i, ((coordinates x).val i).2 = true := by
  simp only [SSet.Subcomplex.mem_unionProd_iff, SSet.mem_boundary_iff_notMem_range,
    zeroSubcomplex, Set.mem_setOf_eq, zero_iff, not_or, not_exists, not_forall, not_not]
  constructor
  · rintro ⟨h, i, hi⟩
    refine ⟨fun j ↦ h j, i, ?_⟩
    change (ULift.down (x.2.obj i)).as = true
    cases hb : (ULift.down (x.2.obj i)).as <;> simp_all
  · rintro ⟨h, i, hi⟩
    refine ⟨h, i, ?_⟩
    change (ULift.down (x.2.obj i)).as = true at hi
    rw [hi]
    decide

end
end DaggerNativeWalkingSimplexWords
