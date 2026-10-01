import DaggerModels.RelativeCellBoundary
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
Independent ordinary boundary-cell data for the Kan--Quillen foundation.
The mathematical skeletal route is also used by joelriou/topcat-model-category,
but no Lean implementation from that repository is copied here. The proofs use
pinned Mathlib and this project's previously checked relative-cell lemmas.
-/

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra

universe u

namespace DaggerModels.SSetBoundaryCells

noncomputable section

/-- The actual pointwise disjoint union of copies of one simplicial set. -/
def copies (R : Type u) (K : SSet.{u}) : SSet.{u} where
  obj n := Σ _ : R, K.obj n
  map α x := ⟨x.1, K.map α x.2⟩
  map_id n := by
    funext x
    exact congrArg (Sigma.mk x.1) (congrFun (K.map_id n) x.2)
  map_comp α β := by
    funext x
    exact congrArg (Sigma.mk x.1) (congrFun (K.map_comp α β) x.2)

/-- The canonical inclusions of the actual disjoint-union coproduct. -/
def copiesInclusion (R : Type u) (K : SSet.{u}) (r : R) : K ⟶ copies R K where
  app n x := ⟨r, x⟩

def copiesCofan (R : Type u) (K : SSet.{u}) : Cofan (fun _ : R ↦ K) :=
  Cofan.mk (copies R K) (copiesInclusion R K)

/-- Each simplex of the coproduct retains its actual summand label. -/
def copiesDesc {R : Type u} {K Y : SSet.{u}} (f : R → (K ⟶ Y)) :
    copies R K ⟶ Y where
  app n x := (f x.1).app n x.2
  naturality n m α := by
    funext x
    exact congrFun ((f x.1).naturality α) x.2

/-- The explicit disjoint union has the full simplicial coproduct universal property. -/
def copiesIsColimit (R : Type u) (K : SSet.{u}) : IsColimit (copiesCofan R K) where
  desc s := copiesDesc (fun r ↦ s.ι.app ⟨r⟩)
  fac s j := by
    ext n x
    rfl
  uniq s f h := by
    ext n x
    exact congrFun (NatTrans.congr_app (h ⟨x.1⟩) n) x.2

/-- The coproduct of one actual simplicial map, with summand labels unchanged. -/
def copiesMap (R : Type u) {K L : SSet.{u}} (f : K ⟶ L) :
    copies R K ⟶ copies R L where
  app n x := ⟨x.1, f.app n x.2⟩
  naturality n m α := by
    funext x
    exact congrArg (Sigma.mk x.1) (congrFun (f.naturality α) x.2)

variable {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]

/-- The original Mathlib relative stage, with no change of target or simplex operators. -/
abbrev stage (n : ℕ) : SSet.{u} := (SSet.skeletonOfMono i n).toSSet

/-- Every newly attached nondegenerate simplex is retained individually, including vertices. -/
def Cells (n : ℕ) : Type u :=
  { σ : Y.nonDegenerate n // σ.1 ∉ Set.range (i.app (op ⦋n⦌)) }

/-- The actual characteristic map factors through the next relative stage. -/
def cellLift {n : ℕ} (σ : Y.nonDegenerate n) : (Δ[n] : SSet.{u}) ⟶ stage i (n + 1) :=
  SSet.Subcomplex.lift (SSet.yonedaEquiv.symm σ.1) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    simpa only [Equiv.apply_symm_apply] using
      (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i σ (n + 1)).mpr
        (Or.inr (Nat.lt_succ_self n)))

@[simp]
theorem cellLift_app_val {n : ℕ} (σ : Y.nonDegenerate n)
    (k : SimplexCategoryᵒᵖ) (x : (Δ[n] : SSet.{u}).obj k) :
    ((cellLift i σ).app k x).1 = Y.map x.down.op σ.1 := rfl

/-- The real boundary lands in the previous stage, without monicity of the cell map. -/
def boundaryLift {n : ℕ} (σ : Cells i n) :
    (SSet.boundary.{u} n).toSSet ⟶ stage i n :=
  SSet.Subcomplex.lift ((SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm σ.1.1) (by
    intro k y hy
    obtain ⟨a, rfl⟩ := hy
    change a.1 ∈ ((SSet.skeletonOfMono i n).preimage
      (SSet.yonedaEquiv.symm σ.1.1)).obj k
    rw [RelativeCellBoundary.characteristic_preimage_relativeSkeleton i n σ.1 σ.2]
    exact a.2)

/-- The genuine monic successor inclusion. -/
def step (n : ℕ) : stage i n ⟶ stage i (n + 1) :=
  SSet.Subcomplex.homOfLE ((SSet.skeletonOfMono i).monotone (Nat.le_succ n))

theorem boundaryLift_step {n : ℕ} (σ : Cells i n) :
    boundaryLift i σ ≫ step i n = (SSet.boundary n).ι ≫ cellLift i σ.1 := by
  ext k a
  exact Subtype.ext rfl

/-- The actual relative skeletal diagram, with the original image as stage zero. -/
def filtration : ℕ ⥤ SSet.{u} where
  obj n := stage i n
  map f := SSet.Subcomplex.homOfLE ((SSet.skeletonOfMono i).monotone (leOfHom f))

/-- The original inclusions of each actual stage into the fixed target. -/
def inclusion : filtration i ⟶ (Functor.const ℕ).obj Y where
  app n := (SSet.skeletonOfMono i n).ι

/-- The mono identifies its original source with the actual zeroth relative stage. -/
def zeroMap : X ⟶ (filtration i).obj 0 :=
  SSet.Subcomplex.toRange i ≫
    (SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i).symm).hom

def zeroIso : X ≅ (filtration i).obj 0 := by
  let : IsIso (zeroMap i) := by
    change IsIso (SSet.Subcomplex.toRange i ≫
      (SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i).symm).hom)
    infer_instance
  exact asIso (zeroMap i)

theorem zeroIso_inclusion : (zeroIso i).hom ≫ (inclusion i).app 0 = i := rfl

/-- Every simplex appears in the actual diagram, whose target is literally the original target. -/
def filtrationIsColimit : IsColimit (Cocone.mk Y (inclusion i)) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    refine ⟨n.unop.len + 1, ⟨x, ?_⟩, rfl⟩
    exact SSet.skeleton_le_skeletonOfMono i _ _
      (Y.mem_skeleton (i := n.unop.len) x (by omega))
  · intro j x y he
    exact ⟨j, 𝟙 j, Subtype.ext he⟩

/-- The countable transfinite composition retains both the original source and original map. -/
def transfiniteComposition : TransfiniteCompositionOfShape ℕ i where
  F := filtration i
  isoBot := (zeroIso i).symm
  incl := inclusion i
  isColimit := filtrationIsColimit i
  fac := zeroIso_inclusion i

end
end DaggerModels.SSetBoundaryCells
