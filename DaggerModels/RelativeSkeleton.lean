import DaggerModels.FreeCofibration
import DaggerModels.ForgetfulReflection
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# Dagger-stable relative skeleta

The filtration in Part I, `dj.lem.free-cof`, is built from the image of the
original map and the ordinary skeleton. We restrict the original dagger to
these actual subcomplexes. Mathlib's `skeleton n` uses simplices of dimension
strictly less than `n`: stage zero is the image and stage `n + 1` is the
paper's stage containing all new nondegenerate simplices of dimension at most `n`.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

/-- A simplicial subcomplex is dagger-stable if it contains the dagger of each simplex. -/
def IsDaggerStable {X : DaggerSSet.{u}} (K : X.toSSet.Subcomplex) : Prop :=
  ∀ (n : ℕ) (x : X.toSSet _⦋n⦌), x ∈ K.obj (op ⦋n⦌) →
    X.daggerSimplex x ∈ K.obj (op ⦋n⦌)

/-- The restriction of the original dagger to a stable simplicial subcomplex. -/
def subcomplex {X : DaggerSSet.{u}} (K : X.toSSet.Subcomplex) (hK : IsDaggerStable K) :
    DaggerSSet.{u} where
  toSSet := K.toSSet
  dagger :=
    { app := fun n x ↦ ⟨X.dagger.app n x.1, hK n.unop.len x.1 x.2⟩
      naturality := by
        intro m n f
        funext x
        apply Subtype.ext
        exact congrFun (X.dagger.naturality f) x.1 }
  involutive n x := by
    apply Subtype.ext
    exact X.involutive n x.1
  fixedVertices x := by
    apply Subtype.ext
    exact X.fixedVertices x.1

/-- The genuine dagger-compatible inclusion of a stable subcomplex. -/
def subcomplexInclusion {X : DaggerSSet.{u}} (K : X.toSSet.Subcomplex)
    (hK : IsDaggerStable K) : subcomplex K hK ⟶ X where
  hom := K.ι
  comm := rfl

/-- Inclusions between stable subcomplexes commute with the restricted dagger. -/
def subcomplexHomOfLE {X : DaggerSSet.{u}} {K L : X.toSSet.Subcomplex}
    {hK : IsDaggerStable K} {hL : IsDaggerStable L} (h : K ≤ L) :
    subcomplex K hK ⟶ subcomplex L hL where
  hom := SSet.Subcomplex.homOfLE h
  comm := rfl

/-- Images of dagger-compatible maps are stable, without a monicity assumption. -/
theorem daggerStable_range {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    IsDaggerStable (SSet.Subcomplex.range f.hom) := by
  intro n y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨X.daggerSimplex x, f.dagger_comm x⟩

/-- A union of dagger-stable subcomplexes is stable. -/
theorem IsDaggerStable.sup {X : DaggerSSet.{u}} {K L : X.toSSet.Subcomplex}
    (hK : IsDaggerStable K) (hL : IsDaggerStable L) : IsDaggerStable (K ⊔ L) := by
  intro n x hx
  exact hx.elim (fun h ↦ Or.inl (hK n x h)) (fun h ↦ Or.inr (hL n x h))

/-- Reversal preserves the actual simplicial skeleton in every dimension. -/
theorem daggerStable_skeleton (X : DaggerSSet.{u}) (n : ℕ) :
    IsDaggerStable (X.toSSet.skeleton n) := by
  intro d x hx
  simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
    Set.mem_iUnion] at hx ⊢
  obtain ⟨i, y, hy⟩ := hx
  refine ⟨i, ⟨X.daggerSimplex y.1, (X.dagger_mem_nonDegenerate_iff y.1).2 y.2⟩, ?_⟩
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff] at hy ⊢
  obtain ⟨f, rfl⟩ := hy
  exact ⟨SimplexCategory.rev.map f, (X.dagger_map f y.1).symm⟩

section Relative

variable {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i]

local instance : Mono i.hom := (mono_iff_mono_hom i).1 inferInstance

/-- The relative skeleton of the given monomorphism is dagger-stable. -/
theorem daggerStable_skeletonOfMono (n : ℕ) :
    IsDaggerStable (SSet.skeletonOfMono i.hom n) :=
  (daggerStable_range i).sup (daggerStable_skeleton Y n)

/-- The actual relative skeletal filtration with its restricted dagger. -/
def relativeSkeleton : ℕ ⥤ DaggerSSet.{u} where
  obj n := subcomplex (SSet.skeletonOfMono i.hom n) (daggerStable_skeletonOfMono i n)
  map f := subcomplexHomOfLE ((SSet.skeletonOfMono i.hom).monotone (leOfHom f))

/-- The canonical compatible inclusions of all relative stages in the target. -/
def relativeSkeletonInclusion : relativeSkeleton i ⟶ (Functor.const ℕ).obj Y where
  app n := subcomplexInclusion _ (daggerStable_skeletonOfMono i n)

/-- The initial stage is the image of the original monomorphism. -/
def relativeSkeletonZeroMap : X ⟶ (relativeSkeleton i).obj 0 where
  hom := SSet.Subcomplex.toRange i.hom ≫
    (SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i.hom).symm).hom
  comm := by
    ext n x
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app i.comm n) x

/-- The initial stage is canonically isomorphic to the given source. -/
noncomputable def relativeSkeletonZeroIso : X ≅ (relativeSkeleton i).obj 0 := by
  let : forget.{u}.ReflectsIsomorphisms := forget_reflectsIsomorphisms
  let : IsIso (forget.map (relativeSkeletonZeroMap i)) := by
    change IsIso (SSet.Subcomplex.toRange i.hom ≫
      (SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i.hom).symm).hom)
    infer_instance
  let : IsIso (relativeSkeletonZeroMap i) := isIso_of_reflects_iso _ forget
  exact asIso (relativeSkeletonZeroMap i)

/-- The initial-stage identification preserves the original map into the target. -/
theorem relativeSkeletonZeroIso_hom_inclusion :
    (relativeSkeletonZeroIso i).hom ≫ (relativeSkeletonInclusion i).app 0 = i := rfl

/-- A nondegenerate simplex is in stage `n` precisely when it is old or has dimension `< n`. -/
theorem relativeSkeleton_nonDegenerate_membership {d : ℕ}
    (x : Y.toSSet.nonDegenerate d) (n : ℕ) :
    x.1 ∈ (SSet.skeletonOfMono i.hom n).obj (op ⦋d⦌) ↔
      x.1 ∈ Set.range (i.hom.app (op ⦋d⦌)) ∨ d < n :=
  SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i.hom x n

/-- Every simplex occurs in the actual relative skeletal filtration. -/
theorem relativeSkeleton_exhaustive :
    ⨆ n, SSet.skeletonOfMono i.hom n = ⊤ :=
  SSet.iSup_skeletonOfMono i.hom

/-- The target is the actual colimit of its relative skeletal filtration. -/
noncomputable def relativeSkeletonIsColimit :
    IsColimit (Cocone.mk Y (relativeSkeletonInclusion i)) := by
  let : ReflectsColimits forget.{u} := forget_reflectsColimits
  let : ReflectsColimitsOfSize.{0, 0} forget.{u} :=
    reflectsSmallestColimits_of_reflectsColimits forget
  apply isColimitOfReflects forget
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    refine ⟨n.unop.len + 1, ⟨x, ?_⟩, rfl⟩
    exact SSet.skeleton_le_skeletonOfMono i.hom _ _
      (Y.toSSet.mem_skeleton (i := n.unop.len) x (by omega))
  · intro j x y he
    refine ⟨j, 𝟙 j, ?_⟩
    exact Subtype.ext he

/-- The actual relative skeletal filtration, including its source and colimit identifications. -/
noncomputable def relativeSkeletonTransfiniteComposition :
    TransfiniteCompositionOfShape ℕ i where
  F := relativeSkeleton i
  isoBot := (relativeSkeletonZeroIso i).symm
  incl := relativeSkeletonInclusion i
  isColimit := relativeSkeletonIsColimit i
  fac := relativeSkeletonZeroIso_hom_inclusion i

/-- A monomorphism has its genuine relative skeletal filtration in the dagger category.
The stage isomorphisms preserve the specified inclusions in the target. -/
theorem exists_relativeSkeletonFiltration :
    ∃ t : TransfiniteCompositionOfShape ℕ i, ∀ n,
      ∃ e : (t.F.obj n).toSSet ≅
          (SSet.Subcomplex.range i.hom ⊔ Y.toSSet.skeleton n).toSSet,
        e.hom ≫ (SSet.Subcomplex.range i.hom ⊔ Y.toSSet.skeleton n).ι =
          (t.incl.app n).hom := by
  refine ⟨relativeSkeletonTransfiniteComposition i, fun n ↦ ⟨Iso.refl _, ?_⟩⟩
  exact Category.id_comp _

end Relative

end DaggerModels.DaggerSSet
