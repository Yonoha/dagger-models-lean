import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# The discrete simplicial set of vertices

The constant simplicial set on the vertices of `A` maps to the totally
degenerate simplices of both `A` and `A.op`. It gives the common simplicial
set in the explicit free dagger completion from Part I, `dj.not.adjunctions`.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels
namespace SSetVertices

/-- The constant simplicial set on the vertices of `A`. -/
def obj (A : SSet.{u}) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (A.obj (op ⦋0⦌))

/-- The inclusion sends each vertex to its total degeneracy in every dimension. -/
def inclusion (A : SSet.{u}) : obj A ⟶ A where
  app n x := A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x
  naturality {n m} f := by
    funext x
    change A.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x =
      A.map f.unop.op (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.eq_const_to_zero (f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0)]

/-- The canonical inclusion of the same vertices into the reversed simplicial set. -/
def opInclusion (A : SSet.{u}) : obj A ⟶ A.op where
  app n x := SSet.opObjEquiv.symm
    (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
  naturality {n m} f := by
    funext x
    change A.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x =
      A.map (SimplexCategory.rev.map f.unop).op
        (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.eq_const_to_zero
      (SimplexCategory.rev.map f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0)]
    rfl

/-- Reversal is the identity on the constant simplicial set of vertices. -/
def opIso (A : SSet.{u}) : obj A ≅ (obj A).op :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso (Equiv.refl _))

/-- A simplicial map induces its map on vertices in every constant dimension. -/
def map {A B : SSet.{u}} (f : A ⟶ B) : obj A ⟶ obj B where
  app _ := f.app (op ⦋0⦌)
  naturality {n m} g := by rfl

@[simp] theorem map_id (A : SSet.{u}) : map (𝟙 A) = 𝟙 (obj A) := by
  ext n x
  rfl

@[simp] theorem map_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    map (f ≫ g) = map f ≫ map g := by
  ext n x
  rfl

/-- Taking the constant simplicial set of vertices is functorial. -/
def functor : SSet.{u} ⥤ SSet.{u} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

@[simp] theorem inclusion_app_zero (A : SSet.{u}) (x : A.obj (op ⦋0⦌)) :
    (inclusion A).app (op ⦋0⦌) x = x := by
  simp only [inclusion, SimplexCategory.const_eq_id, op_id, A.map_id]
  rfl

@[simp] theorem opInclusion_app_zero (A : SSet.{u}) (x : A.obj (op ⦋0⦌)) :
    SSet.opObjEquiv ((opInclusion A).app (op ⦋0⦌) x) = x :=
  inclusion_app_zero A x

@[simp] theorem inclusion_app_zero_eq_id (A : SSet.{u}) :
    (inclusion A).app (op ⦋0⦌) = 𝟙 (A.obj (op ⦋0⦌)) := by
  funext x
  exact inclusion_app_zero A x

@[simp] theorem opInclusion_app_zero_eq_id (A : SSet.{u}) :
    (opInclusion A).app (op ⦋0⦌) = 𝟙 (A.obj (op ⦋0⦌)) := by
  funext x
  exact opInclusion_app_zero A x

instance inclusion_app_zero_isIso (A : SSet.{u}) :
    IsIso ((inclusion A).app (op ⦋0⦌)) := by
  rw [inclusion_app_zero_eq_id]
  infer_instance

instance opInclusion_app_zero_isIso (A : SSet.{u}) :
    IsIso ((opInclusion A).app (op ⦋0⦌)) := by
  rw [opInclusion_app_zero_eq_id]
  infer_instance

@[reassoc] theorem map_inclusion {A B : SSet.{u}} (f : A ⟶ B) :
    map f ≫ inclusion B = inclusion A ≫ f := by
  ext n x
  exact (congrFun (f.naturality (SimplexCategory.const n.unop ⦋0⦌ 0).op) x).symm

@[reassoc] theorem map_opInclusion {A B : SSet.{u}} (f : A ⟶ B) :
    map f ≫ opInclusion B = opInclusion A ≫ SSet.opFunctor.map f := by
  ext n x
  exact (congrFun (f.naturality (SimplexCategory.const n.unop ⦋0⦌ 0).op) x).symm

@[reassoc] theorem opIso_hom_op_inclusion (A : SSet.{u}) :
    (opIso A).hom ≫ SSet.opFunctor.map (inclusion A) = opInclusion A := by
  ext n x
  rfl

@[reassoc] theorem opIso_hom_op_opInclusion (A : SSet.{u}) :
    (opIso A).hom ≫ SSet.opFunctor.map (opInclusion A) =
      inclusion A ≫ SSet.opFunctorCompOpFunctorIso.inv.app A := by
  ext n x
  rfl

@[reassoc] theorem opIso_hom_op_opIso_hom (A : SSet.{u}) :
    (opIso A).hom ≫ SSet.opFunctor.map (opIso A).hom ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (obj A) = 𝟙 (obj A) := by
  ext n x
  rfl

@[reassoc] theorem map_opIso_hom {A B : SSet.{u}} (f : A ⟶ B) :
    map f ≫ (opIso B).hom = (opIso A).hom ≫ SSet.opFunctor.map (map f) := by
  ext n x
  rfl

instance inclusion_mono (A : SSet.{u}) : Mono (inclusion A) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  have h' := congrArg (A.map (SimplexCategory.const ⦋0⦌ n.unop 0).op) h
  change A.map (SimplexCategory.const ⦋0⦌ n.unop 0).op
    (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x) =
    A.map (SimplexCategory.const ⦋0⦌ n.unop 0).op
      (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op y) at h'
  simpa only [← FunctorToTypes.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    SimplexCategory.const_apply, SimplexCategory.const_eq_id, op_id, A.map_id] using h'

/-- The total-degeneracy map is a monomorphism. -/
theorem mono_inclusion (A : SSet.{u}) : Mono (inclusion A) := inferInstance

/-- Mathlib uses dimensions `< n` for `skeleton n`, so its `skeleton 1`
is precisely the manuscript's zero-skeleton of totally degenerate simplices. -/
theorem range_inclusion (A : SSet.{u}) :
    SSet.Subcomplex.range (inclusion A) = A.skeleton 1 := by
  ext n x
  change (∃ v : A.obj (op ⦋0⦌), (inclusion A).app n v = x) ↔
    x ∈ (A.skeleton 1).obj n
  constructor
  · rintro ⟨v, rfl⟩
    exact (A.skeleton 1).map (SimplexCategory.const n.unop ⦋0⦌ 0).op
      (A.mem_skeleton v (by decide))
  · intro hx
    simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
      Set.iUnion_coe_set, Set.mem_iUnion] at hx
    obtain ⟨i, y, _hy, hxy⟩ := hx
    obtain rfl : i = (0 : Fin 1) := Subsingleton.elim _ _
    obtain ⟨q, hq⟩ := (SSet.Subcomplex.mem_ofSimplex_obj_iff y x).1 hxy
    refine ⟨y, ?_⟩
    change A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op y = x
    rw [← SimplexCategory.eq_const_to_zero q]
    exact hq

/-- The constant simplicial set of vertices is the actual zero-skeleton subcomplex. -/
noncomputable def skeletonIso (A : SSet.{u}) : obj A ≅ (A.skeleton 1).toSSet :=
  asIso (SSet.Subcomplex.toRange (inclusion A)) ≪≫
    SSet.Subcomplex.eqToIso (range_inclusion A)

@[reassoc (attr := simp)] theorem skeletonIso_hom_inclusion (A : SSet.{u}) :
    (skeletonIso A).hom ≫ (A.skeleton 1).ι = inclusion A := by
  simp [skeletonIso, Category.assoc]

/-- The identification with the zero-skeleton preserves its canonical inclusion. -/
theorem exists_skeletonIso (A : SSet.{u}) :
    ∃ e : obj A ≅ (A.skeleton 1).toSSet, e.hom ≫ (A.skeleton 1).ι = inclusion A :=
  ⟨skeletonIso A, skeletonIso_hom_inclusion A⟩

end SSetVertices
end DaggerModels
