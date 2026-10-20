import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Faithful object injections preserve entire chains, and mono postcomposition preserves indices. -/
set_option autoImplicit false
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ v₃
namespace DaggerNativeFullChainInjectivity

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Retain every chain arrow, including all endpoint transports in the equality. -/
theorem postcomp_injective (F : C ⥤ D) [F.Faithful] (hF : Function.Injective F.obj)
    (K : Type u) [Category.{v} K] : Function.Injective (fun G : K ⥤ C ↦ G ⋙ F) := by
  intro G H h
  have ho : ∀ k, G.obj k = H.obj k := fun k ↦ hF (Functor.congr_obj h k)
  apply CategoryTheory.Functor.ext ho ?_
  intro i j α
  apply F.map_injective
  simpa only [CategoryTheory.Functor.map_comp, eqToHom_map] using Functor.congr_hom h α

/-- Cancel a mono even when the original sources have only been identified by an equality. -/
theorem postcomp_heq {A B X Y : D} (f : A ⟶ B) [Mono f]
    (g : X ⟶ A) (h : Y ⟶ A) (hXY : X = Y) (hg : HEq (g ≫ f) (h ≫ f)) : HEq g h := by
  cases hXY
  exact heq_of_eq ((cancel_mono f).mp (eq_of_heq hg))

/-- Equality of comma objects preserves their entire structure map heterogeneously. -/
theorem comma_hom_heq {A : Type u} [Category.{v} A] {B : Type w} [Category.{v₃} B]
    {L : A ⥤ D} {R : B ⥤ D} {P Q : Comma L R} (h : P = Q) : HEq P.hom Q.hom := by
  cases h
  rfl

/-- Recover the complete comma object from both objects and the full structure map. -/
theorem comma_object_eq {A : Type u} [Category.{v} A] {B : Type w} [Category.{v₃} B]
    {L : A ⥤ D} {R : B ⥤ D} {P Q : Comma L R}
    (hl : P.left = Q.left) (hr : P.right = Q.right) (hh : HEq P.hom Q.hom) : P = Q := by
  cases P
  cases Q
  cases hl
  cases hr
  cases eq_of_heq hh
  rfl

/-- Postcomposing the whole original simplex map with a mono is injective on index objects. -/
theorem costructured_map_obj_injective (S : C ⥤ D) {X Y : D} (f : X ⟶ Y) [Mono f] :
    Function.Injective (CostructuredArrow.map (S := S) f).obj := by
  intro P Q h
  have hl : P.left = Q.left := congrArg (fun R ↦ R.left) h
  apply comma_object_eq hl (Subsingleton.elim _ _)
  apply postcomp_heq f P.hom Q.hom (congrArg S.obj hl)
  exact comma_hom_heq h

end DaggerNativeFullChainInjectivity
