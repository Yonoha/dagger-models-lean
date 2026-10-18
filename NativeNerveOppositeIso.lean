import OriginalNerveOppositeMap
import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# Native nerve comparison with simplicial opposite

Complete the retained whole nerve comparison using Mathlib's composable-arrow reversal.
The comparison is a natural isomorphism and satisfies the exact double-opposite coherence.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalNerveOppositeMap
universe v u
namespace DaggerNativeNerveOppositeIso
noncomputable section

/-- The existing reverse-diagram operation has the existing inverse on whole diagrams. -/
theorem reverseDiagram_inverse {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) :
    ((ComposableArrows.opEquivalence C n).inverse.obj (reverseDiagram s)).unop = s := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j f ↦ ?_)
  · change s.obj i.rev.rev = s.obj i
    simp only [Fin.rev_rev]
  · dsimp [reverseDiagram, ComposableArrows.opEquivalence]
    calc
      _ = s.map (eqToHom (Fin.rev_rev i) ≫ f ≫ eqToHom (Fin.rev_rev j).symm) :=
        congrArg s.map (Subsingleton.elim _ _)
      _ = _ := by simp only [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- The same existing inverse is also a right inverse on whole reversed diagrams. -/
theorem inverse_reverseDiagram {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows Cᵒᵖ n) :
    reverseDiagram ((ComposableArrows.opEquivalence C n).inverse.obj s).unop = s := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j f ↦ ?_)
  · change s.obj i.rev.rev = s.obj i
    simp only [Fin.rev_rev]
  · dsimp [reverseDiagram, ComposableArrows.opEquivalence]
    calc
      _ = s.map (eqToHom (Fin.rev_rev i) ≫ f ≫ eqToHom (Fin.rev_rev j).symm) :=
        congrArg s.map (Subsingleton.elim _ _)
      _ = _ := by simp only [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- Two reversals followed by the native double-opposite comparison are the identity. -/
theorem reverseDiagram_twice {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) : reverseDiagram (reverseDiagram s) ⋙ unopUnop C = s := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j f ↦ ?_)
  · change s.obj i.rev.rev = s.obj i
    simp only [Fin.rev_rev]
  · dsimp [reverseDiagram, ComposableArrows.opEquivalence]
    calc
      _ = s.map (eqToHom (Fin.rev_rev i) ≫ f ≫ eqToHom (Fin.rev_rev j).symm) :=
        congrArg s.map (Subsingleton.elim _ _)
      _ = _ := by simp only [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- The comparison is a bijection on all native simplices in each degree. -/
def degreeEquiv (C : Type u) [Category.{v} C] (q : SimplexCategoryᵒᵖ) :
    (nerve C).op.obj q ≃ (nerve Cᵒᵖ).obj q :=
  SSet.opObjEquiv.trans
    { toFun := reverseDiagram
      invFun := fun s ↦ ((ComposableArrows.opEquivalence C q.unop.len).inverse.obj s).unop
      left_inv := reverseDiagram_inverse
      right_inv := inverse_reverseDiagram }

/-- The retained original nerve map is an isomorphism of entire simplicial sets. -/
def nerveOppositeIso (C : Type u) [Category.{v} C] : (nerve C).op ≅ nerve Cᵒᵖ :=
  NatIso.ofComponents (fun q ↦ (degreeEquiv C q).toIso)
    (fun f ↦ (nerveOppositeMap C).naturality f)

/-- The forward map is exactly the previously fixed native reversal map. -/
theorem nerveOppositeIso_hom (C : Type u) [Category.{v} C] :
    (nerveOppositeIso C).hom = nerveOppositeMap C := rfl

/-- The comparison is natural for every actual functor between native categories. -/
def nerveOppositeNatIso :
    nerveFunctor.{u, u} ⋙ SSet.opFunctor ≅ Cat.opFunctor ⋙ nerveFunctor :=
  NatIso.ofComponents (fun C ↦ nerveOppositeIso C) (fun {C D} F ↦ by
    ext q s
    change reverseDiagram (SSet.opObjEquiv s ⋙ F.toFunctor) =
      reverseDiagram (SSet.opObjEquiv s) ⋙ F.toFunctor.op
    rfl)

/-- The natural isomorphism retains both native double-opposite comparison maps. -/
theorem nerveOppositeNatIso_coherence (C : Cat.{u, u}) :
    SSet.opFunctor.map (nerveOppositeNatIso.hom.app C) ≫
        nerveOppositeNatIso.hom.app (Cat.opFunctor.obj C) ≫
          nerveFunctor.map (Cat.opFunctorInvolutive.hom.app C) =
      SSet.opFunctorCompOpFunctorIso.hom.app (nerveFunctor.obj C) := by
  ext q s
  change reverseDiagram (reverseDiagram (SSet.opObjEquiv (SSet.opObjEquiv s))) ⋙
    unopUnop C = SSet.opObjEquiv (SSet.opObjEquiv s)
  exact reverseDiagram_twice _

end
end DaggerNativeNerveOppositeIso
