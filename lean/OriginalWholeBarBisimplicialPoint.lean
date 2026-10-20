import OriginalWholeBarReedyStrictFibre
import NativeReedyFibrantHorizontalMapping

/-! The original source vertex comes from the exact identity-chain bisimplicial point. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialCategoryBarFibre DaggerOriginalWholeBarBisimplicial
open DaggerOriginalWholeBarRelativeReedy DaggerOriginalWholeBarReedyStrictFibre
open DaggerNativeBisimplicialDiagonal DaggerNativeReedyFibrantHorizontalMapping
open DaggerNativeReedyRelativeReplacement
universe u
namespace DaggerOriginalWholeBarBisimplicialPoint
noncomputable section

def identityChain (C : SimplicialCat.{u, u}) (x : C.Obj)
    (h v : SimplexCategoryᵒᵖ) : ((baseRows C).obj h).obj v :=
  (Functor.const (Fin (h.unop.len + 1)) (C := degreeObjects C v)).obj x

theorem identityChain_vertical (C : SimplicialCat.{u, u}) (x : C.Obj)
    (h : SimplexCategoryᵒᵖ) {v w : SimplexCategoryᵒᵖ} (a : v ⟶ w) :
    ((baseRows C).obj h).map a (identityChain C x h v) = identityChain C x h w := by
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  exact heq_of_eq ((degreeMap C a).map_id x)

theorem identityChain_horizontal (C : SimplicialCat.{u, u}) (x : C.Obj)
    {h k : SimplexCategoryᵒᵖ} (a : h ⟶ k) (v : SimplexCategoryᵒᵖ) :
    ((baseRows C).map a).app v (identityChain C x h v) = identityChain C x k v := by
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  rfl

def sourcePoint (C : SimplicialCat.{u, u}) (x : C.Obj) : terminalBi ⟶ baseRows C where
  app h :=
    { app v _ := identityChain C x h v
      naturality v w a := by
        funext t
        exact (identityChain_vertical C x h a).symm }
  naturality h k a := by
    apply NatTrans.ext
    funext v t
    exact (identityChain_horizontal C x a v).symm

def diagonalPointIso : diagonalFunctor.obj terminalBi.{u} ≅ (Δ[0] : SSet.{u}) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

theorem sourcePoint_diagonal (C : SimplicialCat.{u, u}) (x : C.Obj) :
    diagonalFunctor.map (sourcePoint C x) ≫ (baseDiagonalIso C).hom =
      diagonalPointIso.hom ≫ sourceVertexMap C x := by
  apply NatTrans.ext
  rfl

theorem sourcePoint_diagonal_inv (C : SimplicialCat.{u, u}) (x : C.Obj) :
    diagonalPointIso.inv ≫ diagonalFunctor.map (sourcePoint C x) =
      sourceVertexMap C x ≫ (baseDiagonalIso C).inv := by
  apply NatTrans.ext
  rfl

theorem transported_point_diagonal (C : SimplicialCat.{u, u}) (x : C.Obj) :
    diagonalPointIso.inv ≫
      diagonalFunctor.map (sourcePoint C x ≫ baseUnit (barArrow C)) = point C x := by
  rw [Functor.map_comp, ← Category.assoc, sourcePoint_diagonal_inv, Category.assoc]
  rfl

end
end DaggerOriginalWholeBarBisimplicialPoint
