import NativeTwoBeadSpineGeometry

/-! The exact final edge of the original cone simplex and its native face isomorphism. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerNativeTwoBeadSpineGeometry
universe u
namespace DaggerNativeRightConeFinalEdge
noncomputable section

def edgeSet (n : ℕ) : Finset (Fin (n + 2)) := {(Fin.last n).castSucc, (Fin.last n).succ}

def edgeVertex (n : ℕ) (i : Fin 2) : Fin (n + 2) :=
  ⟨n + i.val, by have hi := i.isLt; omega⟩

def edgeOrderIso (n : ℕ) : Fin 2 ≃o ↥(edgeSet n) where
  toFun i := ⟨edgeVertex n i, by
    fin_cases i
    · exact Finset.mem_insert.mpr (Or.inl (Fin.ext rfl))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext rfl)))⟩
  invFun x := ⟨x.val.val - n, by
    have hx := x.property
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    · rw [Finset.mem_singleton.mp hx]
      simp only [Fin.val_succ, Fin.val_last]
      omega⟩
  left_inv i := by
    apply Fin.ext
    change n + i.val - n = i.val
    omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change n + (x.val.val - n) = x.val.val
    have hx := x.property
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    · rw [Finset.mem_singleton.mp hx]
      simp only [Fin.val_succ, Fin.val_last]
      omega
  map_rel_iff' := by
    intro i j
    change n + i.val ≤ n + j.val ↔ i.val ≤ j.val
    omega

def edgeHom (n : ℕ) : ⦋1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkHom ⟨edgeVertex n, by
    intro i j hij
    change n + i.val ≤ n + j.val
    change i.val ≤ j.val at hij
    omega⟩

def edgeMap (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 1] := SSet.stdSimplex.map (edgeHom n)

def edgeIso (n : ℕ) : (Δ[1] : SSet.{u}) ≅ (lastEdge n : SSet.{u}) :=
  SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy (edgeSet n) 1 (edgeOrderIso n))

theorem edgeIso_hom (n : ℕ) : (edgeIso.{u} n).hom ≫ (lastEdge n).ι = edgeMap n := by
  apply NatTrans.ext
  funext q s
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  rfl

def prefixLast (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))

theorem edgeMap_first (n : ℕ) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ edgeMap.{u} n = prefixLast n ≫ face n := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
    SSet.stdSimplex.map (edgeHom n) =
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
      SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)))
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i : 3
  apply Fin.ext
  have hi : i.val = 0 := by have ht : i.val < 1 := i.isLt; omega
  change n + ((Fin.last 1).succAbove i).val =
    ((Fin.last (n + 1)).succAbove (Fin.last n)).val
  simp only [Fin.succAbove_last, Fin.val_castSucc, Fin.val_last]
  omega

theorem edgeMap_last (n : ℕ) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeMap.{u} n = lastVertex n := by
  rw [lastVertex_eq_inr]
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (edgeHom n) = _
  rw [← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i : 3
  apply Fin.ext
  have hi : i.val = 0 := by have ht : i.val < 1 := i.isLt; omega
  have hr := congrArg Fin.val (AugmentedSimplexCategory.inr'_eval ⦋n⦌ ⦋0⦌ i)
  have hr' : ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom i).val =
      n + 1 + i.val := by
    simpa only [Fin.val_cast, Fin.val_natAdd, SimplexCategory.len_mk] using hr
  change n + ((0 : Fin 2).succAbove i).val =
    ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom i).val
  rw [hr', Fin.succAbove_zero]
  simp only [Fin.val_succ]
  omega

end
end DaggerNativeRightConeFinalEdge
