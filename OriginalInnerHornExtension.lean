import OriginalInnerHornCompleteMaps

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornExtension

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces
open InnerHornCompleteMaps

variable {n : ℕ} {A : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))
variable (ell : extremeHom.{u} n ⟶
  (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))
variable (hl : (extremeHorn.{u} n k).ι ≫ ell = InnerHornGlue.hornMap k D)

include hl in
theorem completeMap_cut (v : interior n) :
    compose (ULift.up 0) (ULift.up v.val)
        (ULift.up (Fin.last (n + 1))) ≫ ell =
      (InnerHornProperMaps.properMap k D 0 v.val (leftProper v) ⊗ₘ
        InnerHornProperMaps.properMap k D v.val
          (Fin.last (n + 1)) (rightProper v)) ≫
            eComp SSet (D.obj 0) (D.obj v.val) (D.obj (Fin.last (n + 1))) := by
  calc
    _ = cutMap _ _ _ ≫ SSet.Subcomplex.homOfLE (cut_le_extremeHorn n k v) ≫
        (extremeHorn n k).ι ≫ ell := rfl
    _ = cutMap _ _ _ ≫ SSet.Subcomplex.homOfLE (cut_le_extremeHorn n k v) ≫
        InnerHornGlue.hornMap k D := by rw [hl]
    _ = cutMap _ _ _ ≫ InnerHornFacetMaps.cutEvaluation k D v := by
      rw [InnerHornGlue.hornMap_cut k D v]
    _ = _ := InnerHornFacetMaps.cutMap_evaluation k D v

include hl in
theorem completeMap_comp (i j l : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up j) (ULift.up l) ≫
      completeMap k D ell i l =
        (completeMap k D ell i j ⊗ₘ completeMap k D ell j l) ≫
          eComp SSet (D.obj i) (D.obj j) (D.obj l) := by
  by_cases ho : i ≤ j ∧ j ≤ l
  · by_cases hp : i = 0 ∧ l = Fin.last (n + 1)
    · rcases hp with ⟨rfl, rfl⟩
      by_cases hj0 : j = 0
      · subst j
        exact InnerHornCompleteMaps.completeMap_comp_left_unit
          k D ell 0 (Fin.last (n + 1))
      by_cases hjn : j = Fin.last (n + 1)
      · subst j
        exact InnerHornCompleteMaps.completeMap_comp_right_unit
          k D ell 0 (Fin.last (n + 1))
      let v : interior n := ⟨j, ⟨lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj0),
        lt_of_le_of_ne (Fin.le_last j) hjn⟩⟩
      rw [InnerHornCompleteMaps.completeMap_extreme,
        InnerHornCompleteMaps.completeMap_proper k D ell 0 j (leftProper v),
        InnerHornCompleteMaps.completeMap_proper k D ell j
          (Fin.last (n + 1)) (rightProper v)]
      exact completeMap_cut k D ell hl v
    · have hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)) := by
        rintro ⟨hi, hj⟩
        apply hp
        refine ⟨hi, le_antisymm (Fin.le_last l) ?_⟩
        exact hj ▸ ho.2
      have hpjl : ¬ (j = 0 ∧ l = Fin.last (n + 1)) := by
        rintro ⟨hj, hl'⟩
        apply hp
        refine ⟨le_antisymm ?_ (Fin.zero_le i), hl'⟩
        exact hj ▸ ho.1
      rw [InnerHornCompleteMaps.completeMap_proper k D ell i l hp,
        InnerHornCompleteMaps.completeMap_proper k D ell i j hpij,
        InnerHornCompleteMaps.completeMap_proper k D ell j l hpjl]
      exact InnerHornProperMaps.properMap_comp_forward k D i j l
        ho.1 ho.2 hp hpij hpjl
  · apply NatTrans.ext
    funext q p
    rcases p with ⟨γ, δ⟩
    exact False.elim (ho ⟨(γ.obj 0).le, (δ.obj 0).le⟩)

/-- The complete enriched simplex functor from the actual inner-horn data. -/
def extensionFunctor : T.obj ⦋n + 1⦌ ⟶ A where
  obj x := D.obj x.as.down
  map x y := completeMap k D ell x.as.down y.as.down
  map_id x := completeMap_id k D ell x.as.down
  map_comp x y z := completeMap_comp k D ell hl x.as.down y.as.down z.as.down

end

end DaggerOrdinaryRigidificationCof.InnerHornExtension
