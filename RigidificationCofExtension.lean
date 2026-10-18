import RigidificationCofCompleteMaps
import RigidificationCofBoundarySquare

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A B : SC.{u}}

variable (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (hl : (extremeBoundary n).ι ≫ ell = boundaryMap a)

include hl in
theorem completeMap_cut (k : interior n) :
    compose (ULift.up 0) (ULift.up k.val) (ULift.up (Fin.last (n + 1))) ≫ ell =
      (properMap a 0 k.val (leftProper k) ⊗ₘ
        properMap a k.val (Fin.last (n + 1)) (rightProper k)) ≫
          eComp SSet (vertex a 0) (vertex a k.val) (vertex a (Fin.last (n + 1))) := by
  calc
    _ = cutMap _ _ _ ≫ SSet.Subcomplex.homOfLE (cut_le_extremeBoundary n k) ≫
        (extremeBoundary n).ι ≫ ell := rfl
    _ = cutMap _ _ _ ≫ SSet.Subcomplex.homOfLE (cut_le_extremeBoundary n k) ≫
        boundaryMap a := by rw [hl]
    _ = cutMap _ _ _ ≫ cutEvaluation a k := by
      rw [boundaryMap_restrict a (Sum.inr k)]
      rfl
    _ = _ := cutMap_evaluation a k

include hl in
theorem completeMap_comp (i j k : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up j) (ULift.up k) ≫ completeMap a ell i k =
      (completeMap a ell i j ⊗ₘ completeMap a ell j k) ≫
        eComp SSet (vertex a i) (vertex a j) (vertex a k) := by
  by_cases ho : i ≤ j ∧ j ≤ k
  · by_cases hp : i = 0 ∧ k = Fin.last (n + 1)
    · rcases hp with ⟨rfl, rfl⟩
      by_cases hj0 : j = 0
      · subst j
        exact completeMap_comp_left_unit a ell 0 (Fin.last (n + 1))
      by_cases hjn : j = Fin.last (n + 1)
      · subst j
        exact completeMap_comp_right_unit a ell 0 (Fin.last (n + 1))
      let v : interior n := ⟨j, ⟨lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj0),
        lt_of_le_of_ne (Fin.le_last j) hjn⟩⟩
      rw [completeMap_extreme, completeMap_proper a ell 0 j (leftProper v),
        completeMap_proper a ell j (Fin.last (n + 1)) (rightProper v)]
      exact completeMap_cut a ell hl v
    · have hpij : ¬ (i = 0 ∧ j = Fin.last (n + 1)) := by
        rintro ⟨hi, hj⟩
        apply hp
        refine ⟨hi, le_antisymm (Fin.le_last k) ?_⟩
        exact hj ▸ ho.2
      have hpjk : ¬ (j = 0 ∧ k = Fin.last (n + 1)) := by
        rintro ⟨hj, hk⟩
        apply hp
        refine ⟨le_antisymm ?_ (Fin.zero_le i), hk⟩
        exact hj ▸ ho.1
      rw [completeMap_proper a ell i k hp, completeMap_proper a ell i j hpij,
        completeMap_proper a ell j k hpjk]
      exact properMap_comp_forward a i j k ho.1 ho.2 hp hpij hpjk
  · apply NatTrans.ext
    funext q p
    rcases p with ⟨γ, δ⟩
    exact False.elim (ho ⟨(γ.obj 0).le, (δ.obj 0).le⟩)

/-- The ENTIRE original enriched lift: objects, every Hom map, units and all triples. -/
def extensionFunctor : T.obj ⦋n + 1⦌ ⟶ A where
  obj x := vertex a x.as.down
  map x y := completeMap a ell x.as.down y.as.down
  map_id x := completeMap_id a ell x.as.down
  map_comp x y z := completeMap_comp a ell hl x.as.down y.as.down z.as.down

variable (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (hr : ell ≫ p.map (vertex a 0) (vertex a (Fin.last (n + 1))) =
      (topWithVertices a b p sq).map (.mk (ULift.up 0))
        (.mk (ULift.up (Fin.last (n + 1)))))

include hr in
theorem extensionFunctor_over : extensionFunctor a ell hl ≫ p = top b := by
  rw [← topWithVertices_eq a b p sq]
  change EnrichedFunctor.comp SSet (extensionFunctor a ell hl) p =
    topWithVertices a b p sq
  apply EnrichedFunctor.ext SSet
    (F := EnrichedFunctor.comp SSet (extensionFunctor a ell hl) p)
    (G := topWithVertices a b p sq) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change completeMap a ell x.as.down y.as.down ≫ _ = _
  by_cases hp : x.as.down = 0 ∧ y.as.down = Fin.last (n + 1)
  · rcases x with ⟨⟨xi⟩⟩
    rcases y with ⟨⟨yi⟩⟩
    rcases hp with ⟨rfl, rfl⟩
    rw [completeMap_extreme]
    exact hr
  · rw [completeMap_proper a ell _ _ hp]
    exact properMap_over a b p sq _ _ hp

end

end DaggerOrdinaryRigidificationCof.BoundaryData
