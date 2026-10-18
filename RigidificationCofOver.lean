import RigidificationCofProperLaws

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A B : SC.{u}}

theorem canonicalFaceFunctor_eq (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ) :
    canonicalFaceFunctor a s hs hp = faceFunctor a s hs hp :=
  reobject_self _ _ _

def topWithVertices (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) : T.obj ⦋n + 1⦌ ⟶ B :=
  reobject (top b) (fun x => p.obj (vertex a x.as.down))
    (fun x => (vertex_over a b p sq x.as.down).symm)

theorem topWithVertices_eq (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) :
    topWithVertices a b p sq = top b := reobject_self _ _ _

theorem faceFunctor_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ) :
    canonicalFaceFunctor a s hs hp ≫ p =
      SimplicialThickening.functor (subsetEmbedding.{u} s).toOrderHom ≫
        topWithVertices a b p sq := by
  rw [canonicalFaceFunctor_eq, topWithVertices_eq]
  unfold faceFunctor
  rw [Category.assoc, simplex_over (n := ⦋n + 1⦌) a b p sq,
    ← Category.assoc]
  congr 1
  change EnrichedFunctor.comp SSet
    (SimplicialThickening.functor (faceBackward s hs).uliftMap)
    (SimplicialThickening.functor (faceOrdinal s hs).toOrderHom.uliftMap) = _
  rw [← SimplicialThickening.functor_comp]
  congr 1
  apply DFunLike.ext
  intro x
  apply ULift.ext
  change ((faceOrderIso s hs) ((faceOrderIso s hs).symm x.down)).val = x.down.val
  simp only [OrderIso.apply_symm_apply]

theorem enriched_map_heq {E D : SC.{u}} {F G : E ⟶ D} (h : F = G) (x y : E.Obj) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

theorem faceMap_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    faceMap a s hs hp i j hi hj ≫ p.map (vertex a i) (vertex a j) =
      homFromFace s i j hi hj ≫
        (topWithVertices a b p sq).map (.mk (ULift.up i)) (.mk (ULift.up j)) :=
  eq_of_heq (enriched_map_heq (faceFunctor_over a b p sq s hs hp)
    (label s i hi) (label s j hj))

theorem forwardProperMap_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (i j : Fin (n + 2)) (hij : i ≤ j) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    forwardProperMap a i j hij hp ≫ p.map (vertex a i) (vertex a j) =
      (topWithVertices a b p sq).map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  apply (cancel_epi (intervalHomIso.{u} i j hij).hom).mp
  change homFromFace (Finset.Icc i j) i j _ _ ≫ _ = _
  rw [← Category.assoc, forwardProperMap_restrict a i j hij hp
    (Finset.Icc i j) (intervalNonempty i j hij) (intervalProper i j hp) _ _,
    faceMap_over a b p sq]
  rfl

end

end DaggerOrdinaryRigidificationCof.BoundaryData
