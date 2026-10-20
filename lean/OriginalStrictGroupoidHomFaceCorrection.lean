import OriginalStrictSimplicialGroupoidHomOperations

/-!
# Correct a face in the original strict simplicial groupoid Hom

The correction uses only the original mapping simplex, face, degeneracy, composition
and degree inverse. It works for arbitrary source and target objects. A compatible
operator square proves that another original face stays unchanged.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidHomOperations

universe u

namespace DaggerOriginalStrictGroupoidHomFaceCorrection

noncomputable section

/-- Correct the selected original face by a degenerate original automorphism of its source. -/
def correctedHom (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (s : op ⦋n⦌ ⟶ op ⦋n + 1⦌) (b : op ⦋n + 1⦌ ⟶ op ⦋n⦌)
    {x y : C.Obj} (w : PointHom C (n + 1) x y) (a : PointHom C n x y) :
    PointHom C (n + 1) x y :=
  pointComp C (n + 1)
    ((C.enriched.Hom x x).map s
      (pointComp C n a (pointInverse C hC n ((C.enriched.Hom x y).map b w)))) w

/-- A genuine degeneracy section makes the selected original face exactly the prescribed face.
-/
theorem correctedHom_selected (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (s : op ⦋n⦌ ⟶ op ⦋n + 1⦌) (b : op ⦋n + 1⦌ ⟶ op ⦋n⦌) (hs : s ≫ b = 𝟙 _)
    {x y : C.Obj} (w : PointHom C (n + 1) x y) (a : PointHom C n x y) :
    (C.enriched.Hom x y).map b (correctedHom C hC n s b w a) = a := by
  have hsection (r : PointHom C n x x) :
      (C.enriched.Hom x x).map b ((C.enriched.Hom x x).map s r) = r := by
    have h := congrFun ((C.enriched.Hom x x).map_comp s b) r
    simpa only [hs, (C.enriched.Hom x x).map_id] using h.symm
  rw [correctedHom, pointComp_map, hsection, pointComp_assoc, pointInverse_comp,
    pointComp_id]

/-- If the lower matching face agrees, the corresponding other original face is preserved. -/
theorem correctedHom_preserves (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    {n m k : ℕ} (s : op ⦋n⦌ ⟶ op ⦋n + 1⦌) (b : op ⦋n + 1⦌ ⟶ op ⦋n⦌)
    (i : op ⦋n + 1⦌ ⟶ op ⦋m⦌) (j : op ⦋n⦌ ⟶ op ⦋k⦌) (t : op ⦋k⦌ ⟶ op ⦋m⦌)
    (hsquare : s ≫ i = j ≫ t) {x y : C.Obj}
    (w : PointHom C (n + 1) x y) (a : PointHom C n x y)
    (hmatch : (C.enriched.Hom x y).map j a =
      (C.enriched.Hom x y).map j ((C.enriched.Hom x y).map b w)) :
    (C.enriched.Hom x y).map i (correctedHom C hC n s b w a) =
      (C.enriched.Hom x y).map i w := by
  let r := pointComp C n a (pointInverse C hC n ((C.enriched.Hom x y).map b w))
  have hkernel : (C.enriched.Hom x x).map j r = pointId C k x := by
    dsimp only [r]
    rw [pointComp_map, pointInverse_map, hmatch, pointComp_inverse]
  have hface : (C.enriched.Hom x x).map i ((C.enriched.Hom x x).map s r) =
      pointId C m x := by
    calc
      (C.enriched.Hom x x).map i ((C.enriched.Hom x x).map s r) =
          (C.enriched.Hom x x).map (s ≫ i) r :=
        (congrFun ((C.enriched.Hom x x).map_comp s i) r).symm
      _ = (C.enriched.Hom x x).map (j ≫ t) r := by rw [hsquare]
      _ = (C.enriched.Hom x x).map t ((C.enriched.Hom x x).map j r) :=
        congrFun ((C.enriched.Hom x x).map_comp j t) r
      _ = pointId C m x := by rw [hkernel, pointId_map]
  change (C.enriched.Hom x y).map i
    (pointComp C (n + 1) ((C.enriched.Hom x x).map s r) w) = _
  rw [pointComp_map, hface, pointId_comp]

/-- The lower correction uses the actual original j-th degeneracy and its lower face. -/
def lowerCorrection (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (j : Fin (n + 1)) {x y : C.Obj} (w : PointHom C (n + 1) x y)
    (a : PointHom C n x y) : PointHom C (n + 1) x y :=
  correctedHom C hC n (SimplexCategory.σ j).op (SimplexCategory.δ j.castSucc).op w a

/-- The lower correction sets its actual original face to the prescribed simplex. -/
theorem lowerCorrection_face (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (j : Fin (n + 1)) {x y : C.Obj} (w : PointHom C (n + 1) x y)
    (a : PointHom C n x y) : (C.enriched.Hom x y).δ j.castSucc
      (lowerCorrection C hC n j w a) = a := by
  apply correctedHom_selected
  simp only [← op_comp, SimplexCategory.δ_comp_σ_self, op_id]

/-- The upper correction uses the actual original j-th degeneracy and its upper face. -/
def upperCorrection (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (j : Fin (n + 1)) {x y : C.Obj} (w : PointHom C (n + 1) x y)
    (a : PointHom C n x y) : PointHom C (n + 1) x y :=
  correctedHom C hC n (SimplexCategory.σ j).op (SimplexCategory.δ j.succ).op w a

/-- The upper correction sets its actual original face to the prescribed simplex. -/
theorem upperCorrection_face (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    (j : Fin (n + 1)) {x y : C.Obj} (w : PointHom C (n + 1) x y)
    (a : PointHom C n x y) : (C.enriched.Hom x y).δ j.succ
      (upperCorrection C hC n j w a) = a := by
  apply correctedHom_selected
  simp only [← op_comp, SimplexCategory.δ_comp_σ_succ, op_id]

end

end DaggerOriginalStrictGroupoidHomFaceCorrection
