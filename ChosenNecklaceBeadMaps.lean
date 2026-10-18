import ChosenNecklaceUnion
import ChosenNecklaceMapVertices

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

theorem piece_le_complex (i : Option T.Bead) : pieces.{u} T i ≤ T.complex := by
  rw [← (cover.{u} T).iSup_eq]
  exact le_iSup T.pieces i

def pieceι (i : Option T.Bead) : (pieces.{u} T i).toSSet ⟶ T.toSSet :=
  SSet.Subcomplex.homOfLE (T.piece_le_complex i) ≫ T.complexIso.inv

theorem pieceι_inclusion (i : Option T.Bead) :
    T.pieceι i ≫ T.inclusion = (T.pieces i).ι := by
  simp [pieceι, inclusion, Category.assoc]

theorem pieceι_some (b : T.Bead) : T.pieceι (some b) = T.beadι b := by
  apply (cancel_mono T.inclusion).1
  rw [T.pieceι_inclusion, T.beadι_inclusion]
  rfl

/-- Every whole simplex map into a necklace factors through one actual bead or the point. -/
theorem simplex_factors_piece {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ T.toSSet) :
    ∃ i : Option T.Bead, ∃ g : Δ[n] ⟶ (T.pieces i).toSSet, g ≫ T.pieceι i = f := by
  let x := SSet.yonedaEquiv f
  have hx : T.inclusion.app _ x ∈ T.complex.obj (op ⦋n⦌) :=
    (T.complexIso.hom.app _ x).property
  obtain ⟨i, hi⟩ : ∃ i : Option T.Bead,
      T.inclusion.app _ x ∈ (T.pieces i).obj (op ⦋n⦌) := by
    rcases (T.mem_complex_iff _).mp hx with h | ⟨b, h⟩
    · exact ⟨none, SSet.stdSimplex.mem_face_iff _ _ |>.mpr (by simpa using h)⟩
    · exact ⟨some b, SSet.stdSimplex.mem_face_iff _ _ |>.mpr h⟩
  have hr : SSet.Subcomplex.range (f ≫ T.inclusion) ≤ T.pieces i := by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    exact hi
  refine ⟨i, SSet.Subcomplex.lift (f ≫ T.inclusion) hr, ?_⟩
  apply (cancel_mono T.inclusion).1
  rw [Category.assoc, T.pieceι_inclusion, SSet.Subcomplex.lift_ι]

theorem map_bead_factors {U : NecklaceCode} (f : T.toSSet ⟶ U.toSSet) (b : T.Bead) :
    ∃ i : Option U.Bead, ∃ g : Δ[b.length] ⟶ (U.pieces i).toSSet,
      g ≫ U.pieceι i = T.beadSimplex b ≫ f :=
  U.simplex_factors_piece (T.beadSimplex b ≫ f)

end

end DaggerChosenRigidificationNecklace.NecklaceCode
