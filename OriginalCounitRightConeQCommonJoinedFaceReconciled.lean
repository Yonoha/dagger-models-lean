import OriginalCounitRightConeQCommonBaseFaceReconciled
import OriginalCounitRightConeQJoinVertexFormulaReconciled

/-!
# Large-simplex image of the explicit common old face

The joined map of `commonBaseHom` has precisely the large-simplex
vertices other than the two old vertices omitted by the cofaces. Its
last vertex is retained, as required by the actual collapsed-face cone.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQJoinVertexFormula

namespace DaggerOriginalCounitRightConeQCommonJoinedFace

noncomputable section

/-- Vertex image of the actual `joinHom` of the common old face. -/
theorem commonJoinHom_vertex_range (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) (v : Fin (n + 4)) :
    v ∈ Set.range (joinHom (commonBaseHom n i j hij)).toOrderHom ↔
      v ≠ i.castSucc ∧ v ≠ j.castSucc := by
  constructor
  · rintro ⟨z, rfl⟩
    cases z using Fin.lastCases with
    | last =>
        change (joinHom (commonBaseHom n i j hij)).toOrderHom
          (Fin.last (n + 1)) ≠ i.castSucc ∧
          (joinHom (commonBaseHom n i j hij)).toOrderHom
            (Fin.last (n + 1)) ≠ j.castSucc
        have hlast : (joinHom (commonBaseHom n i j hij)).toOrderHom
            (Fin.last (n + 1)) = Fin.last (n + 3) := by
          simpa using (joinHom_last (commonBaseHom n i j hij))
        rw [hlast]
        exact ⟨(Fin.castSucc_ne_last i).symm,
          (Fin.castSucc_ne_last j).symm⟩
    | cast w =>
        rw [joinHom_castSucc]
        have hw := (commonBaseHom_vertex_range n i j hij
          ((commonBaseHom n i j hij).toOrderHom w)).1 ⟨w, rfl⟩
        constructor
        · intro h
          exact hw.1 (Fin.castSucc_inj.mp h)
        · intro h
          exact hw.2 (Fin.castSucc_inj.mp h)
  · rintro ⟨hvi, hvj⟩
    cases v using Fin.lastCases with
    | last =>
        exact ⟨Fin.last (n + 1), by
          simpa using (joinHom_last (commonBaseHom n i j hij))⟩
    | cast w =>
        have hwi : w ≠ i := by
          intro h
          exact hvi (congrArg Fin.castSucc h)
        have hwj : w ≠ j := by
          intro h
          exact hvj (congrArg Fin.castSucc h)
        obtain ⟨z, hz⟩ :=
          (commonBaseHom_vertex_range n i j hij w).2 ⟨hwi, hwj⟩
        refine ⟨z.castSucc, ?_⟩
        rw [joinHom_castSucc, hz]

end

end DaggerOriginalCounitRightConeQCommonJoinedFace
