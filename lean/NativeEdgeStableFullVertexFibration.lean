import OriginalFullVertexSubcomplexUniversal
import OriginalFullVertexPointedHomotopyComparison
import TopCatModelCategory.ModelCategorySSet

/-! A full vertex inclusion is a native Kan fibration when its vertices are stable along edges.
The ambient simplex in each lifting square is retained exactly, including both one-horn cases.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalFullVertexSubcomplex DaggerOriginalFullVertexPointedHomotopyComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeEdgeStableFullVertexFibration
noncomputable section

def EdgeStable {X : SSet.{u}} (V : Set (X.obj (op ⦋0⦌))) : Prop :=
  ∀ σ : (Δ[1] : SSet.{u}) ⟶ X,
    σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) ∈ V ↔
      σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 1) ∈ V

theorem inclusion_fibration {X : SSet.{u}} (V : Set (X.obj (op ⦋0⦌)))
    (hV : EdgeStable V) : Fibration (fullVertexSubcomplex X V).ι := by
  let ambient := X
  change Fibration (fullVertexSubcomplex ambient V).ι
  rw [fibration_iff]
  intro P Q f hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  constructor
  intro t σ sq
  have hv : ∀ w : (Δ[n + 1] : SSet.{u}).obj (op ⦋0⦌), σ.app (op ⦋0⦌) w ∈ V := by
    intro w
    cases n with
    | zero =>
      have hs := hV σ
      have hends : σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) ∈ V ∧
          σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 1) ∈ V := by
        fin_cases i
        · let z : (Λ[1, 0] : SSet.{u}).obj (op ⦋0⦌) :=
            ⟨SSet.stdSimplex.obj₀Equiv.symm 0, by
              apply SSet.face_le_horn (1 : Fin 2) 0 (by decide)
              rw [SSet.stdSimplex.mem_face_iff]
              intro j
              change (0 : Fin 2) ∈ ({1} : Finset (Fin 2))ᶜ
              decide⟩
          have he := congrFun (NatTrans.congr_app sq.w (op ⦋0⦌)) z
          change (t.app (op ⦋0⦌) z).val =
            σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) at he
          have h0 := he ▸ fullVertex_vertex_mem V (t.app (op ⦋0⦌) z)
          exact ⟨h0, hs.mp h0⟩
        · let z : (Λ[1, 1] : SSet.{u}).obj (op ⦋0⦌) :=
            ⟨SSet.stdSimplex.obj₀Equiv.symm 1, by
              apply SSet.face_le_horn (0 : Fin 2) 1 (by decide)
              rw [SSet.stdSimplex.mem_face_iff]
              intro j
              change (1 : Fin 2) ∈ ({0} : Finset (Fin 2))ᶜ
              decide⟩
          have he := congrFun (NatTrans.congr_app sq.w (op ⦋0⦌)) z
          change (t.app (op ⦋0⦌) z).val =
            σ.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 1) at he
          have h1 := he ▸ fullVertex_vertex_mem V (t.app (op ⦋0⦌) z)
          exact ⟨hs.mpr h1, h1⟩
      obtain ⟨v, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective w
      fin_cases v
      · exact hends.1
      · exact hends.2
    | succ n =>
      have hw : w ∈ (Λ[n + 2, i]).obj (op ⦋0⦌) := by
        rw [SSet.horn_obj_zero]
        trivial
      let z : (Λ[n + 2, i] : SSet.{u}).obj (op ⦋0⦌) := ⟨w, hw⟩
      have he := congrFun (NatTrans.congr_app sq.w (op ⦋0⦌)) z
      change (t.app (op ⦋0⦌) z).val = σ.app (op ⦋0⦌) w at he
      exact he ▸ fullVertex_vertex_mem V (t.app (op ⦋0⦌) z)
  let τ := liftMapOfVertices V σ hv
  refine CommSq.HasLift.mk' {
    l := τ
    fac_left := ?_
    fac_right := liftMapOfVertices_ι V σ hv }
  apply (cancel_mono (fullVertexSubcomplex ambient V).ι).mp
  rw [Category.assoc, liftMapOfVertices_ι]
  exact sq.w.symm

end
end DaggerNativeEdgeStableFullVertexFibration
