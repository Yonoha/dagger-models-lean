import NativeHornActionGluing
import NativePointEvaluationMappingFibreIso
import TopCatModelCategory.SSet.HomotopySequenceAction

/-! The glued action family lies above the original path under actual point evaluation. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeHornActionGluing DaggerOriginalFixedObjectCotensorPoints
universe u
namespace DaggerNativeHornActionEvaluationPath
noncomputable section

theorem restriction_of_vertex {A D X : SSet.{u}} (j : A ⟶ D)
    (v : ((ihom D).obj X) _⦋0⦌) (f : A ⟶ X)
    (h : ((MonoidalClosed.pre j).app X).app _ v = SSet.ihom₀Equiv.symm f) :
    j ≫ SSet.ihom₀Equiv v = f := by
  apply SSet.ihom₀Equiv.symm.injective
  rw [SSet.ihom₀Equiv_symm_comp, Equiv.symm_apply_apply]
  exact h

variable {n : ℕ} (i : Fin (n + 2)) {X : SSet.{u}} {x y : X _⦋0⦌}
  {p : Edge (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)}
  {f : X.PtSimplex n x} {g : X.PtSimplex n y}

theorem gluedMap_evaluation
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u})) (h : ActionStruct p f g) :
    curry (gluedMap i h) ≫
      pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X = p.map := by
  apply NatTrans.ext
  funext q t
  have ht := congrFun (NatTrans.congr_app (gluedMap_horn i h) q)
    (a.app q PUnit.unit, t)
  change (gluedMap i h).app q
    ((SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)).app q (a.app q PUnit.unit),
      (Δ[1] : SSet.{u}).map (𝟙 q) t) = p.map.app q t
  rw [FunctorToTypes.map_id_apply]
  exact ht

def evaluationActionStruct
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u})) (h : ActionStruct p f g)
    (v₀ v₁ : ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj X) _⦋0⦌)
    (h₀H : ((MonoidalClosed.pre
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _ v₀ =
        SSet.ihom₀Equiv.symm (SSet.const x))
    (h₀F : ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ v₀ =
      SSet.ihom₀Equiv.symm f.map)
    (h₁H : ((MonoidalClosed.pre
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _ v₁ =
        SSet.ihom₀Equiv.symm (SSet.const y))
    (h₁F : ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ v₁ =
      SSet.ihom₀Equiv.symm g.map) :
    FiberActionStruct
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) p v₀ v₁ where
  map := curry (gluedMap i h)
  map_p := gluedMap_evaluation i a h
  δ₁_map := by
    have he := (SSet.Homotopy.equiv (gluedHomotopy i h
      (SSet.ihom₀Equiv v₀) (SSet.ihom₀Equiv v₁)
      (restriction_of_vertex _ _ _ h₀H) (restriction_of_vertex _ _ _ h₀F)
      (restriction_of_vertex _ _ _ h₁H) (restriction_of_vertex _ _ _ h₁F))).comm₀
    simpa only [Equiv.symm_apply_apply] using he
  δ₀_map := by
    have he := (SSet.Homotopy.equiv (gluedHomotopy i h
      (SSet.ihom₀Equiv v₀) (SSet.ihom₀Equiv v₁)
      (restriction_of_vertex _ _ _ h₀H) (restriction_of_vertex _ _ _ h₀F)
      (restriction_of_vertex _ _ _ h₁H) (restriction_of_vertex _ _ _ h₁F))).comm₁
    simpa only [Equiv.symm_apply_apply] using he

end
end DaggerNativeHornActionEvaluationPath
