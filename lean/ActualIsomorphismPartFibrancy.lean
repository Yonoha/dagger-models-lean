import ActualIsomorphismPartLocalWeakInvariance

/-! Unions of ALL isomorphism components of locally Kan original Homs are locally Kan. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualIsomorphismPartLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIsomorphismPartFibrancy
noncomputable section

theorem locallyKan (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) (x y : C.Obj) :
    SSet.KanComplex ((part C).enriched.Hom x y) := by
  have := hC x y
  have := inclusion_fibration C x y
  have ht : Fibration ((homSubcomplex C x y).ι ≫ terminal.from (C.enriched.Hom x y)) :=
    inferInstance
  have hf : IsFibrant (homSubcomplex C x y : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).mpr ht
  change SSet.KanComplex (homSubcomplex C x y : SSet.{u})
  infer_instance

end
end DaggerActualIsomorphismPartFibrancy
