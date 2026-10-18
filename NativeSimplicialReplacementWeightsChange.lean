import NativeSimplicialReplacement

/-! Apply an actual natural transformation to each whole original parameter simplex. -/
set_option autoImplicit false
open CategoryTheory Opposite HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplicialReplacementWeightsChange
noncomputable section

variable {C : Type u} [Category.{u} C] {G H : C ⥤ SSet.{u}} (η : G ⟶ H)

/-- Preserve the entire chain and apply the given full map to its original parameter simplex. -/
def changeWeights : replacement G ⟶ replacement H where
  app q :=
    { app k x := ⟨x.1, (η.app (first x.1)).app k x.2⟩
      naturality {k l} β := by
        funext x
        apply congrArg (fun t ↦ (⟨x.1, t⟩ : Cell H q l))
        exact congrFun ((η.app (first x.1)).naturality β) x.2 }
  naturality {q r} α := by
    apply NatTrans.ext
    funext k x
    apply congrArg (fun t ↦ (⟨(nerve C).map α x.1, t⟩ : Cell H r k))
    exact congrFun (NatTrans.congr_app (η.naturality (initialArrow α x.1)) k) x.2

def diagonalChange : DaggerBisimplicialDiagonal.diag (replacement G) ⟶
    DaggerBisimplicialDiagonal.diag (replacement H) :=
  DaggerBisimplicialDiagonal.diagMap (changeWeights η)

/-- The whole original chain projection remains exactly the same. -/
theorem projection_square : diagonalChange η ≫ diagonalProjection H = diagonalProjection G := by
  apply NatTrans.ext
  rfl

/-- Proved weak projections imply that this exact map of whole weighted replacements is weak. -/
theorem diagonalChange_GW
    (hG : GW (diagonalProjection G)) (hH : GW (diagonalProjection H)) :
    GW (diagonalChange η) := by
  have : WeakEquivalence (diagonalProjection G) := (weakEquivalence_iff_GW _).mpr hG
  have : WeakEquivalence (diagonalProjection H) := (weakEquivalence_iff_GW _).mpr hH
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_postcomp_iff (diagonalChange η) (diagonalProjection H)).mp
  rw [projection_square]
  infer_instance

/-- The given full natural transformations agree on every original augmentation cell. -/
theorem augmentation_square {X : SSet.{u}} (θ : H ⟶ (Functor.const C).obj X) :
    diagonalChange η ≫ diagonalAugmentation H θ = diagonalAugmentation G (η ≫ θ) := by
  apply NatTrans.ext
  rfl

end
end DaggerNativeSimplicialReplacementWeightsChange
