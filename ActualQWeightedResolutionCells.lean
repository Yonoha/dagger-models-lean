import ActualQWeightedResolutionCofibrations
import NativeCostructuredChainDecomposition

/-! Keep all Q-weighted cells, with the whole degree chain and the whole final simplex. -/
set_option autoImplicit false
open CategoryTheory Opposite
open DaggerActualQWeightedResolutionNaturality DaggerNativeSimplicialReplacementCells
open DaggerNativeCostructuredChainDecomposition
open DaggerOriginalCounitRightConeQFunctor
universe u
namespace DaggerActualQWeightedResolutionCells
noncomputable section

abbrev DegreeChain (q : SimplexCategoryᵒᵖ) := Fin (q.unop.len + 1) ⥤ SimplexCategory

def RawCells (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :=
  Σ A : DegreeChain q,
    (uliftYoneda.{u}.obj (A.obj (Fin.last q.unop.len)) ⟶ X) ×
      (QFunctor.{u}.obj (A.obj 0)).obj k

/-- Both directions retain every degree arrow, entire last map, and entire Q parameter. -/
def cellEquiv (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :
    Cell (weights X) q k ≃ RawCells X q k where
  toFun x :=
    ⟨x.1 ⋙ ULiftHom.down.{0, u, u} ⋙ CostructuredArrow.proj uliftYoneda X,
      (ULiftHom.down.{0, u, u}.obj (x.1.obj (Fin.last q.unop.len))).hom, x.2⟩
  invFun x := ⟨chainLift uliftYoneda x.1 x.2.1 ⋙ ULiftHom.up.{0, u, u}, x.2.2⟩
  left_inv x := by
    have hc : chainLift uliftYoneda
        (x.1 ⋙ ULiftHom.down.{0, u, u} ⋙ CostructuredArrow.proj uliftYoneda X)
        (ULiftHom.down.{0, u, u}.obj (x.1.obj (Fin.last q.unop.len))).hom ⋙
          ULiftHom.up.{0, u, u} = x.1 := by
      change chainLift uliftYoneda
        ((x.1 ⋙ ULiftHom.down.{0, u, u}) ⋙ CostructuredArrow.proj uliftYoneda X)
        ((x.1 ⋙ ULiftHom.down.{0, u, u}).obj (Fin.last q.unop.len)).hom ⋙
          ULiftHom.up.{0, u, u} = x.1
      rw [← chain_reconstruct uliftYoneda (x.1 ⋙ ULiftHom.down.{0, u, u})]
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact Sigma.ext hc HEq.rfl
  right_inv x := by
    rcases x with ⟨A, f, t⟩
    exact Sigma.ext rfl (heq_of_eq (Prod.ext (chainLift_last uliftYoneda A f) rfl))

/-- Yoneda evaluates only the final map; every intermediate arrow and Q parameter remains. -/
def FlatCells (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :=
  Σ A : DegreeChain q,
    X.obj (op (A.obj (Fin.last q.unop.len))) × (QFunctor.{u}.obj (A.obj 0)).obj k

def rawToFlat (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :
    RawCells X q k ≃ FlatCells X q k :=
  Equiv.sigmaCongrRight (fun _ ↦ Equiv.prodCongr uliftYonedaEquiv (Equiv.refl _))

def flatEquiv (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :
    Cell (weights X) q k ≃ FlatCells X q k :=
  (cellEquiv X q k).trans (rawToFlat X q k)

/-- The original target map acts on the final simplex, retaining the whole degree chain. -/
def rawMap {X Y : SSet.{u}} (f : X ⟶ Y) (q k : SimplexCategoryᵒᵖ) :
    RawCells X q k → RawCells Y q k := fun x ↦ ⟨x.1, x.2.1 ≫ f, x.2.2⟩

/-- The same target map on the complete evaluated cell. -/
def flatMap {X Y : SSet.{u}} (f : X ⟶ Y) (q k : SimplexCategoryᵒᵖ) :
    FlatCells X q k → FlatCells Y q k :=
  fun x ↦ ⟨x.1, f.app (op (x.1.obj (Fin.last q.unop.len))) x.2.1, x.2.2⟩

/-- Naturality holds on the entire original weighted replacement, in every bidegree. -/
theorem cellEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (q k : SimplexCategoryᵒᵖ)
    (x : Cell (weights X) q k) :
    cellEquiv Y q k
      (((DaggerNativeSimplicialReplacementReindex.reindex
        (DaggerNativeSimplexIndexResolutionNaturality.indexMap f) (weights Y)).app q).app k x) =
      rawMap f q k (cellEquiv X q k x) := rfl

/-- The Yoneda coordinate is natural for the entire original last simplex map. -/
theorem flatEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (q k : SimplexCategoryᵒᵖ)
    (x : Cell (weights X) q k) :
    flatEquiv Y q k
      (((DaggerNativeSimplicialReplacementReindex.reindex
        (DaggerNativeSimplexIndexResolutionNaturality.indexMap f) (weights Y)).app q).app k x) =
      flatMap f q k (flatEquiv X q k x) := by
  change (rawToFlat Y q k) (rawMap f q k (cellEquiv X q k x)) =
    flatMap f q k ((rawToFlat X q k) (cellEquiv X q k x))
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Prod.ext
  · exact uliftYonedaEquiv_comp _ f
  · rfl

end
end DaggerActualQWeightedResolutionCells
