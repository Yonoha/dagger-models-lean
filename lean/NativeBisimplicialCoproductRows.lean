import NativeBisimplicialHorizontalMapping
import NativeCoproductLoopActionTrivial
import NativeCoproductReindexedWeak

/-! Native coproduct rows retain their exact summands, Kan property, actions and weak maps. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeCoproductLoopActionTrivial
open DaggerNativeUnitalMultiplicationAction DaggerNativeWeakMapTrivialAction
open DaggerNativeCoproductReindexedWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialCoproductRows
noncomputable section

def rowSigmaIso {I : Type u} (F : I → BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    (∐ fun i ↦ (F i).obj h) ≅ (∐ F).obj h :=
  asIso (sigmaComparison ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj h) F)

theorem rowSigmaIso_inclusion {I : Type u} (F : I → BiSSet.{u})
    (h : SimplexCategoryᵒᵖ) (i : I) :
    Limits.Sigma.ι (fun i ↦ (F i).obj h) i ≫ (rowSigmaIso F h).hom =
      (Limits.Sigma.ι F i).app h :=
  ι_comp_sigmaComparison ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj h) F i

instance coproduct_rows_Kan {I : Type u} (F : I → BiSSet.{u})
    [∀ i h, IsFibrant ((F i).obj h)] (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((∐ F).obj h) := by
  have : ∀ i, IsFibrant ((F i).obj h) := fun i ↦ inferInstance
  have : IsFibrant (∐ fun i ↦ (F i).obj h) := inferInstance
  exact isFibrant_of_fibration (rowSigmaIso F h).inv

theorem coproduct_row_actions_trivial {I : Type u} (F : I → BiSSet.{u})
    [∀ i h, IsFibrant ((F i).obj h)]
    (hF : ∀ i h x, TrivialActionAt ((F i).obj h) x) (h : SimplexCategoryᵒᵖ) :
    ∀ x, TrivialActionAt ((∐ F).obj h) x := by
  have : ∀ i, IsFibrant ((F i).obj h) := fun i ↦ inferInstance
  have : IsFibrant ((∐ F).obj h) := coproduct_rows_Kan F h
  exact all_trivial_actions_of_weak (rowSigmaIso F h).hom
    (coproduct_actions_trivial (fun i ↦ (F i).obj h) (fun i ↦ hF i h))

theorem row_map'_square {I J : Type u} {F : I → BiSSet.{u}} {G : J → BiSSet.{u}}
    (r : I → J) (f : ∀ i, F i ⟶ G (r i)) (h : SimplexCategoryᵒᵖ) :
    Limits.Sigma.map' r (fun i ↦ (f i).app h) ≫ (rowSigmaIso G h).hom =
      (rowSigmaIso F h).hom ≫ (Limits.Sigma.map' r f).app h := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_comp_map', Category.assoc, rowSigmaIso_inclusion]
  rw [← Category.assoc, rowSigmaIso_inclusion]
  exact (NatTrans.congr_app (Limits.Sigma.ι_comp_map' r f i) h).symm

theorem row_map'_weak {I J : Type u} {F : I → BiSSet.{u}} {G : J → BiSSet.{u}}
    (r : I → J) (hr : Function.Bijective r) (f : ∀ i, F i ⟶ G (r i))
    (hf : ∀ i h, WeakEquivalence ((f i).app h)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((Limits.Sigma.map' r f).app h) := by
  let rf : ∀ i, (F i).obj h ⟶ (G (r i)).obj h := fun i ↦ (f i).app h
  have : WeakEquivalence (C := SSet.{u})
      (Limits.Sigma.map' (f := fun i ↦ (F i).obj h) (g := fun j ↦ (G j).obj h) r rf) :=
    DaggerNativeCoproductReindexedWeak.map'_weak
      (X := fun i ↦ (F i).obj h) (Y := fun j ↦ (G j).obj h) r hr rf (fun i ↦ hf i h)
  have : WeakEquivalence (C := SSet.{u})
      (Limits.Sigma.map' (f := fun i ↦ (F i).obj h) (g := fun j ↦ (G j).obj h) r rf ≫
        (rowSigmaIso G h).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (row_map'_square r f h).symm

end
end DaggerNativeBisimplicialCoproductRows
