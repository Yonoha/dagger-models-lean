import SSetProductGeometric
import TopCatModelCategory.ModelCategorySSet

/-! Finite pointwise products preserve native weak equivalences using existing tensor weakness. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFinitePiWeak
noncomputable section

def piObject {n : ℕ} (X : Fin n → SSet.{u}) : SSet.{u} where
  obj d := ∀ i, (X i).obj d
  map α a i := (X i).map α (a i)
  map_id d := by funext a i; exact congrFun ((X i).map_id d) (a i)
  map_comp α β := by funext a i; exact congrFun ((X i).map_comp α β) (a i)

def piMap {n : ℕ} {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    piObject X ⟶ piObject Y where
  app d a i := (f i).app d (a i)
  naturality d e α := by funext a i; exact congrFun ((f i).naturality α) (a i)

def headTailEquiv {n : ℕ} (A : Fin (n + 1) → Type u) :
    (∀ i, A i) ≃ A 0 × (∀ i : Fin n, A i.succ) where
  toFun a := (a 0, fun i ↦ a i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv a := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := rfl

def piSuccIso {n : ℕ} (X : Fin (n + 1) → SSet.{u}) :
    piObject X ≅ X 0 ⊗ piObject (fun i ↦ X i.succ) :=
  NatIso.ofComponents (fun d ↦ (headTailEquiv (fun i ↦ (X i).obj d)).toIso) (by
    intro d e α
    funext a
    rfl)

theorem piSuccIso_natural {n : ℕ} {X Y : Fin (n + 1) → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) : piMap f ≫ (piSuccIso Y).hom =
      (piSuccIso X).hom ≫ (f 0 ⊗ₘ piMap (fun i ↦ f i.succ)) := by
  apply NatTrans.ext
  rfl

theorem piMap_weak {n : ℕ} {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, WeakEquivalence (f i)) : WeakEquivalence (piMap f) := by
  induction n with
  | zero =>
    have : IsIso (piMap f) := by
      refine ⟨⟨piMap (fun i ↦ Fin.elim0 i), ?_, ?_⟩⟩
      · apply NatTrans.ext
        funext d a i
        exact Fin.elim0 i
      · apply NatTrans.ext
        funext d a i
        exact Fin.elim0 i
    infer_instance
  | succ n ih =>
    have hw : WeakEquivalence (piMap (fun i ↦ f i.succ)) := ih _ (fun i ↦ hf i.succ)
    have ht : WeakEquivalence (f 0 ⊗ₘ piMap (fun i ↦ f i.succ)) :=
      (DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mp
        (DaggerSSetProductGeometric.tensorMap_geometric _ _
          ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr (hf 0))
          ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr hw))
    have := ht
    have : WeakEquivalence ((piSuccIso X).hom ≫
        (f 0 ⊗ₘ piMap (fun i ↦ f i.succ))) := inferInstance
    exact weakEquivalence_of_postcomp_of_fac (piSuccIso_natural f)

end
end DaggerNativeFinitePiWeak
