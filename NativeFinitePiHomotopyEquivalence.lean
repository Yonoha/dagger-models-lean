import NativeFinitePiHomotopyAction

/-! Native based homotopy classes of the exact finite pointwise product are coordinate classes. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerNativeFinitePiWeak DaggerNativeFinitePiKan DaggerNativeFinitePiHomotopyAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFinitePiHomotopyEquivalence
noncomputable section

def productPtSimplex {k n : ℕ} (X : Fin k → SSet.{u}) (a : (piObject X) _⦋0⦌)
    (p : ∀ i, (X i).PtSimplex n (a i)) : (piObject X).PtSimplex n a where
  map :=
    { app d t i := (p i).map.app d t
      naturality d e α := by
        funext t i
        exact congrFun ((p i).map.naturality α) t }
  comm := by
    rw [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply NatTrans.ext
    funext d t i
    have h : (SSet.boundary n).ι ≫ (p i).map = SSet.const (a i) := by
      simpa only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const] using (p i).comm
    exact congrFun (NatTrans.congr_app h d) t

def coordinateClasses {k n : ℕ} (X : Fin k → SSet.{u}) (a : (piObject X) _⦋0⦌) :
    π n (piObject X) a → ∀ i, π n (X i) (a i) :=
  fun p i ↦ mapπ (projection X i) n a (a i) rfl p

theorem coordinateClasses_bijective {k n : ℕ} (X : Fin k → SSet.{u})
    [∀ i, IsFibrant (X i)] [IsFibrant (piObject X)] (a : (piObject X) _⦋0⦌) :
    Function.Bijective (coordinateClasses (n := n) X a) := by
  constructor
  · intro p q h
    exact mapπ_projections_jointly_injective X a p q (fun i ↦ congrFun h i)
  · intro q
    have hp (i : Fin k) : ∃ p : (X i).PtSimplex n (a i), π.mk p = q i :=
      π.mk_surjective (q i)
    refine ⟨π.mk (productPtSimplex X a (fun i ↦ (hp i).choose)), ?_⟩
    funext i
    change π.mk ((productPtSimplex X a (fun i ↦ (hp i).choose)).pushforward
      (projection X i) (a i) rfl) = q i
    rw [← (hp i).choose_spec]
    congr 1

def finitePiπEquiv {k n : ℕ} (X : Fin k → SSet.{u})
    [∀ i, IsFibrant (X i)] [IsFibrant (piObject X)] (a : (piObject X) _⦋0⦌) :
    π n (piObject X) a ≃ ∀ i, π n (X i) (a i) :=
  Equiv.ofBijective (coordinateClasses X a) (coordinateClasses_bijective X a)

theorem finitePiπEquiv_natural {k n : ℕ} {X Y : Fin k → SSet.{u}}
    [∀ i, IsFibrant (X i)] [∀ i, IsFibrant (Y i)]
    [IsFibrant (piObject X)] [IsFibrant (piObject Y)]
    (f : ∀ i, X i ⟶ Y i) (a : (piObject X) _⦋0⦌) (b : (piObject Y) _⦋0⦌)
    (h : ∀ i, (f i).app (op ⦋0⦌) (a i) = b i) (p : π n (piObject X) a) (i : Fin k) :
    finitePiπEquiv Y b (mapπ (piMap f) n a b (funext h) p) i =
      mapπ (f i) n (a i) (b i) (h i) (finitePiπEquiv X a p i) := by
  change mapπ (projection Y i) n b (b i) rfl
    (mapπ (piMap f) n a b (funext h) p) =
      mapπ (f i) n (a i) (b i) (h i) (mapπ (projection X i) n a (a i) rfl p)
  obtain ⟨p, rfl⟩ := π.mk_surjective p
  rw [mapπ_mk, mapπ_mk, mapπ_mk, mapπ_mk]
  rfl

end
end DaggerNativeFinitePiHomotopyEquivalence
