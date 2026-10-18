import NativeCoproductKan
import NativeFinitePiHomotopyEquivalence

/-! Positive native based homotopy classes stay in their original coproduct summand. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerNativeCoproductConnectedFactor DaggerNativeStandardSimplexContraction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductHomotopy
noncomputable section

theorem lift_positive_pointed_simplex {I : Type u} (X : I → SSet.{u}) (i : I)
    (x : (X i) _⦋0⦌) {n : ℕ}
    (s : (∐ X).PtSimplex (n + 1) ((Sigma.ι X i).app (op ⦋0⦌) x)) :
    ∃ p : (X i).PtSimplex (n + 1) x,
      p.pushforward (Sigma.ι X i) _ rfl = s := by
  let v := (SSet.stdSimplex.δ (0 : Fin (n + 2))).app (op ⦋0⦌) (firstVertex n)
  have hv : s.map.app (op ⦋0⦌) v = (Sigma.ι X i).app (op ⦋0⦌) x := by
    have h := congrFun (NatTrans.congr_app (s.δ_map 0) (op ⦋0⦌)) (firstVertex n)
    simpa only [NatTrans.comp_app, FunctorToTypes.comp, SSet.const_app,
      SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] using h
  obtain ⟨g, hg⟩ := connected_factor_fixed_summand X i s.map v x hv
  let p : (X i).PtSimplex (n + 1) x := SSet.PtSimplex.mk g (fun j ↦ by
    apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg, s.δ_map j, SSet.const_comp])
  refine ⟨p, SSet.Subcomplex.RelativeMorphism.ext hg⟩

def lift_summand_relation {I : Type u} (X : I → SSet.{u}) (i : I)
    (x : (X i) _⦋0⦌) {n : ℕ} (p q : (X i).PtSimplex n x)
    (h : (p.pushforward (Sigma.ι X i) _ rfl).RelStruct₀
      (q.pushforward (Sigma.ι X i) _ rfl)) : p.RelStruct₀ q := by
  let v := (SSet.stdSimplex.δ (0 : Fin (n + 2))).app (op ⦋0⦌) (firstVertex n)
  have hv : h.map.app (op ⦋0⦌) v =
      (Sigma.ι X i).app (op ⦋0⦌) (p.map.app (op ⦋0⦌) (firstVertex n)) :=
    congrFun (NatTrans.congr_app h.δ_castSucc_map (op ⦋0⦌)) (firstVertex n)
  have he := connected_factor_fixed_summand X i h.map v _ hv
  let g := he.choose
  have hg : g ≫ Sigma.ι X i = h.map := he.choose_spec
  refine
    { map := g
      δ_castSucc_map := ?_
      δ_succ_map := ?_
      δ_map_of_lt := ?_
      δ_map_of_gt := ?_ }
  · apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg]
    exact h.δ_castSucc_map
  · apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg]
    exact h.δ_succ_map
  · intro j hj
    apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg, h.δ_map_of_lt j hj, SSet.const_comp]
  · intro j hj
    apply (cancel_mono (Sigma.ι X i)).mp
    rw [Category.assoc, hg, h.δ_map_of_gt j hj, SSet.const_comp]

theorem summand_mapπ_injective {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) (x : (X i) _⦋0⦌) (n : ℕ) :
    Function.Injective (mapπ (Sigma.ι X i) n x _ rfl) := by
  intro p q h
  obtain ⟨p, rfl⟩ := π.mk_surjective p
  obtain ⟨q, rfl⟩ := π.mk_surjective q
  obtain ⟨h⟩ := π.mk_eq_mk_iff.mp h
  exact π.mk_eq_mk_iff.mpr ⟨lift_summand_relation X i x p q h⟩

theorem summand_mapπ_positive_bijective {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) (x : (X i) _⦋0⦌) (n : ℕ) :
    Function.Bijective (mapπ (Sigma.ι X i) (n + 1) x _ rfl) := by
  refine ⟨summand_mapπ_injective X i x (n + 1), ?_⟩
  intro s
  obtain ⟨s, rfl⟩ := π.mk_surjective s
  obtain ⟨p, hp⟩ := lift_positive_pointed_simplex X i x s
  refine ⟨π.mk p, ?_⟩
  rw [mapπ_mk, hp]

def summandPiEquiv {I : Type u} (X : I → SSet.{u}) [∀ i, IsFibrant (X i)]
    (i : I) (x : (X i) _⦋0⦌) (n : ℕ) :
    π (n + 1) (X i) x ≃ π (n + 1) (∐ X) ((Sigma.ι X i).app (op ⦋0⦌) x) :=
  Equiv.ofBijective _ (summand_mapπ_positive_bijective X i x n)

end
end DaggerNativeCoproductHomotopy
