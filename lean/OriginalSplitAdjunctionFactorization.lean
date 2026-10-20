import ChallengeSplitAdjunctionFactorization

/-! Prove the exact independent split-adjunction canonical-factorization statement. -/
set_option autoImplicit false
open CategoryTheory
universe u v a b
namespace DaggerOriginalSplitAdjunctionFactorization
noncomputable section

/-- Native adjunction lifting and full endpoint isomorphisms give the exact target classes. -/
theorem exact_statement : DaggerChallengeSplitAdjunctionFactorization.Statement.{u, v, a, b} := by
  intro C categoryC D categoryD L R S adj e P Q respects sourceFactorization hQ hR
  have hleft : ∀ {X Y : D} (i : X ⟶ Y), Q.llp i → P.llp (L.map i) := by
    intro X Y i hi A B p hp
    exact (adj.hasLiftingProperty_iff i p).2 (hi _ (hR p hp))
  refine ⟨fun {X Y} f ↦ ?_⟩
  let d : Q.llp.MapFactorizationData Q (S.map f) :=
    Classical.choice (MorphismProperty.HasFactorization.nonempty_mapFactorizationData (S.map f))
  refine ⟨⟨L.obj d.Z, (e.app X).inv ≫ L.map d.i, L.map d.p ≫ (e.app Y).hom, ?_, ?_, ?_⟩⟩
  · calc
      ((e.app X).inv ≫ L.map d.i) ≫ (L.map d.p ≫ (e.app Y).hom) =
          (e.app X).inv ≫ L.map (d.i ≫ d.p) ≫ (e.app Y).hom := by
            simp only [Functor.map_comp, Category.assoc]
      _ = (e.app X).inv ≫ (S ⋙ L).map f ≫ (e.app Y).hom := by rw [d.fac]; rfl
      _ = f := NatIso.naturality_1 e f
  · exact MorphismProperty.RespectsIso.precomp P.llp (e.app X).inv _ (hleft d.i d.hi)
  · apply MorphismProperty.RespectsIso.postcomp P (e.app Y).hom
    exact (congrArg (fun T : MorphismProperty D ↦ T d.p) hQ).mp d.hp

end
end DaggerOriginalSplitAdjunctionFactorization
