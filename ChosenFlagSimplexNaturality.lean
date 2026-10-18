import ChosenFlagSimplexIso

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- Both original thickening endpoint transports retain every set in the chain. -/
theorem thickeningHom_eqToHom_I {n : ℕ}
    {a b c d : (T.{u}.obj ⦋n⦌).Obj} (ha : a = c) (hb : b = d)
    (h : (a ⟶[SSet.{u}] b) = (c ⟶[SSet.{u}] d))
    (q : SimplexCategoryᵒᵖ) (F : (a ⟶[SSet.{u}] b).obj q)
    (i : Fin (q.unop.len + 1)) :
    ((((eqToHom h).app q F).obj i).I) = (F.obj i).I := by
  cases ha
  cases hb
  rfl

theorem simplexVertexMap_postcomp {P : NecklaceCode} {n m : ℕ}
    (f : toSSet.{u} P ⟶ Δ[n]) (α : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexVertexMap (f ≫ SSet.stdSimplex.map α) =
      α.toOrderHom.uliftMap ∘ simplexVertexMap f := rfl

/-- Full original simplex naturality, including collapsing operators and both Hom casts. -/
theorem flagSimplexIso_naturality {n m : ℕ} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    EMap (SSet.stdSimplex.{u}.map α) ≫ (flagSimplexIso m).hom =
      (flagSimplexIso n).hom ≫ T.map α := by
  have ho : ∀ x : (E (Δ[n] : SSet.{u})).Obj,
      (EMap (SSet.stdSimplex.map α) ≫ (flagSimplexIso m).hom).obj x =
        ((flagSimplexIso n).hom ≫ T.map α).obj x := by
    intro x
    change (flagSimplexIso m).hom.obj ((SSet.stdSimplex.map α).app _ x) =
      (T.map α).obj ((flagSimplexIso n).hom.obj x)
    rw [flagSimplexIso_hom_obj, flagSimplexIso_hom_obj]
    rfl
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply NatTrans.ext
  funext q F
  induction F using Quot.ind with | _ p
  refine CategoryTheory.Functor.ext
    (fun i ↦ SimplicialThickening.Path.ext ?_)
  change ((((eqToHom (show
      ((EMap (SSet.stdSimplex.map α) ≫ (flagSimplexIso m).hom).obj x ⟶[SSet.{u}]
        (EMap (SSet.stdSimplex.map α) ≫ (flagSimplexIso m).hom).obj y) =
      (((flagSimplexIso n).hom ≫ T.map α).obj x ⟶[SSet.{u}]
        ((flagSimplexIso n).hom ≫ T.map α).obj y) by rw [ho x, ho y])).app q
      (((flagSimplexIso m).hom.map _ _).app q
        (((EMap (SSet.stdSimplex.map α)).map x y).app q (Quot.mk _ p)))).obj i).I) =
    ((((T.map α).map _ _).app q
      (((flagSimplexIso n).hom.map x y).app q (Quot.mk _ p))).obj i).I
  rw [thickeningHom_eqToHom_I (ho x) (ho y)]
  change ((((flagSimplexIso m).hom.map _ _).app q
      (Quot.mk _ ⟨(NecklacesOver.postcomp (SSet.stdSimplex.map α)).obj p.1, p.2⟩)).obj i).I = _
  rw [flagSimplexIso_hom_raw_I]
  change simplexVertexMap (p.1.map ≫ SSet.stdSimplex.map α) '' p.2.chain i =
    α.toOrderHom.uliftMap ''
      ((((flagSimplexIso n).hom.map x y).app q (Quot.mk _ p)).obj i).I
  rw [flagSimplexIso_hom_raw_I, simplexVertexMap_postcomp, Set.image_image]
  rfl

/-- Inverse legs are the same inverse functors, not a separately chosen simplex map. -/
theorem flagSimplexIso_inv_naturality {n m : ℕ} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    T.{u}.map α ≫ (flagSimplexIso m).inv =
      (flagSimplexIso n).inv ≫ EMap (SSet.stdSimplex.map α) := by
  apply (cancel_epi (flagSimplexIso n).hom).mp
  rw [← Category.assoc, ← flagSimplexIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end DaggerChosenRigidificationNecklace
