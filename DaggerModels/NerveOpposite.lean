import DaggerModels.ThickeningReversal

/-!
# The actual coherent nerve and ordinary enriched opposite

The comparison retains restricted ULift Yoneda and the existing simplicial opposite.
Its simplex maps use the concrete standard-thickening reversal. Naturality holds for
all simplex operators and all enriched target functors; its involution uses the actual
double-opposite comparisons. This does not construct a dagger lift or a rigidification mate.
-/

open CategoryTheory Opposite

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.NerveOpposite

open ThickeningReversal

private theorem doubleOpposite_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    SimplicialCat.oppositeFunctor.map (SimplicialCat.oppositeFunctor.map F) ≫
        SimplicialCat.doubleOppositeHom D = SimplicialCat.doubleOppositeHom C ≫ F :=
  SimplicialCat.doubleOppositeNatIso.hom.naturality F

private theorem opposite_doubleOppositeHom (C : SimplicialCat.{u, u}) :
    SimplicialCat.oppositeFunctor.map (SimplicialCat.doubleOppositeHom C) =
      SimplicialCat.doubleOppositeHom (SimplicialCat.opposite C) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

/-- The prescribed forward map on full enriched simplices. -/
def forward (C : SimplicialCat.{u, u}) (n : SimplexCategory)
    (F : standard n ⟶ SimplicialCat.opposite C) : standard n ⟶ C :=
  reversal n ≫ SimplicialCat.oppositeFunctor.map F ≫ SimplicialCat.doubleOppositeHom C

/-- The prescribed inverse map on full enriched simplices. -/
def backward (C : SimplicialCat.{u, u}) (n : SimplexCategory)
    (G : standard n ⟶ C) : standard n ⟶ SimplicialCat.opposite C :=
  reversal n ≫ SimplicialCat.oppositeFunctor.map G

/-- Applying backward and then forward preserves the complete enriched functor. -/
theorem forward_backward (C : SimplicialCat.{u, u}) (n : SimplexCategory)
    (G : standard n ⟶ C) : forward C n (backward C n G) = G := by
  unfold forward backward
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [doubleOpposite_naturality]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k ↦ k ≫ G) (reversal_involutive n)

/-- Applying forward and then backward preserves the complete enriched functor. -/
theorem backward_forward (C : SimplicialCat.{u, u}) (n : SimplexCategory)
    (F : standard n ⟶ SimplicialCat.opposite C) : backward C n (forward C n F) = F := by
  unfold forward backward
  simp only [CategoryTheory.Functor.map_comp, opposite_doubleOppositeHom]
  rw [doubleOpposite_naturality F]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k ↦ k ≫ F) (reversal_involutive n)

/-- Forward conversion commutes with every simplex operator and its reversal. -/
theorem forward_precomp (C : SimplicialCat.{u, u}) {n m : SimplexCategory}
    (f : n ⟶ m) (F : standard m ⟶ SimplicialCat.opposite C) :
    forward C n (cosimplicialThickening.map f ≫ F) =
      cosimplicialThickening.map (SimplexCategory.rev.map f) ≫ forward C m F := by
  unfold forward
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ SimplicialCat.oppositeFunctor.map F ≫
      SimplicialCat.doubleOppositeHom C) (reversal_naturality f).symm

/-- Backward conversion commutes with every reversed simplex operator. -/
theorem backward_precomp (C : SimplicialCat.{u, u}) {n m : SimplexCategory}
    (f : n ⟶ m) (G : standard m ⟶ C) :
    backward C n (cosimplicialThickening.map (SimplexCategory.rev.map f) ≫ G) =
      cosimplicialThickening.map f ≫ backward C m G := by
  unfold backward
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    SimplexCategory.rev_map_rev_map, SimplexCategory.rev_obj] using
    congrArg (fun k ↦ k ≫ SimplicialCat.oppositeFunctor.map G)
      (reversal_naturality (SimplexCategory.rev.map f)).symm

/-- Forward conversion is natural for arbitrary enriched target functors. -/
theorem forward_postcomp {C D : SimplicialCat.{u, u}} (H : C ⟶ D)
    (n : SimplexCategory) (F : standard n ⟶ SimplicialCat.opposite C) :
    forward D n (F ≫ SimplicialCat.oppositeFunctor.map H) = forward C n F ≫ H := by
  unfold forward
  rw [CategoryTheory.Functor.map_comp, Category.assoc, doubleOpposite_naturality]
  simp only [Category.assoc]

/-- Backward conversion is natural for arbitrary enriched target functors. -/
theorem backward_postcomp {C D : SimplicialCat.{u, u}} (H : C ⟶ D)
    (n : SimplexCategory) (G : standard n ⟶ C) :
    backward D n (G ≫ H) = backward C n G ≫ SimplicialCat.oppositeFunctor.map H := by
  unfold backward
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The full degreewise equivalence retains outer ULift and actual opObjEquiv. -/
def simplexEquiv (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (coherentNerve.obj (SimplicialCat.opposite C)).obj n ≃
      (SSet.opFunctor.obj (coherentNerve.obj C)).obj n where
  toFun P := SSet.opObjEquiv.symm (ULift.up (forward C n.unop P.down))
  invFun P := ULift.up (backward C n.unop (SSet.opObjEquiv P).down)
  left_inv P := by
    apply ULift.ext
    exact backward_forward C n.unop P.down
  right_inv P := by
    apply ULift.ext
    exact forward_backward C n.unop (SSet.opObjEquiv P).down

/-- The comparison is an actual isomorphism of simplicial sets. -/
def coherentNerveOppositeObjIso (C : SimplicialCat.{u, u}) :
    coherentNerve.obj (SimplicialCat.opposite C) ≅ SSet.opFunctor.obj (coherentNerve.obj C) :=
  NatIso.ofComponents (fun n ↦ (simplexEquiv C n).toIso) (by
    intro n m f
    funext P
    apply ULift.ext
    exact forward_precomp C f.unop P.down)

/-- The prescribed comparison is natural in arbitrary enriched target functors. -/
def coherentNerveOppositeIso :
    SimplicialCat.oppositeFunctor ⋙ coherentNerve.{u} ≅ coherentNerve ⋙ SSet.opFunctor :=
  NatIso.ofComponents coherentNerveOppositeObjIso (by
    intro C D H
    ext n P
    apply ULift.ext
    exact forward_postcomp H n.unop P.down)

/-- Two forward conversions agree with the actual double-opposite hom. -/
theorem forward_forward (C : SimplicialCat.{u, u}) (n : SimplexCategory)
    (F : standard n ⟶ SimplicialCat.opposite (SimplicialCat.opposite C)) :
    forward C n (forward (SimplicialCat.opposite C) n F) =
      F ≫ SimplicialCat.doubleOppositeHom C := by
  unfold forward
  simp only [CategoryTheory.Functor.map_comp, opposite_doubleOppositeHom]
  rw [doubleOpposite_naturality F]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k ↦ k ≫ F ≫ SimplicialCat.doubleOppositeHom C) (reversal_involutive n)

/-- The natural comparison satisfies the actual opposite-involution coherence. -/
theorem coherentNerveOpposite_coherence (C : SimplicialCat.{u, u}) :
    coherentNerveOppositeIso.hom.app (SimplicialCat.opposite C) ≫
        SSet.opFunctor.map (coherentNerveOppositeIso.hom.app C) ≫
        SSet.opFunctorCompOpFunctorIso.hom.app (coherentNerve.obj C) =
      coherentNerve.map (SimplicialCat.doubleOppositeIso C).hom := by
  ext n P
  apply ULift.ext
  exact forward_forward C n.unop P.down

end DaggerModels.OrdinaryRigidification.NerveOpposite
