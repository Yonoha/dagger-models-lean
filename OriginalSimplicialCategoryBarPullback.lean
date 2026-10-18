import OriginalSimplicialCategoryBarFibre

/-!
# The actual original Hom pullback of the original DK80 bar projection

The source-vertex subcomplex is exactly the range of the native Yoneda vertex
map from the standard zero-simplex. It is isomorphic to that zero-simplex.
Transport the native subcomplex-preimage pullback along this isomorphism and
the full original Hom-fibre isomorphism. The resulting pullback square has the
unchanged original Hom, original bar inclusion, projection and source vertex.
No homotopy pullback or quasifibration conclusion is assumed.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryBarFibre
universe u
namespace DaggerOriginalSimplicialCategoryBarPullback
noncomputable section

/-- The original constant-vertex subcomplex is the range of the actual native vertex map. -/
theorem sourceVertexSubcomplex_eq_range (C : SimplicialCat.{u, u}) (x : C.Obj) :
    sourceVertexSubcomplex C x = SSet.Subcomplex.range (sourceVertexMap C x) := by
  apply Subfunctor.ext
  funext n
  ext a
  change (a = constantSourceSimplex C x n) ↔
    ∃ b, (sourceVertexMap C x).app n b = a
  constructor
  · intro ha
    exact ⟨SSet.stdSimplex.objEquiv.symm (n.unop.const ⦋0⦌ 0), ha.symm⟩
  · rintro ⟨b, rfl⟩
    rfl

/-- The strict fibre is exactly the inverse image of the original vertex-map range. -/
theorem barFibre_eq_vertexPreimage (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    barFibre C x y =
      (SSet.Subcomplex.range (sourceVertexMap C x)).preimage (barComponentProjection C y) :=
  congrArg (fun B ↦ B.preimage (barComponentProjection C y))
    (sourceVertexSubcomplex_eq_range C x)

/-- In each degree the source-vertex subcomplex is exactly the standard point. -/
def sourceVertexEquiv (C : SimplicialCat.{u, u}) (x : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (SSet.stdSimplex.obj ⦋0⦌).obj n ≃ ((sourceVertexSubcomplex C x).toSSet).obj n where
  toFun _ := ⟨constantSourceSimplex C x n, rfl⟩
  invFun _ := SSet.stdSimplex.objEquiv.symm (n.unop.const ⦋0⦌ 0)
  left_inv _ := Subsingleton.elim _ _
  right_inv a := Subtype.ext a.property.symm

/-- The entire original source-vertex subcomplex is isomorphic to the standard point. -/
def sourceVertexIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.stdSimplex.obj ⦋0⦌ ≅ (sourceVertexSubcomplex C x).toSSet :=
  NatIso.ofComponents (fun n ↦ (sourceVertexEquiv C x n).toIso) (by
    intro n m i
    funext a
    apply Subtype.ext
    exact (constantSourceSimplex_map C x i).symm)

/-- Including the source-vertex isomorphism is exactly the original native vertex map. -/
theorem sourceVertexIso_hom_ι (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (sourceVertexIso C x).hom ≫ (sourceVertexSubcomplex C x).ι = sourceVertexMap C x := by
  apply NatTrans.ext
  funext n
  rfl

/-- The native strict-fibre pullback retains the original Hom, projection and source vertex. -/
theorem barHomIsPullback (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    IsPullback (barHomInclusion C x y)
      (SSet.stdSimplex.isTerminalObj₀.from (C.enriched.Hom x y))
      (barComponentProjection C y) (sourceVertexMap C x) := by
  have h := (sourceVertexSubcomplex C x).preimage_isPullback (barComponentProjection C y)
  refine h.of_iso (barFibreIso C x y).symm (Iso.refl (barComponent C y))
    (sourceVertexIso C x).symm (Iso.refl (diagonalNerveFunctor.obj C)) ?_ ?_ ?_ ?_
  · rw [← barFibreIso_hom_ι C x y]
    simp [barFibre]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · simp
  · rw [← sourceVertexIso_hom_ι C x]
    simp

end
end DaggerOriginalSimplicialCategoryBarPullback
