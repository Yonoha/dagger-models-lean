import OriginalSimplicialCategoryWholeBarFibreDegree

/-!
# The entire original strict whole-bar fibre is the original Hom coproduct

Assemble the native component-fibre isomorphisms through the actual coproduct
universal property. The forward map under inclusion is exactly the original
Hom inclusions followed by the original whole bar inclusions. No homotopy
pullback or homotopy-fibre comparison is asserted.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreIso
noncomputable section

/-- The entire original component-fibre coproduct is the actual whole strict fibre. -/
def componentFibreSumIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    componentFibreSum C x ≅ (wholeBarFibre C x).toSSet :=
  NatIso.ofComponents (fun n ↦ (componentFibreSumDegreeEquiv C x n).toIso) (by
    intro n m i
    funext a
    obtain ⟨⟨y, a⟩, rfl⟩ :=
      (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n).surjective a
    change componentFibreSumDegreeEquiv C x m
        ((componentFibreSum C x).map i
          (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩)) =
      ((wholeBarFibre C x).toSSet).map i
        (componentFibreSumDegreeEquiv C x n
          (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩))
    have hd := coproductDegreeEquiv_map (fun y ↦ (barFibre C x y).toSSet) i y a
    change (componentFibreSum C x).map i
        (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩) = _ at hd
    rw [hd, componentFibreSumDegreeEquiv_apply, componentFibreSumDegreeEquiv_apply]
    exact congrFun ((componentFibreInclusion C x y).naturality i) a)

/-- The original whole fibre isomorphism's forward map is exactly the native descent. -/
theorem componentFibreSumIso_hom (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (componentFibreSumIso C x).hom = componentFibreSumMap C x := by
  apply NatTrans.ext
  funext n a
  obtain ⟨⟨y, a⟩, rfl⟩ :=
    (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n).surjective a
  change componentFibreSumDegreeEquiv C x n
      (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩) = _
  rw [componentFibreSumDegreeEquiv_apply]
  exact (coproductDegreeEquiv_desc (componentFibreInclusion C x) n y a).symm

/-- Under inclusion the whole fibre isomorphism is exactly the original component inclusions. -/
theorem componentFibreSumIso_hom_ι (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (componentFibreSumIso C x).hom ≫ (wholeBarFibre C x).ι =
      Sigma.desc (fun y ↦ (barFibre C x y).ι ≫ barInclusion C y) := by
  rw [componentFibreSumIso_hom]
  apply Sigma.hom_ext
  intro y
  change Sigma.ι (fun y ↦ (barFibre C x y).toSSet) y ≫
      (Sigma.desc (componentFibreInclusion C x) ≫ (wholeBarFibre C x).ι) = _
  rw [← Category.assoc, Sigma.ι_desc, componentFibreInclusion_ι, Sigma.ι_desc]

/-- The native coproduct of all original enriched Hom objects with the same original source. -/
def originalHomSum (C : SimplicialCat.{u, u}) (x : C.Obj) : SSet.{u} :=
  ∐ (fun y ↦ C.enriched.Hom x y)

/-- The original Hom coproduct includes by its original component and whole bar inclusions. -/
def wholeBarHomInclusion (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ⟶ bar C :=
  Sigma.desc (fun y ↦ barHomInclusion C x y ≫ barInclusion C y)

/-- The actual whole original fibre is the native coproduct of the original enriched Homs. -/
def wholeBarHomFibreIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ≅ (wholeBarFibre C x).toSSet :=
  Sigma.mapIso (barFibreIso C x) ≪≫ componentFibreSumIso C x

/-- The full Hom-fibre isomorphism retains the actual original whole Hom inclusion. -/
theorem wholeBarHomFibreIso_hom_ι (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (wholeBarHomFibreIso C x).hom ≫ (wholeBarFibre C x).ι =
      wholeBarHomInclusion C x := by
  change (Limits.Sigma.map (fun y ↦ (barFibreIso C x y).hom) ≫
      (componentFibreSumIso C x).hom) ≫ (wholeBarFibre C x).ι = _
  rw [Category.assoc, componentFibreSumIso_hom_ι]
  apply Sigma.hom_ext
  intro y
  rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_desc,
    ← Category.assoc, barFibreIso_hom_ι]
  exact (Sigma.ι_desc (fun y ↦ barHomInclusion C x y ≫ barInclusion C y) y).symm

end
end DaggerOriginalSimplicialCategoryWholeBarFibreIso
