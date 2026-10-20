import OriginalConnectedCotensorRowIso

/-! The original connected-cotensor base comparison respects every horizontal operator. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed DaggerModels
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalFixedObjectStrictGroupoidCotensors DaggerNativeNerveChainData
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalConnectedCotensorRowIso
universe u
namespace DaggerOriginalConnectedCotensorBaseRows
noncomputable section

def degreeEvaluation (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (n m : SimplexCategoryᵒᵖ) (α : n ⟶ m) (a : K.obj m) :
    degreeObjects (originalCotensor K C) n ⥤ degreeObjects C m where
  obj x := x
  map f := f.app m α a
  map_id x := cotensor_point_id K ⟨C.enriched⟩ x n m α a
  map_comp {x y z} f g := cotensor_point_comp K ⟨C.enriched⟩ x y z n m α f g a

def baseRowIhomMap (K : SSet.{u}) (C : SimplicialCat.{u, u}) (k : ℕ) :
    baseRow (originalCotensor K C) k ⟶ (ihom K).obj (baseRow C k) where
  app n A :=
    { app m α a := A ⋙ degreeEvaluation K C n m α a
      naturality β γ := by
        funext a
        change A ⋙ degreeEvaluation K C n _ (γ ≫ β) (K.map β a) =
          (A ⋙ degreeEvaluation K C n _ γ a) ⋙ degreeMap C β
        refine Functor.hext
          (F := A ⋙ degreeEvaluation K C n _ (γ ≫ β) (K.map β a))
          (G := (A ⋙ degreeEvaluation K C n _ γ a) ⋙ degreeMap C β) (fun _ ↦ rfl) ?_
        intro x y f
        exact heq_of_eq (congrFun ((A.map f).naturality β γ) a) }
  naturality n m α := by
    funext A
    apply Functor.HomObj.ext
    funext d β a
    refine Functor.hext
      (F := (A ⋙ degreeMap (originalCotensor K C) α) ⋙ degreeEvaluation K C m d β a)
      (G := A ⋙ degreeEvaluation K C n d (α ≫ β) a) (fun _ ↦ rfl) ?_
    intro x y f
    rfl

theorem baseRowIhomMap_eq_iso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (k : ℕ) : baseRowIhomMap K C k =
      (baseRowIhomIso K v C k).hom := by
  apply NatTrans.ext
  funext n A
  apply Functor.HomObj.ext
  funext m α a
  change A ⋙ degreeEvaluation K C n m α a =
    (chainDataEquiv (degreeObjects C m) k).symm _
  symm
  apply (chainDataEquiv (degreeObjects C m) k).symm_apply_eq.mpr
  rfl

theorem baseRowIhomMap_horizontal (K : SSet.{u}) (C : SimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (baseRows (originalCotensor K C)).map α ≫ baseRowIhomMap K C m.unop.len =
      baseRowIhomMap K C n.unop.len ≫ (ihom K).map ((baseRows C).map α) := by
  apply NatTrans.ext
  funext d A
  apply Functor.HomObj.ext
  funext e β a
  rfl

def baseRowsIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) :
    baseRows (originalCotensor K C) ≅ baseRows C ⋙ ihom K :=
  NatIso.ofComponents (fun n ↦ baseRowIhomIso K v C n.unop.len) (by
    intro n m α
    rw [← baseRowIhomMap_eq_iso, ← baseRowIhomMap_eq_iso]
    exact baseRowIhomMap_horizontal K C α)

end
end DaggerOriginalConnectedCotensorBaseRows
