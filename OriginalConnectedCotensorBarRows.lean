import OriginalConnectedCotensorBaseRows

/-! The connected-cotensor comparison retains every bar operator and the original projection. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed DaggerModels
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalConnectedCotensorRowIso DaggerOriginalConnectedCotensorBaseRows
open DaggerNativeOverChainFullDataEquivalence DaggerNativeIhomBinaryProduct
open DaggerOriginalOverNerveFibreChallengeProof
open DaggerOriginalNerveRowChainData DaggerOriginalBarRowFullData
universe u
namespace DaggerOriginalConnectedCotensorBarRows
noncomputable section

def barRowIhomMap (K : SSet.{u}) (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRow (originalCotensor K C) z k ⟶ (ihom K).obj (barRow C z k) where
  app n B :=
    { app m α a := B ⋙ Over.post (degreeEvaluation K C n m α a)
      naturality β γ := by
        funext a
        have hobj : ∀ i,
            (B ⋙ Over.post (degreeEvaluation K C n _ (γ ≫ β) (K.map β a))).obj i =
            ((B ⋙ Over.post (degreeEvaluation K C n _ γ a)) ⋙ overDegreeMap C z β).obj i := by
          intro i
          apply overObject_eq
            (a := (B ⋙ Over.post
              (degreeEvaluation K C n _ (γ ≫ β) (K.map β a))).obj i)
            (b := ((B ⋙ Over.post (degreeEvaluation K C n _ γ a)) ⋙
              overDegreeMap C z β).obj i) rfl
          exact heq_of_eq (congrFun ((B.obj i).hom.naturality β γ) a)
        refine Functor.hext hobj ?_
        intro i j f
        apply DaggerOriginalSimplicialCategoryOverDiagram.overHom_heq (hobj i) (hobj j)
        exact heq_of_eq (congrFun ((B.map f).left.naturality β γ) a) }
  naturality n m α := by
    funext B
    apply Functor.HomObj.ext
    funext d β a
    rfl

theorem barRowIhomMap_eq_iso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) : barRowIhomMap K C z k =
      (barRowIhomIso K v C z k).hom := by
  apply NatTrans.ext
  funext n B
  apply Functor.HomObj.ext
  funext m α a
  change B ⋙ Over.post (degreeEvaluation K C n m α a) =
    (overChainDataEquiv (degreeObjects C m) z k).symm _
  symm
  apply (overChainDataEquiv (degreeObjects C m) z k).symm_apply_eq.mpr
  let O := (B ⋙ Over.forget (T := degreeObjects (originalCotensor K C) n) z).obj
  let f := fun i : Fin k ↦ (B.map (homOfLE (Fin.castSucc_le_succ i))).left
  let g := (B.obj (Fin.last k)).hom
  change (⟨O, ((tensorIhomIso K (arrowFamily C O)
    (C.enriched.Hom (O (Fin.last k)) z)).hom.app n
      ((arrowFamilyIhomIso K C O).hom.app n f, g)).app m α a⟩ :
        (barRowFamily C z k).obj m) = _
  rw [tensorIhomIso_app]
  rfl

theorem barRowIhomMap_horizontal (K : SSet.{u}) (C : SimplicialCat.{u, u}) (z : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (barRows (originalCotensor K C) z).map α ≫ barRowIhomMap K C z m.unop.len =
      barRowIhomMap K C z n.unop.len ≫ (ihom K).map ((barRows C z).map α) := by
  apply NatTrans.ext
  funext d B
  apply Functor.HomObj.ext
  funext e β a
  rfl

def barRowsIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (z : C.Obj) :
    barRows (originalCotensor K C) z ≅ barRows C z ⋙ ihom K :=
  NatIso.ofComponents (fun n ↦ barRowIhomIso K v C z n.unop.len) (by
    intro n m α
    rw [← barRowIhomMap_eq_iso, ← barRowIhomMap_eq_iso]
    exact barRowIhomMap_horizontal K C z α)

theorem row_projection_ihom_square (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (z : C.Obj) (k : ℕ) :
    barRowIhomMap K C z k ≫ (ihom K).map (rowProjection C z k) =
      rowProjection (originalCotensor K C) z k ≫ baseRowIhomMap K C k := by
  apply NatTrans.ext
  funext n B
  apply Functor.HomObj.ext
  funext m α a
  rfl

end
end DaggerOriginalConnectedCotensorBarRows
