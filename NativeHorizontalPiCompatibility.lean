import NativeBisimplicialHorizontalMapping
import TopCatModelCategory.SSet.HomotopyGroup

/-! Canonical original pi classes in horizontal mapping objects give compatible row classes. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open SSet.KanComplex DaggerNativeBisimplicialHorizontalMapping
universe u
namespace DaggerNativeHorizontalPiCompatibility
noncomputable section

def evaluation (K : SSet.{u}) (X : BiSSet.{u}) (d : SimplexCategoryᵒᵖ) (x : K.obj d) :
    horizontalMapping K X ⟶ X.obj d where
  app _ a := a.app d x
  naturality _ _ _ := rfl

theorem evaluation_horizontal (K : SSet.{u}) (X : BiSSet.{u})
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) (x : K.obj d) :
    evaluation K X d x ≫ X.map α = evaluation K X e (K.map α x) := by
  apply NatTrans.ext
  funext v a
  exact (congrFun (a.naturality α) x).symm

theorem basepoint_horizontal (K : SSet.{u}) (X : BiSSet.{u})
    (a : (horizontalMapping K X) _⦋0⦌) {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e)
    (x : K.obj d) :
    (X.map α).app _ (a.app d x) = a.app e (K.map α x) :=
  (congrFun (a.naturality α) x).symm

def CompatiblePiFamily (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :=
  {s : ∀ (d : SimplexCategoryᵒᵖ) (x : K.obj d), π t (X.obj d) (a.app d x) //
    ∀ (d e : SimplexCategoryᵒᵖ) (α : d ⟶ e) (x : K.obj d),
      mapπ (X.map α) t (a.app d x) (a.app e (K.map α x))
        (basepoint_horizontal K X a α x) (s d x) = s e (K.map α x)}

def piComparison (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) :
    π t (horizontalMapping K X) a → CompatiblePiFamily K X t a :=
  fun s ↦ ⟨fun d x ↦ mapπ (evaluation K X d x) t a (a.app d x) rfl s, by
    intro d e α x
    have hh := mapπ_mapπ (evaluation K X d x) t a (a.app d x) rfl (X.map α)
      (a.app e (K.map α x)) (basepoint_horizontal K X a α x) s
    simpa only [evaluation_horizontal] using hh⟩

def topSimplex (m : ℕ) : (Δ[m] : SSet.{u}).obj (op ⦋m⦌) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 _)

theorem evaluation_top (X : BiSSet.{u}) (m : ℕ) :
    evaluation (Δ[m] : SSet.{u}) X (op ⦋m⦌) (topSimplex m) =
      (horizontalSimplexIso X m).hom := by
  apply NatTrans.ext
  rfl

theorem simplex_family_ext (X : BiSSet.{u}) (m t : ℕ)
    (a : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌)
    {s r : CompatiblePiFamily (Δ[m] : SSet.{u}) X t a}
    (h : s.val (op ⦋m⦌) (topSimplex m) = r.val (op ⦋m⦌) (topSimplex m)) : s = r := by
  apply Subtype.ext
  funext d x
  let α : op ⦋m⦌ ⟶ d := (SSet.stdSimplex.objEquiv x).op
  have hx : (Δ[m] : SSet.{u}).map α (topSimplex m) = x := by
    simp only [SSet.stdSimplex.map_apply, topSimplex, α, Quiver.Hom.unop_op,
      Equiv.apply_symm_apply, Category.comp_id, Equiv.symm_apply_apply]
  have hs := s.property (op ⦋m⦌) d α (topSimplex m)
  have hr := r.property (op ⦋m⦌) d α (topSimplex m)
  rw [h] at hs
  exact Eq.mp (congrArg (fun y ↦ s.val d y = r.val d y) hx) (hs.symm.trans hr)

theorem simplex_piComparison_injective (X : BiSSet.{u}) (m t : ℕ)
    (a : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌) :
    Function.Injective (piComparison (Δ[m] : SSet.{u}) X t a) := by
  intro s r h
  have hh := congrArg (fun z ↦ z.val (op ⦋m⦌) (topSimplex m)) h
  change mapπ (evaluation _ X _ (topSimplex m)) t a _ rfl s =
    mapπ (evaluation _ X _ (topSimplex m)) t a _ rfl r at hh
  rw [evaluation_top] at hh
  exact (mapπEquivOfIso (horizontalSimplexIso X m) t a
    (a.app (op ⦋m⦌) (topSimplex m)) rfl).injective hh

theorem simplex_piComparison_surjective (X : BiSSet.{u}) (m t : ℕ)
    (a : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌) :
    Function.Surjective (piComparison (Δ[m] : SSet.{u}) X t a) := by
  intro r
  let e := mapπEquivOfIso (horizontalSimplexIso X m) t a
    (a.app (op ⦋m⦌) (topSimplex m)) rfl
  refine ⟨e.symm (r.val (op ⦋m⦌) (topSimplex m)), simplex_family_ext X m t a ?_⟩
  change e (e.symm (r.val (op ⦋m⦌) (topSimplex m))) = r.val (op ⦋m⦌) (topSimplex m)
  exact e.apply_symm_apply _

theorem simplex_piComparison_bijective (X : BiSSet.{u}) (m t : ℕ)
    (a : (horizontalMapping (Δ[m] : SSet.{u}) X) _⦋0⦌) :
    Function.Bijective (piComparison (Δ[m] : SSet.{u}) X t a) :=
  ⟨simplex_piComparison_injective X m t a, simplex_piComparison_surjective X m t a⟩

end
end DaggerNativeHorizontalPiCompatibility
