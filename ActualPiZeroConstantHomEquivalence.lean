import ActualConstantEnrichmentFunctor
import OriginalSimplicialPiZeroFunctor

/-! The exact original component category is universal for maps to constant enrichments. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerUnitaryDiscrete DaggerActualConstantSimplicialCategory
open DaggerOriginalSimplicialPiZeroCategory
universe u
namespace DaggerActualPiZeroConstantHomEquivalence
noncomputable section

theorem constant_ext {X : SSet.{u}} {B : Type u} {f g : X ⟶ constSSet B}
    (h : ∀ v : X.obj (op ⦋0⦌), f.app (op ⦋0⦌) v = g.app (op ⦋0⦌) v) : f = g := by
  apply (constantHomEquiv X B).injective
  funext a
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  simpa only [constantHomEquiv_mk] using h v

theorem constant_symm_mk {X : SSet.{u}} {B : Type u} (h : X.π₀ → B)
    (v : X.obj (op ⦋0⦌)) :
    ((constantHomEquiv X B).symm h).app (op ⦋0⦌) v = h (SSet.π₀.mk v) := by
  simpa only [constantHomEquiv_mk] using
    congrFun ((constantHomEquiv X B).apply_symm_apply h) (SSet.π₀.mk v)

def toOrdinary (C : SimplicialCat.{u, u}) (A : Type u) [Category.{u} A]
    (F : C ⟶ constant A) : componentObjects C ⥤ A := by
  letI := C.enriched
  letI := (constant A).enriched
  exact
    { obj := F.obj
      map {x y} := constantHomEquiv (C.enriched.Hom x y) (F.obj x ⟶ F.obj y) (F.map x y)
      map_id x := by
        change (constantHomEquiv _ _) (F.map x x)
          (SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit)) = _
        rw [constantHomEquiv_mk]
        exact congrFun (NatTrans.congr_app (F.map_id x) (op ⦋0⦌)) PUnit.unit
      map_comp {x y z} a b := by
        obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
        obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
        change (constantHomEquiv _ _) (F.map x z)
          (SSet.π₀.mk ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b))) = _
        simp only [constantHomEquiv_mk]
        exact congrFun (NatTrans.congr_app (F.map_comp x y z) (op ⦋0⦌)) (a, b)
    }

def fromOrdinary (C : SimplicialCat.{u, u}) (A : Type u) [Category.{u} A]
    (G : componentObjects C ⥤ A) : C ⟶ constant A := by
  letI := C.enriched
  letI := (constant A).enriched
  exact
    { obj := G.obj
      map x y := (constantHomEquiv (C.enriched.Hom x y) (G.obj x ⟶ G.obj y)).symm
        (fun a ↦ G.map a)
      map_id x := by
        apply constant_ext
        intro p
        change ((constantHomEquiv (C.enriched.Hom x x) _).symm
          (fun a ↦ G.map a)).app (op ⦋0⦌) _ = _
        rw [constant_symm_mk]
        exact G.map_id x
      map_comp x y z := by
        apply constant_ext
        intro p
        change ((constantHomEquiv (C.enriched.Hom x z) _).symm
          (fun a ↦ G.map a)).app (op ⦋0⦌) ((C.enriched.comp x y z).app (op ⦋0⦌) p) =
          (((constantHomEquiv (C.enriched.Hom x y) _).symm
            (fun a ↦ G.map a)).app (op ⦋0⦌) p.1) ≫
          (((constantHomEquiv (C.enriched.Hom y z) _).symm
            (fun a ↦ G.map a)).app (op ⦋0⦌) p.2)
        rw [constant_symm_mk, constant_symm_mk, constant_symm_mk]
        exact G.map_comp (SSet.π₀.mk p.1) (SSet.π₀.mk p.2)
    }

theorem to_from (C : SimplicialCat.{u, u}) (A : Type u) [Category.{u} A]
    (G : componentObjects C ⥤ A) : toOrdinary C A (fromOrdinary C A G) = G := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro x y a
  exact heq_of_eq (congrFun
    ((constantHomEquiv (C.enriched.Hom x y) _).apply_symm_apply (fun a ↦ G.map a)) a)

theorem from_to (C : SimplicialCat.{u, u}) (A : Type u) [Category.{u} A]
    (F : C ⟶ constant A) : fromOrdinary C A (toOrdinary C A F) = F := by
  letI := C.enriched
  letI := (constant A).enriched
  apply EnrichedFunctor.ext SSet
    (F := fromOrdinary C A (toOrdinary C A F)) (G := F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact (constantHomEquiv (C.enriched.Hom x y) _).symm_apply_apply (F.map x y)

/-- This equivalence uses all original objects, all component Homs and their compositions. -/
def homEquiv (C : SimplicialCat.{u, u}) (A : Type u) [Category.{u} A] :
    (componentObjects C ⥤ A) ≃ (C ⟶ constant A) where
  toFun := fromOrdinary C A
  invFun := toOrdinary C A
  left_inv := to_from C A
  right_inv := from_to C A

end
end DaggerActualPiZeroConstantHomEquivalence
