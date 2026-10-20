import OriginalFixedObjectDaggerCofreeTransfer
import OriginalSplitAdjunctionFactorization

/-!
# Actual ordinary factorization from the proved dagger factorization

Lift each full ordinary arrow to its trivial C2 action and recover a dagger via the
original equivalence. Forget the proved dagger factorization and use the full counit
isomorphisms at its endpoints. The left arrow has the exact ordinary canonical LLP;
the right arrow has exactly the original Homwise fibration and weak conditions.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
open DaggerOriginalFixedObjectDaggerCofreeTransfer
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
universe u
namespace DaggerOriginalFixedObjectOrdinaryFactorizationTransfer
noncomputable section

/-- The actual trivial-action lift of full ordinary fixed-object groupoids and their arrows. -/
def ordinaryToDagger (O : Type u) : FixedStrictGroupoids O ⥤ FixedStrictDaggerGroupoids O :=
  DaggerOriginalCommutativeActionColimits.trivialFunctor (FixedStrictGroupoids O) C2.{u} ⋙
    (fixedDaggerActionEquivalence O).inverse

/-- The original counit identifies the entire forgotten trivial-action lift with the identity. -/
def ordinaryDaggerSectionIso (O : Type u) :
    ordinaryToDagger O ⋙ fixedStrictDaggerForget O ≅ 𝟭 (FixedStrictGroupoids O) :=
  NatIso.ofComponents
    (fun C ↦ (Action.forget (FixedStrictGroupoids O) C2.{u}).mapIso
      ((fixedDaggerActionEquivalence O).counitIso.app
        (Action.trivial C2.{u} C))) (by
      intro C D F
      exact congrArg (fun k ↦ (Action.forget (FixedStrictGroupoids O) C2.{u}).map k)
        ((fixedDaggerActionEquivalence O).counitIso.hom.naturality
          ((DaggerOriginalCommutativeActionColimits.trivialFunctor
            (FixedStrictGroupoids O) C2.{u}).map F)))

/-- Every original ordinary arrow has a canonical cofibration/trivial-fibration factorization. -/
def ordinaryFactorizationData {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    (strictCofibrations O).MapFactorizationData
      (strictFibrations O ⊓ strictWeakEquivalences O) F := by
  haveI : (strictCofibrations O).RespectsIso := by
    unfold strictCofibrations
    infer_instance
  let L := fixedStrictDaggerForget O
  let S := ordinaryToDagger O
  let e := ordinaryDaggerSectionIso O
  let d : (strictDaggerCofibrations O).MapFactorizationData
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O) (S.map F) :=
    Classical.choice (MorphismProperty.HasFactorization.nonempty_mapFactorizationData (S.map F))
  refine ⟨L.obj d.Z, (e.app C).inv ≫ L.map d.i, L.map d.p ≫ (e.app D).hom, ?_, ?_, ?_⟩
  · calc
      ((e.app C).inv ≫ L.map d.i) ≫ (L.map d.p ≫ (e.app D).hom) =
          (e.app C).inv ≫ L.map (d.i ≫ d.p) ≫ (e.app D).hom := by
            simp only [Functor.map_comp, Category.assoc]
      _ = (e.app C).inv ≫ (S ⋙ L).map F ≫ (e.app D).hom := by rw [d.fac]; rfl
      _ = F := NatIso.naturality_1 e F
  · exact MorphismProperty.RespectsIso.precomp (strictCofibrations O) (e.app C).inv _
      (forget_cofibration d.i d.hi)
  · exact MorphismProperty.RespectsIso.postcomp (trivialFibrations (FixedStrictGroupoids O))
      (e.app D).hom _
      ((forget_trivialFibration_iff d.p).1 d.hp)

/-- The actual same-O ordinary canonical factorization is now unconditional. -/
instance strictCofTrivialFibFactorization (O : Type u) :
    (strictCofibrations O).HasFactorization (strictFibrations O ⊓ strictWeakEquivalences O) :=
  ⟨fun F ↦ ⟨ordinaryFactorizationData F⟩⟩

/-- The independently specified split-adjunction statement applies to these exact original
classes. -/
theorem ordinaryFactorization_exact_challenge (O : Type u) :
    (strictCofibrations O).HasFactorization (strictFibrations O ⊓ strictWeakEquivalences O) := by
  let P := trivialFibrations (FixedStrictGroupoids O)
  let Q := trivialFibrations (FixedStrictDaggerGroupoids O)
  haveI : Q.llp.HasFactorization Q := by
    change (strictDaggerCofibrations O).HasFactorization
      (strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O)
    infer_instance
  have hQ : Q = P.inverseImage (fixedStrictDaggerForget O) := by
    funext C D F
    exact propext (forget_trivialFibration_iff F)
  exact DaggerOriginalSplitAdjunctionFactorization.exact_statement
    (FixedStrictGroupoids O) inferInstance (FixedStrictDaggerGroupoids O) inferInstance
    (fixedStrictDaggerForget O) (daggerCofree O) (ordinaryToDagger O)
    (daggerForgetCofreeAdjunction O) (ordinaryDaggerSectionIso O)
    P Q inferInstance inferInstance hQ daggerCofree_trivialFibration

end
end DaggerOriginalFixedObjectOrdinaryFactorizationTransfer
