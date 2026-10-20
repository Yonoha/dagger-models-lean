import DaggerModels.FreeSimplicialLift
import DaggerModels.DaggerSimplicialForget
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The free dagger simplicial category adjunction

The actual category of finite paths is left adjoint to forgetting composition.
The unit inserts singleton edges; the inverse Hom map composes paths. This is
the free construction at the start of Part I `bg.lem.presentable`, without
assuming monadicity, presentability, or any model structure.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.FreeDaggerSimplicialCategory

open DaggerSimplicialCat FreeSimplicialExtension

/-- Insert each edge as the corresponding path of length one. -/
noncomputable def unit (G : DaggerSimplicialGraph.{u}) :
    G ⟶ forgetGraph.obj (FreeSimplicialPaths.daggerCat G) where
  obj := id
  map := FreeSimplicialPaths.inclusion G
  map_dagger := FreeSimplicialPaths.inclusion_dagger G

/-- Restrict a dagger simplicial functor to the original edges. -/
noncomputable def restrict {G : DaggerSimplicialGraph.{u}} {C : DaggerSimplicialCat.{u, u}}
    (F : FreeSimplicialPaths.daggerCat G ⟶ C) : G ⟶ forgetGraph.obj C :=
  unit G ≫ forgetGraph.map F

/-- The extension of a dagger-compatible edge map preserves the path dagger. -/
theorem value_reverse {G : DaggerSimplicialGraph.{u}} {C : DaggerSimplicialCat.{u, u}}
    (F : G ⟶ forgetGraph.obj C) (n : SimplexCategoryᵒᵖ) {x y : G.Obj}
    (p : FreeSimplicialPaths.Path G n x y) :
    value G (C := C.Obj) F.obj F.map n (FreeSimplicialPaths.reverse G n p) =
      (DaggerSimplicialStructure.dagger (C := C.Obj) (F.obj x) (F.obj y)).app n
        (value G (C := C.Obj) F.obj F.map n p) := by
  induction p with
  | nil =>
    exact (DaggerSimplicialStructure.dagger_id_app (C := C.Obj) (F.obj x) n).symm
  | @cons y z p e ih =>
    rw [FreeSimplicialPaths.reverse_cons, value_comp, value_singleton, ih, value_cons,
      DaggerSimplicialStructure.dagger_comp_app]
    have he := congrArg (fun h ↦ h.app n e) (F.map_dagger y z)
    change (DaggerSimplicialStructure.dagger (C := C.Obj) (F.obj y) (F.obj z)).app n
      ((F.map y z).app n e) = (F.map z y).app n ((G.dagger y z).app n e) at he
    rw [he]

/-- Compose finite paths to extend a graph map uniquely. -/
noncomputable def lift {G : DaggerSimplicialGraph.{u}} {C : DaggerSimplicialCat.{u, u}}
    (F : G ⟶ forgetGraph.obj C) : FreeSimplicialPaths.daggerCat G ⟶ C where
  toEnrichedFunctor := extend G (C := C.Obj) F.obj F.map
  map_dagger x y := by
    ext n p
    exact (value_reverse F n p).symm

@[simp] theorem restrict_lift {G : DaggerSimplicialGraph.{u}}
    {C : DaggerSimplicialCat.{u, u}} (F : G ⟶ forgetGraph.obj C) :
    restrict (lift F) = F := by
  apply DaggerSimplicialGraph.Map.ext (f := restrict (lift F)) (g := F) rfl
  apply heq_of_eq
  funext x y
  exact inclusion_extend G (C := C.Obj) F.obj F.map x y

@[simp] theorem lift_restrict {G : DaggerSimplicialGraph.{u}}
    {C : DaggerSimplicialCat.{u, u}} (F : FreeSimplicialPaths.daggerCat G ⟶ C) :
    lift (restrict F) = F := by
  apply DaggerSimplicialCat.Hom.ext
  exact extend_restrict G F.toEnrichedFunctor

/-- The actual free-category Hom equivalence, with restriction along singleton edges. -/
noncomputable def homEquiv (G : DaggerSimplicialGraph.{u}) (C : DaggerSimplicialCat.{u, u}) :
    (FreeSimplicialPaths.daggerCat G ⟶ C) ≃ (G ⟶ forgetGraph.obj C) where
  toFun := restrict
  invFun := lift
  left_inv := lift_restrict
  right_inv := restrict_lift

/-- The Hom equivalence is natural in its target dagger simplicial category. -/
theorem homEquiv_naturality (G : DaggerSimplicialGraph.{u})
    (C D : DaggerSimplicialCat.{u, u}) (H : C ⟶ D)
    (F : FreeSimplicialPaths.daggerCat G ⟶ C) :
    homEquiv G D (F ≫ H) = homEquiv G C F ≫ forgetGraph.map H := by
  change unit G ≫ forgetGraph.map (F ≫ H) = _
  rw [Functor.map_comp, ← Category.assoc]
  rfl

/-- The free dagger simplicial category functor has the original finite-path objects. -/
noncomputable def functor : DaggerSimplicialGraph.{u} ⥤ DaggerSimplicialCat.{u, u} :=
  Adjunction.leftAdjointOfEquiv homEquiv homEquiv_naturality

/-- The genuine free–forgetful adjunction on dagger simplicial graphs and categories. -/
noncomputable def adjunction : functor.{u} ⊣ forgetGraph :=
  Adjunction.adjunctionOfEquivLeft homEquiv homEquiv_naturality

/-- The adjunction unit is the original singleton-edge inclusion. -/
@[simp] theorem adjunction_unit (G : DaggerSimplicialGraph.{u}) :
    adjunction.unit.app G = unit G := by
  change unit G ≫ forgetGraph.map (𝟙 _) = unit G
  simp

/-- The original graph forgetful functor has an actual left adjoint. -/
theorem exists_freeDaggerSimplicialCategoryAdjunction :
    ∃ F : DaggerSimplicialGraph.{u} ⥤ DaggerSimplicialCat.{u, u},
      Nonempty (F ⊣ forgetGraph) := ⟨functor, ⟨adjunction⟩⟩

end DaggerModels.FreeDaggerSimplicialCategory

namespace DaggerModels

/-- Every dagger simplicial graph has a free category, with its full universal property. -/
theorem exists_freeDaggerSimplicialCategory (G : DaggerSimplicialGraph.{u}) :
    ∃ (C : DaggerSimplicialCat.{u, u})
      (eta : DaggerSimplicialGraph.Map G (DaggerSimplicialCat.underlyingGraph C)),
      ∀ D : DaggerSimplicialCat.{u, u},
        Function.Bijective (DaggerSimplicialCat.restrictGraph eta (D := D)) := by
  refine ⟨FreeSimplicialPaths.daggerCat G, FreeDaggerSimplicialCategory.unit G, ?_⟩
  intro D
  exact (FreeDaggerSimplicialCategory.homEquiv G D).bijective

end DaggerModels
