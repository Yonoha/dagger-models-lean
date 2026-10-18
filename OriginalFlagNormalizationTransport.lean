import OriginalFlagSourcePrefixCoordinates

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- Internal transport glue only: construction of this actual assembly iso is still required. -/
def normalizationFromAssembly (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) : P ⟶ normOver P := e.hom ≫ assembledNormalization P

theorem normalizationFromAssembly_whole (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    (normalizationFromAssembly P e).hom.map =
      e.hom.hom.map ≫ (assembledNormalization P).hom.map := rfl

theorem normalizationFromAssembly_triangle (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    (normalizationFromAssembly P e).hom.map ≫ (normOver P).map = P.map :=
  (normalizationFromAssembly P e).w

theorem normalizationFromAssembly_first (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    (normalizationFromAssembly P e).hom.map.app (op ⦋0⦌) P.code.first =
      (normOver P).code.first := (normalizationFromAssembly P e).hom.first

theorem normalizationFromAssembly_last (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    (normalizationFromAssembly P e).hom.map.app (op ⦋0⦌) P.code.last =
      (normOver P).code.last := (normalizationFromAssembly P e).hom.last

theorem assembly_inverse_whole (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    e.inv.hom.map ≫ e.hom.hom.map = 𝟙 (assembledSource P).code.toSSet :=
  congrArg (fun f : assembledSource P ⟶ assembledSource P ↦ f.hom.map) e.inv_hom_id

theorem assembly_forward_whole (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    e.hom.hom.map ≫ e.inv.hom.map = 𝟙 P.code.toSSet :=
  congrArg (fun f : P ⟶ P ↦ f.hom.map) e.hom_inv_id

theorem assembly_vertex_surjective (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) : Function.Surjective (mapVertices e.hom.hom.map) := by
  intro z
  refine ⟨mapVertices e.inv.hom.map z, ?_⟩
  have h := congrFun (congrArg
    (mapVertices (T := (assembledSource P).code) (U := (assembledSource P).code))
    (assembly_inverse_whole P e)) z
  rw [mapVertices_comp, mapVertices_id] at h
  exact h

theorem normalizationFromAssembly_surjective (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) :
    Function.Surjective (mapVertices (normalizationFromAssembly P e).hom.map) := by
  rw [normalizationFromAssembly_whole, mapVertices_comp]
  exact (assembledNormalization_surjective P).comp (assembly_vertex_surjective P e)

theorem normalizationFromAssembly_operator (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) {s t : SimplexCategoryᵒᵖ} (α : s ⟶ t) :
    P.code.toSSet.map α ≫ (normalizationFromAssembly P e).hom.map.app t =
      (normalizationFromAssembly P e).hom.map.app s ≫ (normOver P).code.toSSet.map α :=
  (normalizationFromAssembly P e).hom.map.naturality α

def normalizedFlagFromAssembly (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) {n : ℕ} (F : Flag.{u} P.code n) :
    Flag.{u} (normOver P).code n := NecklaceCode.Flag.map (normalizationFromAssembly P e).hom F

theorem normalizedFlagFromAssembly_chain (P : NecklacesOver X a b)
    (e : P ≅ assembledSource P) {n : ℕ} (F : Flag.{u} P.code n) (i : Fin (n + 1)) :
    (normalizedFlagFromAssembly P e F).chain i =
      (mapVertices (normalizationFromAssembly P e).hom.map) '' F.chain i := rfl

end

end DaggerOriginalFlagFlankification
