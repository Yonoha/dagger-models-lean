import ChosenNecklaceWedgeFunctor
import ChosenNecklaceFlags

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode.Flag

noncomputable section

variable {T U T' U' V : NecklaceCode} {n k : ℕ}

/-- Full unflanked flags are joined using the two actual necklace vertex maps. -/
def wedge (F : Flag.{u} T n) (G : Flag.{u} U n) : Flag.{u} (NecklaceCode.wedge T U) n where
  chain :=
    { toFun i := mapVertices (wedgeιLeft T U) '' F.chain i ∪
        mapVertices (wedgeιRight T U) '' G.chain i
      monotone' _ _ h := Set.union_subset_union (Set.image_mono (F.chain.monotone h))
        (Set.image_mono (G.chain.monotone h)) }
  joints v hv := by
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      left
      refine ⟨ULift.up w, F.joints _ hw, ?_⟩
      rw [wedgeιLeft_vertices]
      exact ULift.ext _ _ he
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      right
      refine ⟨ULift.up w, G.joints _ hw, ?_⟩
      rw [wedgeιRight_vertices]
      exact ULift.ext _ _ he

theorem wedge_restrict (α : Fin (k + 1) →o Fin (n + 1))
    (F : Flag.{u} T n) (G : Flag.{u} U n) :
    restrict α (wedge F G) = wedge (restrict α F) (restrict α G) :=
  ext (fun _ ↦ rfl)

theorem wedge_map (f : Hom.{u} T T') (g : Hom.{u} U U')
    (F : Flag.{u} T n) (G : Flag.{u} U n) :
    map (wedgeMap f g) (wedge F G) = wedge (map f F) (map g G) := by
  apply ext
  intro i
  have hl := congrArg mapVertices (wedgeMap_left f g)
  have hr := congrArg mapVertices (wedgeMap_right f g)
  rw [mapVertices_comp, mapVertices_comp] at hl hr
  change mapVertices (wedgeMap f g).map ''
      (mapVertices (wedgeιLeft T U) '' F.chain i ∪
        mapVertices (wedgeιRight T U) '' G.chain i) =
    mapVertices (wedgeιLeft T' U') '' (mapVertices f.map '' F.chain i) ∪
      mapVertices (wedgeιRight T' U') '' (mapVertices g.map '' G.chain i)
  simp only [Set.image_union, Set.image_image]
  change (mapVertices (wedgeMap f g).map ∘ mapVertices (wedgeιLeft T U)) '' F.chain i ∪
      (mapVertices (wedgeMap f g).map ∘ mapVertices (wedgeιRight T U)) '' G.chain i = _
  rw [hl, hr]
  rfl

theorem wedge_assoc (F : Flag.{u} T n) (G : Flag.{u} U n) (H : Flag.{u} V n) :
    map (wedgeAssocCodeHom T U V) (wedge (wedge F G) H) = wedge F (wedge G H) := by
  apply ext
  intro i
  have hT := congrArg mapVertices (wedgeAssocHom_T.{u} T U V)
  have hU := congrArg mapVertices (wedgeAssocHom_U.{u} T U V)
  have hV := congrArg mapVertices (wedgeAssocHom_V.{u} T U V)
  dsimp only [tripleLeftT, tripleLeftU, tripleLeftV,
    tripleRightT, tripleRightU, tripleRightV] at hT hU hV
  simp only [mapVertices_comp] at hT hU hV
  change mapVertices (wedgeAssocHom T U V) ''
      (mapVertices (wedgeιLeft (NecklaceCode.wedge T U) V) ''
        (mapVertices (wedgeιLeft T U) '' F.chain i ∪
          mapVertices (wedgeιRight T U) '' G.chain i) ∪
        mapVertices (wedgeιRight (NecklaceCode.wedge T U) V) '' H.chain i) =
    mapVertices (wedgeιLeft T (NecklaceCode.wedge U V)) '' F.chain i ∪
      mapVertices (wedgeιRight T (NecklaceCode.wedge U V)) ''
        (mapVertices (wedgeιLeft U V) '' G.chain i ∪
          mapVertices (wedgeιRight U V) '' H.chain i)
  simp only [Set.image_union, Set.image_image]
  have t := congrArg (fun f ↦ f '' F.chain i) hT
  have g := congrArg (fun f ↦ f '' G.chain i) hU
  have h := congrArg (fun f ↦ f '' H.chain i) hV
  dsimp only [Function.comp_def] at t g h
  rw [t, g, h, Set.union_assoc]

end

end DaggerChosenRigidificationNecklace.NecklaceCode.Flag
