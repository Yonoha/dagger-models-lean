import SSetGluingPushouts

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u
namespace DaggerSSetGluing
noncomputable section
set_option autoImplicit false

/-- One strict compatible middle span, with both relative comparisons on their actual pushouts. -/
structure Middle {A X Z A' X' Z' : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (k' : A' ⟶ X') (ell' : A' ⟶ Z')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') where
  MA : SSet.{u}
  MX : SSet.{u}
  MZ : SSet.{u}
  Mk : MA ⟶ MX
  Mu : MA ⟶ MZ
  iA : A ⟶ MA
  iX : X ⟶ MX
  iZ : Z ⟶ MZ
  sA : A' ⟶ MA
  sX : X' ⟶ MX
  sZ : Z' ⟶ MZ
  pA : MA ⟶ A'
  pX : MX ⟶ X'
  pZ : MZ ⟶ Z'
  ik : k ≫ iX = iA ≫ Mk
  ie : ell ≫ iZ = iA ≫ Mu
  sk : k' ≫ sX = sA ≫ Mk
  se : ell' ≫ sZ = sA ≫ Mu
  pk : Mk ≫ pX = pA ≫ k'
  pe : Mu ≫ pZ = pA ≫ ell'
  ia : iA ≫ pA = a
  ib : iX ≫ pX = b
  ic : iZ ≫ pZ = c
  sa : sA ≫ pA = 𝟙 A'
  sb : sX ≫ pX = 𝟙 X'
  sc : sZ ≫ pZ = 𝟙 Z'
  cof_iA : Cofibration iA
  cof_iZ : Cofibration iZ
  cof_sA : Cofibration sA
  cof_sZ : Cofibration sZ
  fib_pA : Fibration pA
  fib_pX : Fibration pX
  fib_pZ : Fibration pZ
  weak_pA : WeakEquivalence pA
  weak_pX : WeakEquivalence pX
  weak_pZ : WeakEquivalence pZ
  cof_qi : Cofibration (relativeMap k Mk iA iX ik)
  cof_qs : Cofibration (relativeMap k' Mk sA sX sk)
  jZ : Z ⨿ Z' ⟶ MZ
  jA : A ⨿ A' ⟶ MA
  qA : MA ⟶ pullback ell' pZ
  tau : A ⨿ A' ⟶ pullback ell' pZ
  tau_fst : tau ≫ pullback.fst ell' pZ = coprod.desc a (𝟙 A')
  tau_snd : tau ≫ pullback.snd ell' pZ = coprod.map ell ell' ≫ jZ
  jZ_fac : jZ ≫ pZ = coprod.desc c (𝟙 Z')
  jA_fac : jA ≫ qA = tau
  pA_eq : pA = qA ≫ pullback.fst ell' pZ
  Mu_eq : Mu = qA ≫ pullback.snd ell' pZ
  T : SSet.{u}
  TX : X ⨿ X' ⟶ T
  TM : MA ⟶ T
  squareT : IsPushout (coprod.map k k') jA TX TM
  theta : T ⟶ X'
  theta_left : TX ≫ theta = coprod.desc b (𝟙 X')
  theta_right : TM ≫ theta = pA ≫ k'
  jRel : T ⟶ MX
  jRel_fac : jRel ≫ pX = theta
  JX : X ⨿ X' ⟶ MX
  JX_eq : JX = TX ≫ jRel
  Mk_eq : Mk = TM ≫ jRel
  iA_eq : iA = coprod.inl ≫ jA
  sA_eq : sA = coprod.inr ≫ jA
  iX_eq : iX = coprod.inl ≫ JX
  sX_eq : sX = coprod.inr ≫ JX
  iZ_eq : iZ = coprod.inl ≫ jZ
  sZ_eq : sZ = coprod.inr ≫ jZ
  cof_jZ : Cofibration jZ
  cof_jA : Cofibration jA
  cof_jRel : Cofibration jRel
  fib_qA : Fibration qA
  weak_qA : WeakEquivalence qA
  rhoI : pushout k iA ⟶ T
  rhoS : pushout k' sA ⟶ T
  rhoI_left : pushout.inl k iA ≫ rhoI = coprod.inl ≫ TX
  rhoI_right : pushout.inr k iA ≫ rhoI = TM
  rhoS_left : pushout.inl k' sA ≫ rhoS = coprod.inr ≫ TX
  rhoS_right : pushout.inr k' sA ≫ rhoS = TM
  squareI : IsPushout k' (sA ≫ pushout.inr k iA) (coprod.inr ≫ TX) rhoI
  squareS : IsPushout k (iA ≫ pushout.inr k' sA) (coprod.inl ≫ TX) rhoS
  qi_eq : relativeMap k Mk iA iX ik = rhoI ≫ jRel
  qs_eq : relativeMap k' Mk sA sX sk = rhoS ≫ jRel

/-- Exactly three chosen cofibration/trivial-fibration factorizations, in order Z,A,X. -/
def middle {A X Z A' X' Z' : SSet.{u}}
    (k : A ⟶ X) (ell : A ⟶ Z) (k' : A' ⟶ X') (ell' : A' ⟶ Z')
    [Mono k] [Mono k'] (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z')
    (hk : k ≫ b = a ≫ k') (he : ell ≫ c = a ≫ ell') :
    Middle k ell k' ell' a b c := by
  let hZ := MorphismProperty.factorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u}) (coprod.desc c (𝟙 Z'))
  let tau : A ⨿ A' ⟶ pullback ell' hZ.p :=
    pullback.lift (coprod.desc a (𝟙 A')) (coprod.map ell ell' ≫ hZ.i) (by
      apply coprod.hom_ext
      · simpa [Category.assoc] using he.symm
      · simp [Category.assoc])
  let hA := MorphismProperty.factorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u}) tau
  let pA := hA.p ≫ pullback.fst ell' hZ.p
  let Mu := hA.p ≫ pullback.snd ell' hZ.p
  have foldA : hA.i ≫ pA = coprod.desc a (𝟙 A') := by simp [pA, tau]
  have foldMu : hA.i ≫ Mu = coprod.map ell ell' ≫ hZ.i := by simp [Mu, tau]
  have pe : Mu ≫ hZ.p = pA ≫ ell' := by simp [Mu, pA, pullback.condition]
  let theta : pushout (coprod.map k k') hA.i ⟶ X' :=
    pushout.desc (coprod.desc b (𝟙 X')) (pA ≫ k') (by
      rw [← Category.assoc, foldA]
      apply coprod.hom_ext
      · simpa [Category.assoc] using hk
      · simp)
  let hX := MorphismProperty.factorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u}) theta
  let TX := pushout.inl (coprod.map k k') hA.i
  let TM := pushout.inr (coprod.map k k') hA.i
  let JX := TX ≫ hX.i
  let Mk := TM ≫ hX.i
  have foldX : JX ≫ hX.p = coprod.desc b (𝟙 X') := by simp [JX, TX, theta]
  have pk : Mk ≫ hX.p = pA ≫ k' := by simp [Mk, TM, theta]
  have jMk : hA.i ≫ Mk = coprod.map k k' ≫ JX := by
    simpa [Mk, JX, TX, TM, Category.assoc] using
      congrArg (fun f ↦ f ≫ hX.i) (pushout.condition (f := coprod.map k k') (g := hA.i)).symm
  let iA := coprod.inl ≫ hA.i
  let sA := coprod.inr ≫ hA.i
  let iX := coprod.inl ≫ JX
  let sX := coprod.inr ≫ JX
  have ik : k ≫ iX = iA ≫ Mk := by simp [iX, iA, Category.assoc, jMk]
  have sk : k' ≫ sX = sA ≫ Mk := by simp [sX, sA, Category.assoc, jMk]
  let rhoI : pushout k iA ⟶ pushout (coprod.map k k') hA.i :=
    pushout.desc (coprod.inl ≫ TX) TM (by
      simpa [iA, TX, TM, Category.assoc] using
        congrArg (fun f ↦ coprod.inl ≫ f) (pushout.condition (f := coprod.map k k') (g := hA.i)))
  let rhoS : pushout k' sA ⟶ pushout (coprod.map k k') hA.i :=
    pushout.desc (coprod.inr ≫ TX) TM (by
      simpa [sA, TX, TM, Category.assoc] using
        congrArg (fun f ↦ coprod.inr ≫ f) (pushout.condition (f := coprod.map k k') (g := hA.i)))
  have hi := relative_left_isPushout k k' iA sA hA.i TX TM (by rfl) (by rfl)
    (IsPushout.of_hasPushout (coprod.map k k') hA.i)
    (pushout.inl k iA) (pushout.inr k iA) (IsPushout.of_hasPushout k iA)
    rhoI (by simp [rhoI]) (by simp [rhoI])
  have hs := relative_right_isPushout k k' iA sA hA.i TX TM (by rfl) (by rfl)
    (IsPushout.of_hasPushout (coprod.map k k') hA.i)
    (pushout.inl k' sA) (pushout.inr k' sA) (IsPushout.of_hasPushout k' sA)
    rhoS (by simp [rhoS]) (by simp [rhoS])
  letI : Cofibration k := SSet.modelCategoryQuillen.cofibration_of_mono k
  letI : Cofibration k' := SSet.modelCategoryQuillen.cofibration_of_mono k'
  letI : Cofibration rhoI := cofibration_of_square hi.flip
  letI : Cofibration rhoS := cofibration_of_square hs.flip
  have qi : relativeMap k Mk iA iX ik = rhoI ≫ hX.i := by
    apply pushout.hom_ext <;> simp [relativeMap, rhoI, iX, JX, Mk, TM, Category.assoc]
  have qs : relativeMap k' Mk sA sX sk = rhoS ≫ hX.i := by
    apply pushout.hom_ext <;> simp [relativeMap, rhoS, sX, JX, Mk, TM, Category.assoc]
  refine
    { MA := hA.Z, MX := hX.Z, MZ := hZ.Z, Mk := Mk, Mu := Mu
      iA := iA, iX := iX, iZ := coprod.inl ≫ hZ.i
      sA := sA, sX := sX, sZ := coprod.inr ≫ hZ.i
      pA := pA, pX := hX.p, pZ := hZ.p, ik := ik, sk := sk, pk := pk, pe := pe
      ie := ?_, se := ?_, ia := ?_, ib := ?_, ic := ?_, sa := ?_, sb := ?_, sc := ?_
      cof_iA := by dsimp [iA]; infer_instance
      cof_iZ := by infer_instance
      cof_sA := by dsimp [sA]; infer_instance
      cof_sZ := by infer_instance
      fib_pA := by dsimp [pA]; infer_instance
      fib_pX := by infer_instance
      fib_pZ := by infer_instance
      weak_pA := by dsimp [pA]; infer_instance
      weak_pX := by infer_instance
      weak_pZ := by infer_instance
      cof_qi := by rw [qi]; infer_instance
      cof_qs := by rw [qs]; infer_instance
      jZ := hZ.i, jA := hA.i, qA := hA.p, tau := tau
      tau_fst := by simp [tau]
      tau_snd := by simp [tau]
      jZ_fac := hZ.fac, jA_fac := hA.fac, pA_eq := rfl, Mu_eq := rfl
      T := pushout (coprod.map k k') hA.i, TX := TX, TM := TM
      squareT := IsPushout.of_hasPushout (coprod.map k k') hA.i
      theta := theta, theta_left := by simp [TX, theta]
      theta_right := by simp [TM, theta]
      jRel := hX.i, jRel_fac := hX.fac, JX := JX, JX_eq := rfl, Mk_eq := rfl
      iA_eq := rfl, sA_eq := rfl, iX_eq := rfl, sX_eq := rfl
      iZ_eq := rfl, sZ_eq := rfl
      cof_jZ := by infer_instance
      cof_jA := by infer_instance
      cof_jRel := by infer_instance
      fib_qA := by infer_instance
      weak_qA := by infer_instance
      rhoI := rhoI, rhoS := rhoS
      rhoI_left := by simp [rhoI]
      rhoI_right := by simp [rhoI]
      rhoS_left := by simp [rhoS]
      rhoS_right := by simp [rhoS]
      squareI := hi, squareS := hs, qi_eq := qi, qs_eq := qs }
  · simp [iA, Category.assoc, foldMu]
  · simp [sA, Category.assoc, foldMu]
  · simp [iA, Category.assoc, foldA]
  · simp [iX, Category.assoc, foldX]
  · simp
  · simp [sA, Category.assoc, foldA]
  · simp [sX, Category.assoc, foldX]
  · simp

end
end DaggerSSetGluing
