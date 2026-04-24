import Erdos278.PerfectPacking

namespace Erdos278

universe u

variable {ι : Type u} [DecidableEq ι]
variable {cap : ι → ℕ}

lemma union_eq_union_of_disjoint_left {A B C : Finset ι}
    (hA : Disjoint C A) (hB : Disjoint C B) (hEq : C ∪ A = C ∪ B) : A = B := by
  apply Finset.ext
  intro x
  constructor
  · intro hxA
    have hxCU : x ∈ C ∪ A := Finset.mem_union.mpr (Or.inr hxA)
    have hxCB : x ∈ C ∪ B := by simpa [hEq] using hxCU
    rcases Finset.mem_union.mp hxCB with hxC | hxB
    · exact False.elim ((Finset.disjoint_left.mp hA) hxC hxA)
    · exact hxB
  · intro hxB
    have hxCU : x ∈ C ∪ B := Finset.mem_union.mpr (Or.inr hxB)
    have hxCA : x ∈ C ∪ A := by simpa [hEq] using hxCU
    rcases Finset.mem_union.mp hxCA with hxC | hxA
    · exact False.elim ((Finset.disjoint_left.mp hB) hxC hxB)
    · exact hxA

lemma addCore_injective
    (C : Finset ι) (Lk : SupportFamily ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    Function.Injective (fun A : Member Lk => C ∪ A.1) := by
  intro A B hEq
  apply Subtype.ext
  exact union_eq_union_of_disjoint_left (hdisj A.1 A.2) (hdisj B.1 B.2) hEq

noncomputable def addCoreMemberEquiv
    (C : Finset ι) (Lk : SupportFamily ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    Member Lk ≃ Member (addCore C Lk) := by
  classical
  let f : Member Lk → Member (addCore C Lk) := fun A => ⟨C ∪ A.1, by
    refine Finset.mem_image.mpr ?_
    exact ⟨A.1, A.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    exact union_eq_union_of_disjoint_left
      (hdisj A.1 A.2) (hdisj B.1 B.2) (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro U
    rcases Finset.mem_image.mp U.2 with ⟨L, hL, hLU⟩
    refine ⟨⟨L, hL⟩, ?_⟩
    apply Subtype.ext
    exact hLU
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

def restrictToCore (C : Finset ι) (a : Point cap) : CorePatternType C cap :=
  fun i => a i.1

lemma separatesOn_core_of_restrictToCore_ne
    (C : Finset ι) {a b : Point cap}
    (hpat : restrictToCore (cap := cap) C a ≠ restrictToCore (cap := cap) C b) :
    SeparatesOn cap C C a b := by
  classical
  by_contra hsep
  apply hpat
  funext i
  by_contra hne
  apply hsep
  exact ⟨i.1, Finset.mem_inter.mpr ⟨i.2, i.2⟩, hne⟩

lemma separatesOn_of_addCore_samePattern
    (C A B : Finset ι) {a b : Point cap}
    (hpat : restrictToCore (cap := cap) C a = restrictToCore (cap := cap) C b)
    (hsep : SeparatesOn cap (C ∪ A) (C ∪ B) a b) :
    SeparatesOn cap A B a b := by
  rcases hsep with ⟨i, hi, hne⟩
  rcases Finset.mem_inter.mp hi with ⟨hiCA, hiCB⟩
  have hi_notC : i ∉ C := by
    intro hiC
    have hEq : a i = b i := by
      exact congrFun hpat ⟨i, hiC⟩
    exact hne hEq
  have hiA : i ∈ A := by
    rcases Finset.mem_union.mp hiCA with hiC | hiA
    · exact False.elim (hi_notC hiC)
    · exact hiA
  have hiB : i ∈ B := by
    rcases Finset.mem_union.mp hiCB with hiC | hiB
    · exact False.elim (hi_notC hiC)
    · exact hiB
  exact ⟨i, Finset.mem_inter.mpr ⟨hiA, hiB⟩, hne⟩

lemma separatesOn_mono {S T S' T' : Finset ι} {a b : Point cap}
    (hS : S ⊆ S') (hT : T ⊆ T') :
    SeparatesOn cap S T a b → SeparatesOn cap S' T' a b := by
  rintro ⟨i, hi, hne⟩
  rcases Finset.mem_inter.mp hi with ⟨hiS, hiT⟩
  exact ⟨i, Finset.mem_inter.mpr ⟨hS hiS, hT hiT⟩, hne⟩

lemma addCore_packable_to_packColorable
    (C : Finset ι) (Lk : SupportFamily ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    PerfectlyPackable (addCore C Lk) cap →
      PackColorable Lk cap (CorePatternType C cap) := by
  classical
  intro hpack
  rcases hpack with ⟨assignAdd, hsepAdd⟩
  let e := addCoreMemberEquiv C Lk hdisj
  let assignL : Member Lk → Point cap := fun A => assignAdd (e A)
  refine ⟨fun A => restrictToCore (cap := cap) C (assignL A), ?_⟩
  intro t
  let ec := colorClassMemberEquiv Lk (fun A => restrictToCore (cap := cap) C (assignL A)) t
  refine ⟨fun U => assignL (ec.symm U).1, ?_⟩
  intro U V hUV
  have hUV' : ec.symm U ≠ ec.symm V := by
    intro h
    apply hUV
    simpa using congrArg ec h
  have hABne : (ec.symm U).1 ≠ (ec.symm V).1 := by
    intro h
    apply hUV'
    apply Subtype.ext
    exact h
  have hEne : e ((ec.symm U).1) ≠ e ((ec.symm V).1) := by
    intro h
    apply hABne
    exact e.injective h
  have hpat :
      restrictToCore (cap := cap) C (assignL ((ec.symm U).1)) =
        restrictToCore (cap := cap) C (assignL ((ec.symm V).1)) := by
    rw [(ec.symm U).2, (ec.symm V).2]
  have hsep' :
      SeparatesOn cap (((ec.symm U).1).1) (((ec.symm V).1).1)
        (assignL ((ec.symm U).1)) (assignL ((ec.symm V).1)) := by
    exact separatesOn_of_addCore_samePattern (cap := cap)
      C (((ec.symm U).1).1) (((ec.symm V).1).1) hpat
      (hsepAdd (e ((ec.symm U).1)) (e ((ec.symm V).1)) hEne)
  have hU : ((ec.symm U).1).1 = U.1 := by
    change (ec (ec.symm U)).1 = U.1
    exact congrArg
      (fun W : Member (colorClass Lk
        (fun A => restrictToCore (cap := cap) C (assignL A)) t) => W.1)
      (ec.apply_symm_apply U)
  have hV : ((ec.symm V).1).1 = V.1 := by
    change (ec (ec.symm V)).1 = V.1
    exact congrArg
      (fun W : Member (colorClass Lk
        (fun A => restrictToCore (cap := cap) C (assignL A)) t) => W.1)
      (ec.apply_symm_apply V)
  simpa [assignL, hU, hV] using hsep'

theorem addCore_packable_iff_packColorable
    (C : Finset ι) (Lk : SupportFamily ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    PerfectlyPackable (addCore C Lk) cap ↔
      PackColorable Lk cap (CorePatternType C cap) := by
  constructor
  · exact addCore_packable_to_packColorable (cap := cap) C Lk hdisj
  · intro hcolor
    classical
    rcases hcolor with ⟨color, hpackColor⟩
    let assignColor : ∀ t : CorePatternType C cap, Member (colorClass Lk color t) → Point cap :=
      fun t => Classical.choose (hpackColor t)
    have hsepColor :
        ∀ t : CorePatternType C cap,
          ∀ U V : Member (colorClass Lk color t),
            U ≠ V → SeparatesOn cap U.1 V.1 (assignColor t U) (assignColor t V) := by
      intro t
      exact Classical.choose_spec (hpackColor t)
    have hassignColor_transport :
        ∀ {A : Member Lk} {s t : CorePatternType C cap}
          (hs : color A = s) (ht : color A = t) (h : s = t) (i : ι),
          assignColor s ((colorClassMemberEquiv Lk color s) ⟨A, hs⟩) i =
            assignColor t ((colorClassMemberEquiv Lk color t) ⟨A, ht⟩) i := by
      intro A s t hs ht h i
      cases h
      have hsub : (⟨A, hs⟩ : {A : Member Lk // color A = s}) = ⟨A, ht⟩ := by
        apply Subtype.ext
        rfl
      exact congrArg (fun W => assignColor s W i)
        (congrArg (colorClassMemberEquiv Lk color s) hsub)
    let e := addCoreMemberEquiv C Lk hdisj
    let assignAdd : Member (addCore C Lk) → Point cap := fun U i =>
      let A := e.symm U
      let t := color A
      let ec := colorClassMemberEquiv Lk color t
      if hi : i ∈ C then t ⟨i, hi⟩ else assignColor t (ec ⟨A, rfl⟩) i
    refine ⟨assignAdd, ?_⟩
    intro U V hUV
    let AU : Member Lk := e.symm U
    let AV : Member Lk := e.symm V
    have hAUV : AU ≠ AV := by
      intro h
      apply hUV
      simpa [AU, AV] using congrArg e h
    have hUeq : C ∪ AU.1 = U.1 := by
      change (e AU).1 = U.1
      exact congrArg (fun W : Member (addCore C Lk) => W.1) (e.apply_symm_apply U)
    have hVeq : C ∪ AV.1 = V.1 := by
      change (e AV).1 = V.1
      exact congrArg (fun W : Member (addCore C Lk) => W.1) (e.apply_symm_apply V)
    by_cases hpatEq : color AU = color AV
    · have htV : color AV = color AU := hpatEq.symm
      let t : CorePatternType C cap := color AU
      let ec := colorClassMemberEquiv Lk color t
      let Uc : Member (colorClass Lk color t) := ec ⟨AU, rfl⟩
      let Vc : Member (colorClass Lk color t) := ec ⟨AV, htV⟩
      have hUcVc : Uc ≠ Vc := by
        intro h
        apply hAUV
        simpa [Uc, Vc] using congrArg Subtype.val (ec.injective h)
      have hassignU : ∀ i, i ∈ AU.1 → assignAdd U i = assignColor t Uc i := by
        intro i hi
        have hi_notC : i ∉ C := by
          intro hiC
          exact (Finset.disjoint_left.mp (hdisj AU.1 AU.2)) hiC hi
        simp [assignAdd, AU, t, ec, Uc, hi_notC]
      have hassignV : ∀ i, i ∈ AV.1 → assignAdd V i = assignColor t Vc i := by
        intro i hi
        have hi_notC : i ∉ C := by
          intro hiC
          exact (Finset.disjoint_left.mp (hdisj AV.1 AV.2)) hiC hi
        have htransport :
            assignColor (color AV)
              ((colorClassMemberEquiv Lk color (color AV)) ⟨AV, rfl⟩) i =
              assignColor t Vc i := by
          exact hassignColor_transport (A := AV) (s := color AV) (t := t)
            rfl htV htV i
        simpa [assignAdd, AV, hi_notC] using htransport
      have hsepLink : SeparatesOn cap AU.1 AV.1 (assignAdd U) (assignAdd V) := by
        rcases hsepColor t Uc Vc hUcVc with ⟨i, hi, hne⟩
        rcases Finset.mem_inter.mp hi with ⟨hiU, hiV⟩
        refine ⟨i, hi, ?_⟩
        intro hEq
        apply hne
        calc
          assignColor t Uc i = assignAdd U i := (hassignU i hiU).symm
          _ = assignAdd V i := hEq
          _ = assignColor t Vc i := hassignV i hiV
      have hsubU : AU.1 ⊆ U.1 := by
        intro i hi
        have : i ∈ C ∪ AU.1 := Finset.mem_union.mpr (Or.inr hi)
        simpa [hUeq] using this
      have hsubV : AV.1 ⊆ V.1 := by
        intro i hi
        have : i ∈ C ∪ AV.1 := Finset.mem_union.mpr (Or.inr hi)
        simpa [hVeq] using this
      exact separatesOn_mono (cap := cap) hsubU hsubV hsepLink
    · have hcoreU : restrictToCore (cap := cap) C (assignAdd U) = color AU := by
        funext i
        simp [restrictToCore, assignAdd, AU, i.2]
      have hcoreV : restrictToCore (cap := cap) C (assignAdd V) = color AV := by
        funext i
        simp [restrictToCore, assignAdd, AV, i.2]
      have hcoreNe :
          restrictToCore (cap := cap) C (assignAdd U) ≠
            restrictToCore (cap := cap) C (assignAdd V) := by
        intro hEq
        apply hpatEq
        calc
          color AU = restrictToCore (cap := cap) C (assignAdd U) := hcoreU.symm
          _ = restrictToCore (cap := cap) C (assignAdd V) := hEq
          _ = color AV := hcoreV
      have hsepCore : SeparatesOn cap C C (assignAdd U) (assignAdd V) := by
        exact separatesOn_core_of_restrictToCore_ne (cap := cap) C hcoreNe
      have hsubU : C ⊆ U.1 := by
        intro i hi
        have : i ∈ C ∪ AU.1 := Finset.mem_union.mpr (Or.inl hi)
        simpa [hUeq] using this
      have hsubV : C ⊆ V.1 := by
        intro i hi
        have : i ∈ C ∪ AV.1 := Finset.mem_union.mpr (Or.inl hi)
        simpa [hVeq] using this
      exact separatesOn_mono (cap := cap) hsubU hsubV hsepCore

theorem card_corePatternType
    (C : Finset ι) (cap : ι → ℕ) :
    Fintype.card (CorePatternType C cap) = Finset.prod C cap := by
  classical
  unfold CorePatternType
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  simpa using (Finset.prod_attach C cap)

theorem addCore_packable_iff_chiPackLe
    (C : Finset ι) (Lk : SupportFamily ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    PerfectlyPackable (addCore C Lk) cap ↔
      ChiPackLe Lk cap (Fintype.card (CorePatternType C cap)) := by
  classical
  let eκ : CorePatternType C cap ≃ Fin (Fintype.card (CorePatternType C cap)) :=
    Fintype.equivFin (CorePatternType C cap)
  rw [addCore_packable_iff_packColorable (cap := cap) C Lk hdisj]
  constructor
  · rintro ⟨color, hpackColor⟩
    refine ⟨fun A => eκ (color A), ?_⟩
    intro t
    simpa [colorClass_relabel (Lk := Lk) (color := color) (e := eκ) (t := t)]
      using hpackColor (eκ.symm t)
  · rintro ⟨color, hpackColor⟩
    refine ⟨fun A => eκ.symm (color A), ?_⟩
    intro t
    simpa [colorClass_relabel (Lk := Lk) (color := color) (e := eκ.symm) (t := t)]
      using hpackColor (eκ t)

end Erdos278
