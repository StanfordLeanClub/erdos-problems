import Erdos278.PerfectPacking

namespace Erdos278

universe u

variable {ι : Type u} [DecidableEq ι]
variable {cap : ι → ℕ}

lemma eq_pair_of_card_two_mem {S : Finset ι} {i j : ι}
    (hcard : S.card = 2) (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    S = ({i, j} : Finset ι) := by
  have hsub : ({i, j} : Finset ι) ⊆ S := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj
  have hEq : ({i, j} : Finset ι) = S := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hij, hcard]
  exact hEq.symm

noncomputable def incidentEquiv (H : SupportFamily ι) (i : ι) :
    {A : Member H // i ∈ A.1} ≃ Member (H.filter fun S => i ∈ S) where
  toFun A := ⟨A.1.1, by simp [A.1.2, A.2]⟩
  invFun A := by
    refine ⟨⟨A.1, ?_⟩, ?_⟩
    · exact (Finset.mem_filter.mp A.2).1
    · exact (Finset.mem_filter.mp A.2).2
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro A
    cases A
    simp

lemma card_incident_eq_degree (H : SupportFamily ι) (i : ι) :
    Fintype.card {A : Member H // i ∈ A.1} = degree H i := by
  classical
  rw [degree]
  simpa [Member] using Fintype.card_congr (incidentEquiv H i)

theorem pairFamily_packable_iff
    (hcap : ∀ i, 0 < cap i)
    {H : SupportFamily ι}
    (hpair : IsPairFamily H) :
    PerfectlyPackable H cap ↔
      IntersectingFamily H ∧ ∀ i, degree H i ≤ cap i := by
  constructor
  · rintro ⟨assign, hsep⟩
    refine ⟨?_, ?_⟩
    · intro A B hne
      rcases hsep A B hne with ⟨i, hiAB, _⟩
      exact ⟨i, hiAB⟩
    · intro i
      let f : {A : Member H // i ∈ A.1} → Fin (cap i) := fun A => assign A.1 i
      have hf : Function.Injective f := by
        intro A B hEq
        by_contra hne
        have hne' : A.1 ≠ B.1 := by
          intro h
          apply hne
          exact Subtype.ext h
        rcases hsep A.1 B.1 hne' with ⟨j, hjAB, hneq⟩
        rcases Finset.mem_inter.mp hjAB with ⟨hjA, hjB⟩
        by_cases hji : j = i
        · cases hji
          exact hneq hEq
        · have hij : i ≠ j := by
            intro hij'
            exact hji hij'.symm
          have hA2 : A.1.1.card = 2 := hpair A.1.1 A.1.2
          have hB2 : B.1.1.card = 2 := hpair B.1.1 B.1.2
          have hAeq : A.1.1 = ({i, j} : Finset ι) :=
            eq_pair_of_card_two_mem hA2 A.2 hjA hij
          have hBeq : B.1.1 = ({i, j} : Finset ι) :=
            eq_pair_of_card_two_mem hB2 B.2 hjB hij
          apply hne'
          apply Subtype.ext
          rw [hAeq, hBeq]
      have hle : Fintype.card {A : Member H // i ∈ A.1} ≤ cap i := by
        simpa using Fintype.card_le_of_injective f hf
      simpa [card_incident_eq_degree (H := H) (i := i)] using hle
  · rintro ⟨hinter, hdeg⟩
    classical
    let emb : ∀ i, {A : Member H // i ∈ A.1} ↪ Fin (cap i) := fun i => by
      let e : {A : Member H // i ∈ A.1} ≃ Fin (Fintype.card {A : Member H // i ∈ A.1}) :=
        Fintype.equivFin {A : Member H // i ∈ A.1}
      have hbound : Fintype.card {A : Member H // i ∈ A.1} ≤ cap i := by
        simpa [card_incident_eq_degree (H := H) (i := i)] using hdeg i
      refine
        { toFun := fun A => ⟨(e A).1, Nat.lt_of_lt_of_le (e A).2 hbound⟩
          inj' := ?_ }
      intro A B hEq
      apply e.injective
      apply Fin.ext
      simpa using congrArg Fin.val hEq
    let base : Point cap := fun i => ⟨0, hcap i⟩
    let assign : Member H → Point cap := fun A i =>
      if hi : i ∈ A.1 then emb i ⟨A, hi⟩ else base i
    refine ⟨assign, ?_⟩
    intro A B hAB
    rcases hinter A B hAB with ⟨i, hiAB⟩
    rcases Finset.mem_inter.mp hiAB with ⟨hiA, hiB⟩
    refine ⟨i, hiAB, ?_⟩
    have hinputNe : (⟨A, hiA⟩ : {A : Member H // i ∈ A.1}) ≠ ⟨B, hiB⟩ := by
      intro h
      apply hAB
      exact congrArg Subtype.val h
    have hvalNe : emb i ⟨A, hiA⟩ ≠ emb i ⟨B, hiB⟩ := by
      intro h
      apply hinputNe
      exact (emb i).injective h
    simpa [assign, hiA, hiB] using hvalNe

end Erdos278
