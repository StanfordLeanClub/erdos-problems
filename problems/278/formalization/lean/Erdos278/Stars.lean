import Erdos278.Erdos278Core

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

/-- The pair-support family consisting of all edges from a center `c` to petals in `P`. -/
def starFamily (c : ι) (P : Finset ι) : SupportFamily ι :=
  P.image fun p => ({c, p} : Finset ι)

/-- The canonical member of `starFamily c P` corresponding to a petal `p ∈ P`. -/
def starEdge (c : ι) (P : Finset ι) (p : ↑P) : Member (starFamily c P) := by
  refine ⟨({c, p.1} : Finset ι), ?_⟩
  refine Finset.mem_image.mpr ?_
  exact ⟨p.1, p.2, rfl⟩

noncomputable def starMemberEquiv
    (c : ι) (P : Finset ι) (hcP : c ∉ P) :
    ↑P ≃ Member (starFamily c P) := by
  classical
  let f : ↑P → Member (starFamily c P) := starEdge c P
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    have hval : ({c, p.1} : Finset ι) = ({c, q.1} : Finset ι) := by
      simpa [f, starEdge] using congrArg (fun A : Member (starFamily c P) => A.1) h
    have hqmem : q.1 ∈ ({c, p.1} : Finset ι) := by
      simp [hval]
    have hqc : q.1 ≠ c := by
      intro hqc
      exact hcP (hqc.symm ▸ q.2)
    rw [Finset.mem_insert, Finset.mem_singleton] at hqmem
    rcases hqmem with hqc' | hqp
    · exact False.elim (hqc hqc')
    · exact hqp.symm
  have hsurj : Function.Surjective f := by
    intro U
    rcases Finset.mem_image.mp U.2 with ⟨p, hp, hpU⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hpU
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

lemma center_mem_starEdge (c : ι) (P : Finset ι) (p : ↑P) :
    c ∈ (starEdge c P p).1 := by
  simp [starEdge]

lemma petal_mem_starEdge (c : ι) (P : Finset ι) (p : ↑P) :
    p.1 ∈ (starEdge c P p).1 := by
  simp [starEdge]

section Stars

variable {cap : ι → ℕ}

/-- A star pair-family is perfectly packable exactly when the center has enough capacity. -/
theorem perfectlyPackable_starFamily_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) :
    PerfectlyPackable (starFamily c P) cap ↔ P.card ≤ cap c := by
  classical
  constructor
  · rintro ⟨assign, hsep⟩
    let f : ↑P → Fin (cap c) := fun p => assign (starEdge c P p) c
    have hf : Function.Injective f := by
      intro p q hEq
      by_contra hpq
      have hneq : starEdge c P p ≠ starEdge c P q := by
        intro h
        apply hpq
        apply Subtype.ext
        have hval : ({c, p.1} : Finset ι) = ({c, q.1} : Finset ι) := by
          simpa [starEdge] using congrArg (fun A : Member (starFamily c P) => A.1) h
        have hqmem : q.1 ∈ ({c, p.1} : Finset ι) := by
          simp [hval]
        have hqc : q.1 ≠ c := by
          intro hqc
          exact hcP (hqc.symm ▸ q.2)
        rw [Finset.mem_insert, Finset.mem_singleton] at hqmem
        rcases hqmem with hqc' | hqp'
        · exact False.elim (hqc hqc')
        · exact hqp'.symm
      rcases hsep (starEdge c P p) (starEdge c P q) hneq with ⟨i, hi, hne⟩
      rcases Finset.mem_inter.mp hi with ⟨hip0, hiq0⟩
      have hip : i ∈ ({c, p.1} : Finset ι) := by
        simpa [starEdge] using hip0
      have hiq : i ∈ ({c, q.1} : Finset ι) := by
        simpa [starEdge] using hiq0
      rw [Finset.mem_insert, Finset.mem_singleton] at hip hiq
      have hic : i = c := by
        rcases hip with rfl | hip'
        · rfl
        · rcases hiq with hiq' | hiq'
          · exact hiq'
          · exfalso
            apply hpq
            exact Subtype.ext (hip'.symm.trans hiq')
      subst i
      apply hne
      simpa [f] using hEq
    have hle : Fintype.card ↑P ≤ cap c := by
      simpa [f] using Fintype.card_le_of_injective f hf
    simpa using hle
  · intro hP
    let e : ↑P ≃ Fin (Fintype.card ↑P) := Fintype.equivFin ↑P
    have hbound : Fintype.card ↑P ≤ cap c := by
      simpa using hP
    let emb : ↑P ↪ Fin (cap c) :=
      { toFun := fun p => ⟨(e p).1, Nat.lt_of_lt_of_le (e p).2 hbound⟩
        inj' := by
          intro p q hpq
          apply e.injective
          apply Fin.ext
          simpa using congrArg Fin.val hpq }
    let sm : ↑P ≃ Member (starFamily c P) := starMemberEquiv c P hcP
    let base : Point cap := fun i => ⟨0, hcap i⟩
    let assign : Member (starFamily c P) → Point cap := fun A i =>
      if h : i = c then by
        cases h
        exact emb (sm.symm A)
      else base i
    refine ⟨assign, ?_⟩
    intro A B hAB
    let p : ↑P := sm.symm A
    let q : ↑P := sm.symm B
    have hpA : sm p = A := by
      simp [p]
    have hqB : sm q = B := by
      simp [q]
    have hpq : p ≠ q := by
      intro hpqeq
      apply hAB
      rw [← hpA, ← hqB, hpqeq]
    have hcp : c ∈ A.1 := by
      rw [← hpA]
      exact center_mem_starEdge c P p
    have hcq : c ∈ B.1 := by
      rw [← hqB]
      exact center_mem_starEdge c P q
    have hAc : assign A c = emb p := by
      simp [assign, p]
    have hBc : assign B c = emb q := by
      simp [assign, q]
    have hcenterNe : assign A c ≠ assign B c := by
      intro hEq
      apply hpq
      apply emb.injective
      calc
        emb p = assign A c := hAc.symm
        _ = assign B c := hEq
        _ = emb q := hBc
    exact ⟨c, Finset.mem_inter.mpr ⟨hcp, hcq⟩, hcenterNe⟩

end Stars

end Erdos278
