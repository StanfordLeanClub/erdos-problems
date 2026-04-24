import Erdos278.GraphLinks.BipartiteBasic

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section BipartiteIntersecting

lemma pair_pair_disjoint_of_cross
    {L R : Finset ι} (hLR : Disjoint L R)
    {l0 l1 : ι} {r0 r1 : ι}
    (hl0 : l0 ∈ L) (hl1 : l1 ∈ L) (hr0 : r0 ∈ R) (hr1 : r1 ∈ R)
    (hl : l1 ≠ l0) (hr : r1 ≠ r0) :
    Disjoint ({l1, r0} : Finset ι) ({l0, r1} : Finset ι) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx1 hx2
  rw [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with hxl1 | hxr0 <;> rcases hx2 with hxl0 | hxr1
  · exact hl (hxl1.symm.trans hxl0)
  · have hl1R : l1 ∈ R := by
      have hEq : l1 = r1 := hxl1.symm.trans hxr1
      simpa [hEq] using hr1
    exact (Finset.disjoint_left.mp hLR) hl1 hl1R
  · have hr0L : r0 ∈ L := by
      have hEq : r0 = l0 := hxr0.symm.trans hxl0
      simpa [hEq] using hl0
    exact (Finset.disjoint_left.mp hLR) hr0L hr0
  · exact hr (hxr1.symm.trans hxr0)

/-- A nonempty pairwise-intersecting subfamily of a complete bipartite link
has a common endpoint on one side or the other. -/
theorem intersectingFamily_completeBipartite_common_vertex
    {L R : Finset ι} (hLR : Disjoint L R)
    {H : SupportFamily ι}
    (hsub : H ⊆ completeBipartiteLink L R)
    (hint : IntersectingFamily H)
    (hne : H.Nonempty) :
    (∃ l, l ∈ L ∧ ∀ S ∈ H, l ∈ S) ∨
      (∃ r, r ∈ R ∧ ∀ S ∈ H, r ∈ S) := by
  classical
  rcases hne with ⟨S0, hS0⟩
  let A0 : Member H := ⟨S0, hS0⟩
  rcases (mem_completeBipartiteLink_iff).1 (hsub hS0) with ⟨l0, hl0, r0, hr0, hA0⟩
  by_cases hall : ∀ S ∈ H, l0 ∈ S
  · exact Or.inl ⟨l0, hl0, hall⟩
  · have hall' : ∃ S, S ∈ H ∧ l0 ∉ S := by
      by_contra h
      apply hall
      intro S hS
      by_contra hl0S
      exact h ⟨S, hS, hl0S⟩
    rcases hall' with ⟨Sb, hSb, hl0Sb⟩
    let B : Member H := ⟨Sb, hSb⟩
    have hl0A0 : l0 ∈ A0.1 := by
      simp [A0, hA0]
    have hA0B : A0 ≠ B := by
      intro h
      have : l0 ∈ B.1 := by simpa [h] using hl0A0
      exact hl0Sb this
    have hr0B : r0 ∈ B.1 := by
      rcases hint A0 B hA0B with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxA0, hxB⟩
      have hxSeed : x ∈ ({l0, r0} : Finset ι) := by
        simpa [A0, hA0] using hxA0
      rw [Finset.mem_insert, Finset.mem_singleton] at hxSeed
      rcases hxSeed with hxl0 | hxr0
      · exact False.elim (hl0Sb (by simpa [hxl0, B] using hxB))
      · simpa [hxr0, B] using hxB
    refine Or.inr ⟨r0, hr0, ?_⟩
    intro S hS
    by_contra hr0S
    let C : Member H := ⟨S, hS⟩
    have hr0A0 : r0 ∈ A0.1 := by simp [A0, hA0]
    have hA0C : A0 ≠ C := by
      intro h
      have : r0 ∈ C.1 := by simpa [h] using hr0A0
      exact hr0S this
    have hl0S : l0 ∈ S := by
      rcases hint A0 C hA0C with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxA0, hxC⟩
      have hxSeed : x ∈ ({l0, r0} : Finset ι) := by
        simpa [A0, hA0] using hxA0
      rw [Finset.mem_insert, Finset.mem_singleton] at hxSeed
      rcases hxSeed with hxl0 | hxr0
      · simpa [hxl0] using hxC
      · exact False.elim (hr0S (by simpa [hxr0] using hxC))
    have hBC : B ≠ C := by
      intro h
      have : r0 ∈ C.1 := by simpa [h] using hr0B
      exact hr0S this
    rcases (mem_completeBipartiteLink_iff).1 (hsub hSb) with ⟨lb, hlb, rb, hrb, hBpair⟩
    rcases (mem_completeBipartiteLink_iff).1 (hsub hS) with ⟨lc, hlc, rc, hrc, hCpair⟩
    have hlb_ne_l0 : lb ≠ l0 := by
      intro h
      apply hl0Sb
      have : l0 ∈ ({lb, rb} : Finset ι) := by
        rw [h]
        exact Finset.mem_insert_self _ _
      simpa [B, hBpair] using this
    have hrc_ne_r0 : rc ≠ r0 := by
      intro h
      apply hr0S
      have : r0 ∈ ({lc, rc} : Finset ι) := by
        rw [h]
        exact Finset.mem_singleton_self _ |> Or.inr |> Finset.mem_insert.mpr
      simpa [C, hCpair] using this
    have hrb_eq_r0 : rb = r0 := by
      have : r0 ∈ ({lb, rb} : Finset ι) := by simpa [B, hBpair] using hr0B
      rw [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with hr0lb | hr0rb
      · have hlbR : lb ∈ R := by simpa [hr0lb] using hr0
        exact False.elim ((Finset.disjoint_left.mp hLR) hlb hlbR)
      · exact hr0rb.symm
    have hlc_eq_l0 : lc = l0 := by
      have : l0 ∈ ({lc, rc} : Finset ι) := by simpa [hCpair] using hl0S
      rw [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with hl0lc | hl0rc
      · exact hl0lc.symm
      · have hrcL : rc ∈ L := by simpa [hl0rc] using hl0
        exact False.elim ((Finset.disjoint_left.mp hLR) hrcL hrc)
    have hBsupport : B.1 = ({lb, r0} : Finset ι) := by
      simp [B, hBpair, hrb_eq_r0]
    have hCsupport : C.1 = ({l0, rc} : Finset ι) := by
      simp [C, hCpair, hlc_eq_l0]
    have hdisjBC : Disjoint B.1 C.1 := by
      rw [hBsupport, hCsupport]
      exact pair_pair_disjoint_of_cross hLR hl0 hlb hr0 hrc hlb_ne_l0 hrc_ne_r0
    have hnot : ¬ (B.1 ∩ C.1).Nonempty := by
      intro hneBC
      rcases hneBC with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxB, hxC⟩
      exact (Finset.disjoint_left.mp hdisjBC) hxB hxC
    exact hnot (hint B C hBC)

end BipartiteIntersecting

end Erdos278
