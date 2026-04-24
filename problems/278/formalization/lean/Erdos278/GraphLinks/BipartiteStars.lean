import Erdos278.GraphLinks.BipartiteIntersecting

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

/-- The complete bipartite link with singleton right side is the same star family,
up to the symmetry of unordered pairs. -/
lemma completeBipartiteLink_singleton_right_eq_starLink
    (L : Finset ι) (c : ι) :
    completeBipartiteLink L ({c} : Finset ι) = starLink c L := by
  ext S
  constructor
  · intro hS
    rcases (mem_completeBipartiteLink_iff).1 hS with ⟨l, hl, r, hr, hSr⟩
    have hrc : r = c := by
      simpa using hr
    subst hrc
    refine Finset.mem_image.mpr ?_
    refine ⟨l, hl, ?_⟩
    simpa [Finset.pair_comm] using hSr.symm
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨l, hl, hSl⟩
    refine (mem_completeBipartiteLink_iff).2 ?_
    refine ⟨l, hl, c, by simp, ?_⟩
    simpa [Finset.pair_comm] using hSl.symm

section BipartiteStars

variable {cap : ι → ℕ}

/-- Exact perfect-packability criterion for a singleton-right complete bipartite link. -/
theorem perfectlyPackable_completeBipartiteLink_singleton_right_iff
    (hcap : ∀ i, 0 < cap i)
    {L : Finset ι} {c : ι}
    (hcL : c ∉ L) :
    PerfectlyPackableLink (completeBipartiteLink L ({c} : Finset ι)) cap ↔
      L.card ≤ cap c := by
  rw [completeBipartiteLink_singleton_right_eq_starLink]
  exact perfectlyPackable_starLink_iff (cap := cap) hcap hcL

/-- Exact `k`-color criterion for a singleton-right complete bipartite link. -/
theorem chiPackLe_completeBipartiteLink_singleton_right_iff
    (hcap : ∀ i, 0 < cap i)
    {L : Finset ι} {c : ι}
    (hcL : c ∉ L) (k : ℕ) :
    ChiPackLinkLe (completeBipartiteLink L ({c} : Finset ι)) cap k ↔
      L.card ≤ k * cap c := by
  rw [completeBipartiteLink_singleton_right_eq_starLink]
  exact chiPackLe_starLink_iff (cap := cap) hcap hcL k

/-- Any nonempty pairwise-intersecting subfamily of a complete bipartite link is contained
in either a left star or a right star. -/
theorem intersectingFamily_completeBipartite_subfamily_subset_star
    {L R : Finset ι} (hLR : Disjoint L R)
    {H : SupportFamily ι}
    (hsub : H ⊆ completeBipartiteLink L R)
    (hint : IntersectingFamily H)
    (hne : H.Nonempty) :
    (∃ l, l ∈ L ∧ H ⊆ starLink l R) ∨
      (∃ r, r ∈ R ∧ H ⊆ starLink r L) := by
  rcases
      intersectingFamily_completeBipartite_common_vertex hLR hsub hint hne
    with hL | hR
  · rcases hL with ⟨l, hlL, hall⟩
    refine Or.inl ⟨l, hlL, ?_⟩
    intro S hS
    have hlS : l ∈ S := hall S hS
    rcases (mem_completeBipartiteLink_iff).1 (hsub hS) with ⟨l', hl', r, hr, hpair⟩
    have hll' : l = l' := by
      have hmem : l ∈ ({l', r} : Finset ι) := by
        rw [hpair] at hlS
        exact hlS
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact h
      · have hrL : r ∈ L := by
          rw [h] at hlL
          exact hlL
        exact False.elim ((Finset.disjoint_left.mp hLR) hrL hr)
    refine Finset.mem_image.mpr ?_
    refine ⟨r, hr, ?_⟩
    simpa [hll'] using hpair.symm
  · rcases hR with ⟨r, hrR, hall⟩
    refine Or.inr ⟨r, hrR, ?_⟩
    intro S hS
    have hrS : r ∈ S := hall S hS
    rcases (mem_completeBipartiteLink_iff).1 (hsub hS) with ⟨l, hl, r', hr', hpair⟩
    have hrr' : r = r' := by
      have hmem : r ∈ ({l, r'} : Finset ι) := by
        rw [hpair] at hrS
        exact hrS
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · have hlR : l ∈ R := by
          rw [h] at hrR
          exact hrR
        exact False.elim ((Finset.disjoint_left.mp hLR) hl hlR)
      · exact h
    refine Finset.mem_image.mpr ?_
    refine ⟨l, hl, ?_⟩
    simpa [hrr', Finset.pair_comm] using hpair.symm

end BipartiteStars

end Erdos278
