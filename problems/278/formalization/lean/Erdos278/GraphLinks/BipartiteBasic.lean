import Erdos278.GraphLinks.Chi
import Mathlib.Data.Finset.Card

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

/-- The complete bipartite graph-link with left side `L` and right side `R`. -/
def completeBipartiteLink (L R : Finset ι) : GraphLink ι :=
  (L.product R).image fun e => ({e.1, e.2} : Finset ι)

lemma mem_completeBipartiteLink_iff
    {L R : Finset ι} {S : Finset ι} :
    S ∈ completeBipartiteLink L R ↔
      ∃ l ∈ L, ∃ r ∈ R, S = ({l, r} : Finset ι) := by
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨e, he, rfl⟩
    rcases Finset.mem_product.mp he with ⟨hl, hr⟩
    exact ⟨e.1, hl, e.2, hr, rfl⟩
  · rintro ⟨l, hl, r, hr, rfl⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨(l, r), Finset.mem_product.mpr ⟨hl, hr⟩, rfl⟩

lemma completeBipartiteLink_singleton_left
    (c : ι) (P : Finset ι) :
    completeBipartiteLink ({c} : Finset ι) P = starLink c P := by
  ext S
  constructor
  · intro hS
    rcases (mem_completeBipartiteLink_iff).1 hS with ⟨l, hl, r, hr, hSr⟩
    have hlc : l = c := by simpa using hl
    subst hlc
    refine Finset.mem_image.mpr ?_
    exact ⟨r, hr, hSr.symm⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨p, hp, rfl⟩
    exact (mem_completeBipartiteLink_iff).2 ⟨c, by simp, p, hp, rfl⟩

lemma completeBipartiteLink_singleton_right
    (L : Finset ι) (c : ι) :
    completeBipartiteLink L ({c} : Finset ι) = L.image (fun l => ({l, c} : Finset ι)) := by
  ext S
  constructor
  · intro hS
    rcases (mem_completeBipartiteLink_iff).1 hS with ⟨l, hl, r, hr, hSr⟩
    have hrc : r = c := by simpa using hr
    subst hrc
    refine Finset.mem_image.mpr ?_
    exact ⟨l, hl, hSr.symm⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨l, hl, rfl⟩
    exact (mem_completeBipartiteLink_iff).2 ⟨l, hl, c, by simp, rfl⟩

lemma isGraphLink_completeBipartiteLink
    {L R : Finset ι} (hdisj : Disjoint L R) :
    IsGraphLink (completeBipartiteLink L R) := by
  intro S hS
  rcases (mem_completeBipartiteLink_iff).1 hS with ⟨l, hl, r, hr, rfl⟩
  have hlr : l ≠ r := by
    intro hlr
    exact (Finset.disjoint_left.mp hdisj) hl (hlr ▸ hr)
  change ({l, r} : Finset ι).card = 2
  simpa using Finset.card_pair hlr

section BipartiteBasic

variable {cap : ι → ℕ}

/-- The graph-link star theorem recovered as a singleton-left bipartite corollary. -/
theorem perfectlyPackable_completeBipartiteLink_singleton_left_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) :
    PerfectlyPackableLink (completeBipartiteLink ({c} : Finset ι) P) cap ↔
      P.card ≤ cap c := by
  rw [completeBipartiteLink_singleton_left]
  exact perfectlyPackable_starLink_iff (cap := cap) hcap hcP

/-- The exact `k`-color graph-link star theorem recovered as a
    singleton-left bipartite corollary. -/
theorem chiPackLe_completeBipartiteLink_singleton_left_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) (k : ℕ) :
    ChiPackLinkLe (completeBipartiteLink ({c} : Finset ι) P) cap k ↔
      P.card ≤ k * cap c := by
  rw [completeBipartiteLink_singleton_left]
  exact chiPackLe_starLink_iff (cap := cap) hcap hcP k

end BipartiteBasic

end Erdos278
