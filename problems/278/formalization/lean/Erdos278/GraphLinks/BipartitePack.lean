import Erdos278.GraphLinks.BipartiteStars

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section BipartitePack

variable {cap : ι → ℕ}

lemma colorClass_subset_completeBipartite
    {L R : Finset ι}
    {κ : Type*} [DecidableEq κ]
    (color : Member (completeBipartiteLink L R) → κ) (t : κ) :
    colorClass (completeBipartiteLink L R) color t ⊆ completeBipartiteLink L R := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
  rcases Finset.mem_filter.mp hA with ⟨_, _⟩
  simpa [hAS] using A.2

lemma isGraphLink_colorClass_completeBipartite
    {L R : Finset ι}
    (hLR : Disjoint L R)
    {κ : Type*} [DecidableEq κ]
    (color : Member (completeBipartiteLink L R) → κ) (t : κ) :
    IsGraphLink (colorClass (completeBipartiteLink L R) color t) := by
  intro S hS
  exact
    isGraphLink_completeBipartiteLink (L := L) (R := R) hLR S
      ((colorClass_subset_completeBipartite (L := L) (R := R) color t) hS)

theorem perfectlyPackable_colorClass_intersecting_completeBipartite
    (hcap : ∀ i, 0 < cap i)
    {L R : Finset ι}
    (hLR : Disjoint L R)
    {κ : Type*} [DecidableEq κ]
    (color : Member (completeBipartiteLink L R) → κ) (t : κ)
    (hpack : PerfectlyPackable (colorClass (completeBipartiteLink L R) color t) cap) :
    IntersectingFamily (colorClass (completeBipartiteLink L R) color t) := by
  have hpair :
      IsPairFamily (colorClass (completeBipartiteLink L R) color t) :=
    isGraphLink_colorClass_completeBipartite (L := L) (R := R) hLR color t
  exact
    ((pairFamily_packable_iff
        (cap := cap)
        (H := colorClass (completeBipartiteLink L R) color t)
        hcap hpair).1 hpack).1

/-- In a complete bipartite link, every packable color class is either empty or contained in a
left star or a right star. This is the structural engine behind the exact bipartite packability
formula. -/
theorem colorClass_completeBipartite_star_or_empty
    (hcap : ∀ i, 0 < cap i)
    {L R : Finset ι}
    (hLR : Disjoint L R)
    {κ : Type*} [DecidableEq κ]
    (color : Member (completeBipartiteLink L R) → κ) (t : κ)
    (hpack : PerfectlyPackable (colorClass (completeBipartiteLink L R) color t) cap) :
    colorClass (completeBipartiteLink L R) color t = ∅ ∨
      (∃ l, l ∈ L ∧ colorClass (completeBipartiteLink L R) color t ⊆ starLink l R) ∨
      (∃ r, r ∈ R ∧ colorClass (completeBipartiteLink L R) color t ⊆ starLink r L) := by
  by_cases h0 : colorClass (completeBipartiteLink L R) color t = ∅
  · exact Or.inl h0
  · have hne : (colorClass (completeBipartiteLink L R) color t).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr h0
    have hint' :
        IntersectingFamily (colorClass (completeBipartiteLink L R) color t) :=
      perfectlyPackable_colorClass_intersecting_completeBipartite
        (cap := cap) hcap (L := L) (R := R) hLR color t hpack
    rcases
        intersectingFamily_completeBipartite_subfamily_subset_star
          (L := L) (R := R) hLR
          (H := colorClass (completeBipartiteLink L R) color t)
          (hsub := colorClass_subset_completeBipartite (L := L) (R := R) color t)
          hint' hne
      with hL | hR
    · exact Or.inr (Or.inl hL)
    · exact Or.inr (Or.inr hR)

/-- A `k`-color packing of a complete bipartite link may be chosen so that each color class is
empty or contained in a single left star or a single right star. -/
theorem chiPackLe_completeBipartite_star_or_empty_classes
    (hcap : ∀ i, 0 < cap i)
    {L R : Finset ι}
    (hLR : Disjoint L R)
    {k : ℕ}
    (hchi : ChiPackLinkLe (completeBipartiteLink L R) cap k) :
    ∃ color : Member (completeBipartiteLink L R) → Fin k,
      ∀ t : Fin k,
        colorClass (completeBipartiteLink L R) color t = ∅ ∨
          (∃ l, l ∈ L ∧ colorClass (completeBipartiteLink L R) color t ⊆ starLink l R) ∨
          (∃ r, r ∈ R ∧ colorClass (completeBipartiteLink L R) color t ⊆ starLink r L) := by
  rcases hchi with ⟨color, hpack⟩
  refine ⟨color, ?_⟩
  intro t
  exact colorClass_completeBipartite_star_or_empty
    (cap := cap) hcap (L := L) (R := R) hLR color t (hpack t)

end BipartitePack

end Erdos278
