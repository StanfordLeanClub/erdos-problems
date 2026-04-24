import Erdos278.GraphLinks.Basic
import Mathlib.Data.Finset.Card

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

/-- The graph-link star with center `c` and petal set `P`. -/
abbrev starLink (c : ι) (P : Finset ι) : GraphLink ι := starFamily c P

lemma isGraphLink_starLink
    {c : ι} {P : Finset ι} (hcP : c ∉ P) :
    IsGraphLink (starLink c P) := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨p, hpP, rfl⟩
  have hpc : p ≠ c := by
    intro hpc
    exact hcP (hpc ▸ hpP)
  have hcp : c ≠ p := by
    intro hcp
    exact hpc hcp.symm
  change ({c, p} : Finset ι).card = 2
  simpa using (Finset.card_pair hcp)

section Stars

variable {cap : ι → ℕ}

/-- Exact perfect-packability criterion for a graph-link star. -/
theorem perfectlyPackable_starLink_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) :
    PerfectlyPackableLink (starLink c P) cap ↔ P.card ≤ cap c := by
  exact perfectlyPackable_starFamily_iff (cap := cap) hcap hcP

/-- Exact `k`-color criterion for a graph-link star. -/
theorem chiPackLe_starLink_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) (k : ℕ) :
    ChiPackLinkLe (starLink c P) cap k ↔ P.card ≤ k * cap c := by
  exact chiPackLe_starFamily_iff (cap := cap) hcap hcP k

end Stars

end Erdos278
