import Erdos278.GraphLinks.Chi

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section ChiStars

variable {cap : ι → ℕ}

omit [DecidableEq ι] in
lemma starCard_le_mul_self
    (hcap : ∀ i : ι, 0 < cap i)
    {c : ι} {P : Finset ι} :
    ∃ k : ℕ, P.card ≤ k * cap c := by
  refine ⟨P.card, ?_⟩
  have hc : 0 < cap c := hcap c
  calc
    P.card ≤ P.card * cap c := by
     simpa [Nat.one_mul] using Nat.le_mul_of_pos_right (P.card) hc
    _ = P.card * cap c := rfl

theorem chiPackLink_starLink_eq_find
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) :
    chiPackLink (starLink c P) cap hcap =
      Nat.find (starCard_le_mul_self (cap := cap) hcap (c := c) (P := P)) := by
  apply le_antisymm
  · exact
      (chiPackLink_starLink_le_iff
          (cap := cap) hcap hcP
          (Nat.find (starCard_le_mul_self (cap := cap) hcap (c := c) (P := P)))).2
        (Nat.find_spec (starCard_le_mul_self (cap := cap) hcap (c := c) (P := P)))
  · have hcard :
        P.card ≤ chiPackLink (starLink c P) cap hcap * cap c := by
      exact
        (chiPackLink_starLink_le_iff
            (cap := cap) hcap hcP
            (chiPackLink (starLink c P) cap hcap)).mp
          le_rfl
    exact Nat.find_min'
      (starCard_le_mul_self (cap := cap) hcap (c := c) (P := P))
      hcard

end ChiStars

end Erdos278
