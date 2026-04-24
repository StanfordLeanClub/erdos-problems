import Erdos278.GraphLinks.Stars
import Mathlib.Data.Fintype.EquivFin

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section Chi

variable {cap : ι → ℕ}

lemma perfectlyPackable_singleton
    (hcap : ∀ i, 0 < cap i) (S : Finset ι) :
    PerfectlyPackable ({S} : SupportFamily ι) cap := by
  let a : Point cap := fun i => ⟨0, hcap i⟩
  refine ⟨fun _ => a, ?_⟩
  intro A B hne
  exfalso
  apply hne
  apply Subtype.ext
  have hA : A.1 = S := Finset.mem_singleton.mp A.2
  have hB : B.1 = S := Finset.mem_singleton.mp B.2
  exact hA.trans hB.symm

lemma chiPackLinkLe_exists
    (G : GraphLink ι) (hcap : ∀ i, 0 < cap i) :
    ∃ k, ChiPackLinkLe G cap k := by
  classical
  let e : Member G ≃ Fin (Fintype.card (Member G)) := Fintype.equivFin (Member G)
  let color : Member G → Fin (Fintype.card (Member G)) := e
  refine ⟨Fintype.card (Member G), color, ?_⟩
  intro t
  let A : Member G := e.symm t
  have hclass : colorClass G color t = ({A.1} : SupportFamily ι) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨B, hB, hBS⟩
      rcases Finset.mem_filter.mp hB with ⟨_hBatt, hBt⟩
      have hBeq : B = A := by
        apply e.injective
        simpa [color, A] using hBt
      have hBA : B.1 = A.1 := congrArg Subtype.val hBeq
      exact Finset.mem_singleton.mpr (hBS.symm.trans hBA)
    · intro hS
      have hA : S = A.1 := Finset.mem_singleton.mp hS
      refine Finset.mem_image.mpr ?_
      refine ⟨A, ?_, hA.symm⟩
      exact Finset.mem_filter.mpr ⟨by simp, by simp [color, A]⟩
  simpa [hclass] using perfectlyPackable_singleton (cap := cap) hcap A.1

/-- The abstract graph-link cost invariant: the least number of packable colors. -/
noncomputable def chiPackLink
    (G : GraphLink ι) (cap : ι → ℕ) (hcap : ∀ i, 0 < cap i) : ℕ := by
  classical
  exact Nat.find (chiPackLinkLe_exists (G := G) (cap := cap) hcap)

theorem chiPackLink_spec
    (G : GraphLink ι) (hcap : ∀ i, 0 < cap i) :
    ChiPackLinkLe G cap (chiPackLink G cap hcap) := by
  classical
  exact Nat.find_spec (chiPackLinkLe_exists (G := G) (cap := cap) hcap)

theorem chiPackLink_le_of
    (G : GraphLink ι) (hcap : ∀ i, 0 < cap i) {k : ℕ}
    (hk : ChiPackLinkLe G cap k) :
    chiPackLink G cap hcap ≤ k := by
  classical
  exact Nat.find_min' (chiPackLinkLe_exists (G := G) (cap := cap) hcap) hk

theorem chiPackLink_starLink_le_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) (k : ℕ) :
    chiPackLink (starLink c P) cap hcap ≤ k ↔ P.card ≤ k * cap c := by
  constructor
  · intro hk
    have hchi :
        ChiPackLinkLe (starLink c P) cap
          (chiPackLink (starLink c P) cap hcap) :=
      chiPackLink_spec (G := starLink c P) (cap := cap) hcap
    have hcard :
        P.card ≤ chiPackLink (starLink c P) cap hcap * cap c := by
      exact
        (chiPackLe_starLink_iff (cap := cap) hcap hcP
          (chiPackLink (starLink c P) cap hcap)).mp hchi
    exact le_trans hcard (Nat.mul_le_mul_right (cap c) hk)
  · intro hcard
    apply chiPackLink_le_of (G := starLink c P) (cap := cap) hcap
    exact (chiPackLe_starLink_iff (cap := cap) hcap hcP k).2 hcard

end Chi

end Erdos278
