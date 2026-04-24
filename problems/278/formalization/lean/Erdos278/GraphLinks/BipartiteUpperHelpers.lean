import Erdos278.GraphLinks.Chi

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section UpperHelpers

variable {cap : ι → ℕ} {G : GraphLink ι}

theorem chiPackLe_of_fintypeColoring
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (hcard : Fintype.card κ = k)
    (color : Member G → κ)
    (hpack : ∀ t : κ, PerfectlyPackable (colorClass G color t) cap) :
    ChiPackLinkLe G cap k := by
  classical
  let e : κ ≃ Fin k := by
    simpa [hcard] using (Fintype.equivFin κ)
  refine ⟨fun A => e (color A), ?_⟩
  intro t
  have hclass :
      colorClass G (fun A => e (color A)) t =
        colorClass G color (e.symm t) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
      rcases Finset.mem_filter.mp hA with ⟨hAatt, hAt⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨A, Finset.mem_filter.mpr ⟨hAatt, ?_⟩, hAS⟩
      simpa using congrArg e.symm hAt
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
      rcases Finset.mem_filter.mp hA with ⟨hAatt, hAt⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨A, Finset.mem_filter.mpr ⟨hAatt, ?_⟩, hAS⟩
      simpa using congrArg e hAt
  simpa [hclass] using hpack (e.symm t)

abbrev RightRemainderColor (a q s : ℕ) : Type :=
  (Fin a × Fin q) ⊕ Fin s

abbrev LeftRemainderColor (a q : ℕ) : Type :=
  Fin a × Fin (q + 1)

lemma card_rightRemainderColor (a q s : ℕ) :
    Fintype.card (RightRemainderColor a q s) = a * q + s := by
  simp [RightRemainderColor]

lemma card_leftRemainderColor (a q : ℕ) :
    Fintype.card (LeftRemainderColor a q) = a * q + a := by
  simp [LeftRemainderColor, Nat.mul_add]

end UpperHelpers

end Erdos278
