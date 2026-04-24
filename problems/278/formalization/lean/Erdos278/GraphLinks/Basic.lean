import Erdos278.StarColoring

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

/-- A graph-link family, expressed in the support-family formalism. -/
abbrev GraphLink (ι : Type u) [DecidableEq ι] := SupportFamily ι

/-- Predicate asserting that a graph-link family is pair-supported. -/
abbrev IsGraphLink (H : GraphLink ι) : Prop := IsPairFamily H

/-- Perfect packability for a graph-link family. -/
abbrev PerfectlyPackableLink (H : GraphLink ι) (cap : ι → ℕ) : Prop :=
  PerfectlyPackable H cap

/-- `k`-color packability for a graph-link family. -/
abbrev ChiPackLinkLe (H : GraphLink ι) (cap : ι → ℕ) (k : ℕ) : Prop :=
  ChiPackLe H cap k

/-- Intersection condition on the graph-link side. -/
abbrev IntersectingLink (H : GraphLink ι) : Prop := IntersectingFamily H

section PairLinks

variable {cap : ι → ℕ}

/-- The pair-support theorem, restated in graph-link language. -/
theorem pairLink_packable_iff
    (hcap : ∀ i, 0 < cap i)
    {H : GraphLink ι}
    (hpair : IsGraphLink H) :
    PerfectlyPackableLink H cap ↔
      IntersectingLink H ∧ ∀ i, degree H i ≤ cap i := by
  simpa [PerfectlyPackableLink, IntersectingLink, IsGraphLink] using
    pairFamily_packable_iff (cap := cap) hcap hpair

/-- The common-core theorem, restated in graph-link language. -/
theorem commonCoreLink_packable_iff_chiPack
    (C : Finset ι) (Lk : GraphLink ι)
    (hdisj : CoreLinkDisjoint C Lk) :
    PerfectlyPackableLink (addCore C Lk) cap ↔
      ChiPackLinkLe Lk cap (Fintype.card (CorePatternType C cap)) := by
  simpa [PerfectlyPackableLink, ChiPackLinkLe] using
    addCore_packable_iff_chiPackLe (cap := cap) C Lk hdisj

end PairLinks

end Erdos278
