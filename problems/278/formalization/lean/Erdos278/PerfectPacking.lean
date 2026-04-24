import Erdos278.BasicDefs

namespace Erdos278

universe u

variable {ι : Type u} [DecidableEq ι]
variable {cap : ι → ℕ}

theorem cylinder_disjoint_iff
    (_hcap : ∀ i, 0 < cap i)
    {S T : Finset ι} {a b : Point cap} :
    Disjoint (Cylinder cap S a) (Cylinder cap T b) ↔ SeparatesOn cap S T a b := by
  constructor
  · intro hdisj
    by_contra hsep
    have hEq : ∀ i, i ∈ S → i ∈ T → a i = b i := by
      intro i hiS hiT
      by_contra hne
      exact hsep ⟨i, Finset.mem_inter.mpr ⟨hiS, hiT⟩, hne⟩
    let x : Point cap := fun i => if hi : i ∈ S then a i else b i
    have hxS : x ∈ Cylinder cap S a := by
      intro i hiS
      simp [x, hiS]
    have hxT : x ∈ Cylinder cap T b := by
      intro i hiT
      by_cases hiS : i ∈ S
      · simpa [x, hiS] using hEq i hiS hiT
      · simp [x, hiS]
    exact (Set.disjoint_left.mp hdisj) hxS hxT
  · intro hsep
    refine Set.disjoint_left.mpr ?_
    intro x hxS hxT
    rcases hsep with ⟨i, hiST, hab⟩
    rcases Finset.mem_inter.mp hiST with ⟨hiS, hiT⟩
    have hxa : x i = a i := hxS i hiS
    have hxb : x i = b i := hxT i hiT
    exact hab (hxa.symm.trans hxb)

theorem perfectlyPackable_iff_pairwiseDisjoint
    (hcap : ∀ i, 0 < cap i)
    {H : SupportFamily ι} :
    PerfectlyPackable H cap ↔
      ∃ assign : Member H → Point cap,
        ∀ A B : Member H,
          A ≠ B → Disjoint (Cylinder cap A.1 (assign A)) (Cylinder cap B.1 (assign B)) := by
  constructor
  · rintro ⟨assign, hsep⟩
    refine ⟨assign, ?_⟩
    intro A B hne
    exact ((cylinder_disjoint_iff (cap := cap) hcap
      (S := A.1) (T := B.1) (a := assign A) (b := assign B))).2 (hsep A B hne)
  · rintro ⟨assign, hdisj⟩
    refine ⟨assign, ?_⟩
    intro A B hne
    exact ((cylinder_disjoint_iff (cap := cap) hcap
      (S := A.1) (T := B.1) (a := assign A) (b := assign B))).1 (hdisj A B hne)

end Erdos278
