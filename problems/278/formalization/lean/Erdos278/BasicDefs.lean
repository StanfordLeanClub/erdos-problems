import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Finset

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

abbrev Point (cap : ι → ℕ) := ∀ i, Fin (cap i)

abbrev SupportFamily (ι : Type u) [DecidableEq ι] := Finset (Finset ι)

abbrev Member (H : SupportFamily ι) := {S : Finset ι // S ∈ H}

def Cylinder (cap : ι → ℕ) (S : Finset ι) (a : Point cap) : Set (Point cap) :=
  {x | ∀ i ∈ S, x i = a i}

def SeparatesOn (cap : ι → ℕ) (S T : Finset ι) (a b : Point cap) : Prop :=
  ∃ i, i ∈ S ∩ T ∧ a i ≠ b i

def PerfectlyPackable (H : SupportFamily ι) (cap : ι → ℕ) : Prop :=
  ∃ assign : Member H → Point cap,
    ∀ A B : Member H, A ≠ B → SeparatesOn cap A.1 B.1 (assign A) (assign B)

def degree (H : SupportFamily ι) (i : ι) : ℕ :=
  (H.filter fun S => i ∈ S).card

def IsPairFamily (H : SupportFamily ι) : Prop :=
  ∀ S ∈ H, S.card = 2

def IntersectingFamily (H : SupportFamily ι) : Prop :=
  ∀ A B : Member H, A ≠ B → (A.1 ∩ B.1).Nonempty

def addCore (C : Finset ι) (Lk : SupportFamily ι) : SupportFamily ι :=
  Lk.image fun L => C ∪ L

def CoreLinkDisjoint (C : Finset ι) (Lk : SupportFamily ι) : Prop :=
  ∀ L ∈ Lk, Disjoint C L

abbrev CorePatternType (C : Finset ι) (cap : ι → ℕ) :=
  ∀ i : {j // j ∈ C}, Fin (cap i.1)

section ColorClasses

variable {κ : Type*} [DecidableEq κ]

def colorClass (Lk : SupportFamily ι) (color : Member Lk → κ) (t : κ) : SupportFamily ι :=
  ((Lk.attach).filter fun A => color A = t).image fun A => A.1

def PackColorable (Lk : SupportFamily ι) (cap : ι → ℕ) (κ : Type*) [DecidableEq κ] : Prop :=
  ∃ color : Member Lk → κ, ∀ t : κ, PerfectlyPackable (colorClass Lk color t) cap

def ChiPackLe (Lk : SupportFamily ι) (cap : ι → ℕ) (k : ℕ) : Prop :=
  ∃ color : Member Lk → Fin k,
    ∀ t : Fin k, PerfectlyPackable (colorClass Lk color t) cap

noncomputable def colorClassMemberEquiv
    (Lk : SupportFamily ι) (color : Member Lk → κ) (t : κ) :
    {A : Member Lk // color A = t} ≃ Member (colorClass Lk color t) := by
  classical
  let f : {A : Member Lk // color A = t} → Member (colorClass Lk color t) := fun A =>
    ⟨A.1.1, by
      refine Finset.mem_image.mpr ?_
      refine ⟨A.1, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨by simp, A.2⟩⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg (fun U : Member (colorClass Lk color t) => U.1) h
  have hsurj : Function.Surjective f := by
    intro U
    rcases Finset.mem_image.mp U.2 with ⟨A, hA, hAU⟩
    refine ⟨⟨A, (Finset.mem_filter.mp hA).2⟩, ?_⟩
    apply Subtype.ext
    exact hAU
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

lemma colorClass_relabel {κ' : Type*} [DecidableEq κ']
    (Lk : SupportFamily ι) (color : Member Lk → κ) (e : κ ≃ κ') (t : κ') :
    colorClass Lk (fun A => e (color A)) t = colorClass Lk color (e.symm t) := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨A, hA, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨A, ?_, rfl⟩
    rcases Finset.mem_filter.mp hA with ⟨_, hAt⟩
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    apply e.injective
    simpa using hAt
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨A, hA, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨A, ?_, rfl⟩
    rcases Finset.mem_filter.mp hA with ⟨_, hAt⟩
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    simpa using congrArg e hAt

end ColorClasses

end Erdos278
