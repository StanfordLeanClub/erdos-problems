import Erdos278.Stars

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section StarColoring

variable {cap : ι → ℕ}

lemma starEdge_injective
    {c : ι} {P : Finset ι} (hcP : c ∉ P) :
    Function.Injective (starEdge c P) := by
  intro p q h
  apply Subtype.ext
  have hval : ({c, p.1} : Finset ι) = ({c, q.1} : Finset ι) := by
    simpa [starEdge] using congrArg (fun A : Member (starFamily c P) => A.1) h
  have hqmem : q.1 ∈ ({c, p.1} : Finset ι) := by
    simp [hval]
  have hqc : q.1 ≠ c := by
    intro hqc
    exact hcP (hqc.symm ▸ q.2)
  rw [Finset.mem_insert, Finset.mem_singleton] at hqmem
  rcases hqmem with hqc' | hqp
  · exact False.elim (hqc hqc')
  · exact hqp.symm

lemma nat_eq_of_div_eq_of_mod_eq {x y d : ℕ}
    (hdiv : x / d = y / d) (hmod : x % d = y % d) : x = y := by
  calc
    x = d * (x / d) + x % d := by symm; exact Nat.div_add_mod x d
    _ = d * (y / d) + y % d := by rw [hdiv, hmod]
    _ = y := Nat.div_add_mod y d

/-- A member of the color class at its own color. -/
def colorSelfMember
    {κ : Type*} [DecidableEq κ]
    (Lk : SupportFamily ι) (color : Member Lk → κ) (A : Member Lk) :
    Member (colorClass Lk color (color A)) := by
  refine ⟨A.1, ?_⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨A, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨by simp, rfl⟩

lemma separatesOn_star_edges_center_ne
    {c : ι} {P : Finset ι} {p q : ↑P} {a b : Point cap}
    (hne : a c ≠ b c) :
    SeparatesOn cap (starEdge c P p).1 (starEdge c P q).1 a b := by
  refine ⟨c, Finset.mem_inter.mpr ?_, hne⟩
  exact ⟨center_mem_starEdge c P p, center_mem_starEdge c P q⟩

lemma separatesOn_star_edges_imp_center_ne
    {c : ι} {P : Finset ι} (hcP : c ∉ P)
    {p q : ↑P} (hpq : p ≠ q) {a b : Point cap}
    (hsep : SeparatesOn cap (starEdge c P p).1 (starEdge c P q).1 a b) :
    a c ≠ b c := by
  rcases hsep with ⟨i, hi, hne⟩
  rcases Finset.mem_inter.mp hi with ⟨hip0, hiq0⟩
  have hip : i ∈ ({c, p.1} : Finset ι) := by
    simpa [starEdge] using hip0
  have hiq : i ∈ ({c, q.1} : Finset ι) := by
    simpa [starEdge] using hiq0
  rw [Finset.mem_insert, Finset.mem_singleton] at hip hiq
  have hic : i = c := by
    rcases hip with rfl | hip'
    · rfl
    · rcases hiq with hiq' | hiq'
      · exact hiq'
      · exfalso
        apply hpq
        exact Subtype.ext (hip'.symm.trans hiq')
  subst i
  exact hne

/-- Exact `k`-color packability criterion for a star family. -/
theorem chiPackLe_starFamily_iff
    (hcap : ∀ i, 0 < cap i)
    {c : ι} {P : Finset ι}
    (hcP : c ∉ P) (k : ℕ) :
    ChiPackLe (starFamily c P) cap k ↔ P.card ≤ k * cap c := by
  classical
  constructor
  · intro hchi
    rcases hchi with ⟨color, hpack⟩
    let assignColor : ∀ t : Fin k, Member (colorClass (starFamily c P) color t) → Point cap :=
      fun t => Classical.choose (hpack t)
    have hsepColor :
        ∀ t : Fin k,
          ∀ U V : Member (colorClass (starFamily c P) color t),
            U ≠ V → SeparatesOn cap U.1 V.1 (assignColor t U) (assignColor t V) := by
      intro t
      exact Classical.choose_spec (hpack t)
    have hassignColor_transport :
        ∀ {A : Member (starFamily c P)} {s t : Fin k}
          (hs : color A = s) (ht : color A = t) (h : s = t),
          assignColor s ((colorClassMemberEquiv (starFamily c P) color s) ⟨A, hs⟩) c =
            assignColor t ((colorClassMemberEquiv (starFamily c P) color t) ⟨A, ht⟩) c := by
      intro A s t hs ht h
      cases h
      have hsub : (⟨A, hs⟩ : {A : Member (starFamily c P) // color A = s}) = ⟨A, ht⟩ := by
        apply Subtype.ext
        rfl
      exact congrArg (fun W => assignColor s W c)
        (congrArg (colorClassMemberEquiv (starFamily c P) color s) hsub)
    let f : ↑P → Fin k × Fin (cap c) := fun p =>
      let A := starEdge c P p
      let U := colorSelfMember (starFamily c P) color A
      (color A, assignColor (color A) U c)
    have hf : Function.Injective f := by
      intro p q hEq
      by_contra hpq
      let Ap : Member (starFamily c P) := starEdge c P p
      let Aq : Member (starFamily c P) := starEdge c P q
      have hfst : color Ap = color Aq := by
        simpa [f, Ap, Aq] using congrArg Prod.fst hEq
      have hsndRaw :
          assignColor (color Ap) (colorSelfMember (starFamily c P) color Ap) c =
            assignColor (color Aq) (colorSelfMember (starFamily c P) color Aq) c := by
        simpa [f, Ap, Aq] using congrArg Prod.snd hEq
      let t : Fin k := color Aq
      let U : Member (colorClass (starFamily c P) color t) :=
        colorClassMemberEquiv (starFamily c P) color t ⟨Ap, hfst⟩
      let V : Member (colorClass (starFamily c P) color t) :=
        colorClassMemberEquiv (starFamily c P) color t ⟨Aq, rfl⟩
      have hUV : U ≠ V := by
        intro hUVeq
        have hedge_support : Ap.1 = Aq.1 := by
          simpa [U, V, Ap, Aq] using
            congrArg (fun A : Member (colorClass (starFamily c P) color t) => A.1) hUVeq
        have hedge : Ap = Aq := by
          exact Subtype.ext hedge_support
        exact hpq ((starEdge_injective hcP) hedge)
      have hsepUV : SeparatesOn cap U.1 V.1 (assignColor t U) (assignColor t V) :=
        hsepColor t U V hUV
      have hcenterNe : assignColor t U c ≠ assignColor t V c := by
        exact separatesOn_star_edges_imp_center_ne (cap := cap) hcP hpq hsepUV
      have htransportL :
          assignColor (color Ap)
            (colorSelfMember (starFamily c P) color Ap) c =
          assignColor t U c := by
        exact hassignColor_transport (A := Ap) (s := color Ap) (t := t)
          rfl hfst hfst
      have hsnd : assignColor t U c = assignColor t V c := by
        calc
          assignColor t U c =
              assignColor (color Ap)
                (colorSelfMember (starFamily c P) color Ap) c :=
            htransportL.symm
          _ = assignColor (color Aq) (colorSelfMember (starFamily c P) color Aq) c := hsndRaw
          _ = assignColor t V c := by rfl
      exact hcenterNe hsnd
    have hle : Fintype.card ↑P ≤ Fintype.card (Fin k × Fin (cap c)) := by
      simpa using Fintype.card_le_of_injective f hf
    simpa using hle
  · intro hP
    let d := cap c
    have hd : 0 < d := hcap c
    let e : ↑P ≃ Fin (Fintype.card ↑P) := Fintype.equivFin ↑P
    have hbound : Fintype.card ↑P ≤ k * d := by
      simpa [d] using hP
    let emb : ↑P ↪ Fin (k * d) :=
      { toFun := fun p => ⟨(e p).1, Nat.lt_of_lt_of_le (e p).2 hbound⟩
        inj' := by
          intro p q hpq
          have hvals : (e p).1 = (e q).1 := by
            exact congrArg (fun z : Fin (k * d) => z.1) hpq
          apply e.injective
          apply Fin.ext
          exact hvals }
    let sm : ↑P ≃ Member (starFamily c P) := starMemberEquiv c P hcP
    let color : Member (starFamily c P) → Fin k := fun A =>
      let p := sm.symm A
      let x := emb p
      ⟨x.1 / d, (Nat.div_lt_iff_lt_mul hd).2 (by simp [d])⟩
    refine ⟨color, ?_⟩
    intro t
    let ec := colorClassMemberEquiv (starFamily c P) color t
    let base : Point cap := fun i => ⟨0, hcap i⟩
    let assign : Member (colorClass (starFamily c P) color t) → Point cap := fun U i =>
      let A := ec.symm U
      let p := sm.symm A.1
      let x := emb p
      if h : i = c then by
        cases h
        exact ⟨x.1 % d, Nat.mod_lt _ hd⟩
      else base i
    refine ⟨assign, ?_⟩
    intro U V hUV
    let A := ec.symm U
    let B := ec.symm V
    let p : ↑P := sm.symm A.1
    let q : ↑P := sm.symm B.1
    let x : Fin (k * d) := emb p
    let y : Fin (k * d) := emb q
    have hU' : ec A = U := by simp [A]
    have hV' : ec B = V := by simp [B]
    have hU : A.1.1 = U.1 := by
      exact congrArg (fun W : Member (colorClass (starFamily c P) color t) => W.1) hU'
    have hV : B.1.1 = V.1 := by
      exact congrArg (fun W : Member (colorClass (starFamily c P) color t) => W.1) hV'
    have hpq : p ≠ q := by
      intro hpqeq
      have hAB1 : A.1 = B.1 := by
        calc
          A.1 = sm p := by simp [A, p]
          _ = sm q := by rw [hpqeq]
          _ = B.1 := by simp [B, q]
      have hAB : A = B := by
        apply Subtype.ext
        exact hAB1
      apply hUV
      calc
        U = ec A := hU'.symm
        _ = ec B := congrArg ec hAB
        _ = V := hV'
    have hdiv : x.1 / d = y.1 / d := by
      have hAt : color A.1 = t := A.2
      have hBt : color B.1 = t := B.2
      have hxdiv : x.1 / d = t.1 := by
        simpa [color, A, p, x, d] using congrArg Fin.val hAt
      have hydiv : y.1 / d = t.1 := by
        simpa [color, B, q, y, d] using congrArg Fin.val hBt
      exact hxdiv.trans hydiv.symm
    have hassignU : assign U c = ⟨x.1 % d, Nat.mod_lt _ hd⟩ := by
      simp [assign, A, p, x, d]
    have hassignV : assign V c = ⟨y.1 % d, Nat.mod_lt _ hd⟩ := by
      simp [assign, B, q, y, d]
    have hcenterNe : assign U c ≠ assign V c := by
      intro hEq
      have hmodEq : x.1 % d = y.1 % d := by
        have hfin : (⟨x.1 % d, Nat.mod_lt _ hd⟩ : Fin d) = ⟨y.1 % d, Nat.mod_lt _ hd⟩ := by
          calc
            (⟨x.1 % d, Nat.mod_lt _ hd⟩ : Fin d) = assign U c := hassignU.symm
            _ = assign V c := hEq
            _ = (⟨y.1 % d, Nat.mod_lt _ hd⟩ : Fin d) := hassignV
        exact congrArg Fin.val hfin
      have hxy : x.1 = y.1 := nat_eq_of_div_eq_of_mod_eq hdiv hmodEq
      have hxyFin : x = y := Fin.ext hxy
      exact hpq (emb.injective hxyFin)
    have hAcA' : c ∈ (sm p).1 := center_mem_starEdge c P p
    have hBcB' : c ∈ (sm q).1 := center_mem_starEdge c P q
    have hAp_support : (sm p).1 = A.1.1 := by
      simp [A, p]
    have hBq_support : (sm q).1 = B.1.1 := by
      simp [B, q]
    have hAcA : c ∈ A.1.1 := by simpa [hAp_support] using hAcA'
    have hBcB : c ∈ B.1.1 := by simpa [hBq_support] using hBcB'
    have hUc : c ∈ U.1 := by simpa [← hU] using hAcA
    have hVc : c ∈ V.1 := by simpa [← hV] using hBcB
    exact ⟨c, Finset.mem_inter.mpr ⟨hUc, hVc⟩, hcenterNe⟩

end StarColoring

end Erdos278
