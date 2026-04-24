import Erdos278.GraphLinks.Chi
import Erdos278.GraphLinks.BipartitePack
import Erdos278.GraphLinks.BipartiteUpperHelpers

open Finset
open scoped BigOperators

universe u

namespace Erdos278

variable {ι : Type u} [DecidableEq ι]

section BipartiteExact

/-- The exact value predicted by the paper in the complete bipartite regime
`a < d` (with `a ≤ b`). -/
def bipartiteSmallSideValue (a b d : ℕ) : ℕ :=
  a * (b / d) + min a (b % d)

variable {d : ℕ} {L R : Finset ι}

/-- In a normalized complete bipartite coloring, a right-star color can hit a fixed row
in at most one column. -/
lemma right_star_hits_row_at_most_one
    (_ : Disjoint L R)
    {r : ι} (_ : r ∈ R)
    {l : ι} (_ : l ∈ L)
    {H : SupportFamily ι}
    (_ : H ⊆ starLink r L) :
    (H.filter fun S => ({l, r} : Finset ι) = S).card ≤ 1 := by
  classical
  have hsubset :
      H.filter (fun S => ({l, r} : Finset ι) = S) ⊆
        ({({l, r} : Finset ι)} : Finset (Finset ι)) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    exact Finset.mem_singleton.mpr hS.2.symm
  exact le_trans (Finset.card_le_card hsubset) (by simp)

lemma bipartiteSmallSideValue_le_b
    {a b d : ℕ}
    (_ : 0 < d) (ha : a < d) :
    bipartiteSmallSideValue a b d ≤ b := by
  have ha' : a ≤ d := Nat.le_of_lt ha
  have hmul : a * (b / d) ≤ d * (b / d) :=
    Nat.mul_le_mul_right (b / d) ha'
  have hmin : min a (b % d) ≤ b % d :=
    Nat.min_le_right _ _
  calc
    bipartiteSmallSideValue a b d = a * (b / d) + min a (b % d) := rfl
    _ ≤ d * (b / d) + b % d := Nat.add_le_add hmul hmin
    _ = (b / d) * d + b % d := by rw [Nat.mul_comm]
    _ = b % d + (b / d) * d := by rw [Nat.add_comm]
    _ = b := by
          simpa [Nat.mul_comm] using (Nat.mod_add_div b d)

lemma profile_y_lt_mod
    {a b d y : ℕ}
    (hd : 0 < d) (ha : a < d)
    (hyr : y < b % d) :
    bipartiteSmallSideValue a b d ≤ y + a * ((b - y + d - 1) / d) := by
  let q := b / d
  let r := b % d
  have hb : r + q * d = b := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.mod_add_div b d)
  have hy_le : y ≤ r := Nat.le_of_lt hyr
  have hsub : b - y = q * d + (r - y) := by
    rw [← hb, Nat.add_comm r (q * d), Nat.add_sub_assoc hy_le]
  have hpos : 0 < r - y := Nat.sub_pos_of_lt hyr
  have hzge : d ≤ (r - y) + d - 1 := by
    have hone : 1 ≤ r - y := Nat.succ_le_of_lt hpos
    cases d with
    | zero =>
        cases Nat.lt_asymm hd hd
    | succ d' =>
        calc
          d' + 1 = d' + 1 := rfl
          _ ≤ d' + (r - y) := Nat.add_le_add_left hone d'
          _ = (r - y) + d' := by simp [Nat.add_comm]
          _ = (r - y) + (d' + 1) - 1 := by simp
  have hq1 : q + 1 ≤ (b - y + d - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      (q + 1) * d = q * d + d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ q * d + ((r - y) + d - 1) := Nat.add_le_add_left hzge (q * d)
      _ = (q * d + (r - y)) + d - 1 := by
            cases d with
            | zero => cases Nat.lt_asymm hd hd
            | succ d' =>
                calc
                  q * (d' + 1) + (r - y + d')
                      = q * (d' + 1) + ((r - y + d') + 1) - 1 := by
                          simp
                  _ = q * (d' + 1) + (r - y + (d' + 1)) - 1 := by
                          rw [Nat.add_assoc]
                  _ = q * (d' + 1) + (r - y) + (d' + 1) - 1 := by
                          simp [Nat.add_assoc]
      _ = b - y + d - 1 := by rw [← hsub]
  have hmul : a * (q + 1) ≤ a * ((b - y + d - 1) / d) :=
    Nat.mul_le_mul_left a hq1
  calc
    bipartiteSmallSideValue a b d = a * q + min a r := by
      simp [bipartiteSmallSideValue, q, r]
    _ ≤ a * q + a := Nat.add_le_add_left (Nat.min_le_left _ _) _
    _ = a * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ a * ((b - y + d - 1) / d) := hmul
    _ ≤ y + a * ((b - y + d - 1) / d) := Nat.le_add_left _ _

lemma profile_y_eq_mod
    {a b d y : ℕ}
    (hd : 0 < d)
    (hyr : y = b % d) :
    bipartiteSmallSideValue a b d ≤ y + a * ((b - y + d - 1) / d) := by
  let q := b / d
  let r := b % d
  have hb : r + q * d = b := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.mod_add_div b d)
  have hr : r = y := by
    simpa [r] using hyr.symm
  have hsub : b - y = q * d := by
    rw [← hr, ← hb, Nat.add_sub_cancel_left]
  have hq : q ≤ (b - y + d - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      q * d ≤ q * d + (d - 1) := Nat.le_add_right _ _
      _ = q * d + d - 1 := by
        cases d with
        | zero => cases Nat.lt_asymm hd hd
        | succ d' => simp
      _ = b - y + d - 1 := by rw [hsub]
  have hmul : a * q ≤ a * ((b - y + d - 1) / d) :=
    Nat.mul_le_mul_left a hq
  calc
    bipartiteSmallSideValue a b d = a * q + min a r := by
      simp [bipartiteSmallSideValue, q, r]
    _ = a * q + min a y := by simp [hr]
    _ ≤ a * q + y := Nat.add_le_add_left (Nat.min_le_right _ _) _
    _ ≤ y + a * ((b - y + d - 1) / d) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add_left hmul y

lemma profile_mod_lt_y_le_b
    {a b d y : ℕ}
    (hd : 0 < d) (ha : a < d)
    (hyb : y ≤ b)
    (hyr : b % d < y) :
    bipartiteSmallSideValue a b d ≤ y + a * ((b - y + d - 1) / d) := by
  let q := b / d
  let r := b % d
  let z := y - r
  let m := z / d
  have hzr : r ≤ y := Nat.le_of_lt hyr
  have hy_expr : y = r + z := by
    dsimp [z]
    calc
      y = y - r + r := (Nat.sub_add_cancel hzr).symm
      _ = r + (y - r) := by simp [Nat.add_comm]
  have hb : r + q * d = b := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.mod_add_div b d)
  have hqdz : z ≤ q * d := by
    rw [hy_expr] at hyb
    rw [← hb] at hyb
    exact Nat.le_of_add_le_add_left hyb
  have hmq : m ≤ q := by
    have hm_lt : m < q + 1 := by
      dsimp [m]
      apply (Nat.div_lt_iff_lt_mul hd).2
      calc
        z ≤ q * d := hqdz
        _ < q * d + d := Nat.lt_add_of_pos_right hd
        _ = (q + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_succ_iff.mp hm_lt
  have hzbound : z ≤ m * d + (d - 1) := by
    dsimp [m]
    calc
      z = (z / d) * d + z % d := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod z d).symm
      _ ≤ (z / d) * d + (d - 1) := by
        exact Nat.add_le_add_left (Nat.le_pred_of_lt (Nat.mod_lt z hd)) _
      _ = m * d + (d - 1) := rfl
  have hsub : b - y = q * d - z := by
    rw [hy_expr, ← hb]
    exact Nat.add_sub_add_left r (q * d) z
  have hsplit : q * d = (q - m) * d + m * d := by
    calc
      q * d = ((q - m) + m) * d := by rw [Nat.sub_add_cancel hmq]
      _ = (q - m) * d + m * d := by rw [Nat.add_mul]
  have hqsub : q - m ≤ (b - y + d - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    rw [hsub]
    have hqd_target : (q - m) * d + m * d ≤ (q * d - z + (d - 1)) + m * d := by
      calc
        (q - m) * d + m * d = q * d := by simp [hsplit]
        _ = (q * d - z) + z := by exact (Nat.sub_add_cancel hqdz).symm
        _ ≤ (q * d - z) + (m * d + (d - 1)) := Nat.add_le_add_left hzbound _
        _ = (q * d - z + (d - 1)) + m * d := by
              simp [Nat.add_left_comm, Nat.add_comm]
    have hqd_target' :
        (q - m) * d + m * d ≤ (q * d - z + (d - 1)) + m * d := hqd_target
    have hleft : (q - m) * d ≤ q * d - z + (d - 1) := by
      exact Nat.le_of_add_le_add_right hqd_target'
    have hright :
        q * d - z + (d - 1) = q * d - z + d - 1 := by
      cases d with
      | zero => cases Nat.lt_asymm hd hd
      | succ d' => simp
    exact hright ▸ hleft
  have ham : a * m ≤ z := by
    calc
      a * m ≤ d * m := Nat.mul_le_mul_right m (Nat.le_of_lt ha)
      _ = m * d := by rw [Nat.mul_comm]
      _ ≤ z := by
            dsimp [m]
            exact Nat.div_mul_le_self z d
  have hmul : a * (q - m) ≤ a * ((b - y + d - 1) / d) :=
    Nat.mul_le_mul_left a hqsub
  calc
    bipartiteSmallSideValue a b d = a * q + min a r := by
      simp [bipartiteSmallSideValue, q, r]
    _ ≤ a * q + r := Nat.add_le_add_left (Nat.min_le_right _ _) _
    _ = r + (a * (q - m) + a * m) := by
      rw [← Nat.sub_add_cancel hmq, Nat.mul_add]
      simp [Nat.add_comm]
    _ ≤ r + (a * ((b - y + d - 1) / d) + z) := by
      apply Nat.add_le_add_left
      exact Nat.add_le_add hmul ham
    _ = y + a * ((b - y + d - 1) / d) := by
      rw [hy_expr]
      simp [Nat.add_assoc, Nat.add_comm]

/-- Arithmetic core of the small-side lower bound: for every tentative number `y`
of right-star colors, the count `y + a * ceil((b-y)/d)` is bounded below by the
closed form from the paper. This is the only purely arithmetic ingredient needed
after the normalized star/empty-color reduction. -/
lemma bipartiteSmallSideValue_le_profile
    {a b d y : ℕ}
    (hd : 0 < d) (ha : a < d) (_ : a ≤ b) :
    bipartiteSmallSideValue a b d ≤ y + a * ((b - y + d - 1) / d) := by
  by_cases hyb : y ≤ b
  · by_cases hyr_lt : y < b % d
    · exact profile_y_lt_mod hd ha hyr_lt
    · by_cases hyr_eq : y = b % d
      · exact profile_y_eq_mod hd hyr_eq
      · have hyr_gt : b % d < y := by
          exact lt_of_le_of_ne (Nat.le_of_not_gt hyr_lt) (by
            intro h
            apply hyr_eq
            exact h.symm)
        exact profile_mod_lt_y_le_b hd ha hyb hyr_gt
  · have hbase : bipartiteSmallSideValue a b d ≤ b :=
      bipartiteSmallSideValue_le_b hd ha
    have hby : b < y := Nat.lt_of_not_ge hyb
    exact le_trans hbase (le_trans (Nat.le_of_lt hby) (Nat.le_add_right y _))

/-- A color of a normalized `K_{|L|,|R|}` coloring is called "right" if its whole
color class is contained in a right-star. -/
def IsRightColor
    {k : ℕ}
    (color : Member (completeBipartiteLink L R) → Fin k)
    (t : Fin k) : Prop :=
  ∃ r : ι, r ∈ R ∧
    colorClass (completeBipartiteLink L R) color t ⊆ starLink r L

/-- The set of right-star colors in a normalized complete bipartite coloring. -/
noncomputable def RightColors
    {k : ℕ}
    (color : Member (completeBipartiteLink L R) → Fin k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (IsRightColor (L := L) (R := R) color)

/-- The non-right colors whose color class contains a set incident to the row `l`. -/
noncomputable def RowLeftColors
    {k : ℕ}
    (color : Member (completeBipartiteLink L R) → Fin k)
    (l : ι) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun t =>
    ¬ IsRightColor (L := L) (R := R) color t ∧
      ∃ S ∈ colorClass (completeBipartiteLink L R) color t, l ∈ S
lemma colorClass_nonempty_left_or_right_star
    {k : ℕ}
    (hLR : Disjoint L R)
    (color : Member (completeBipartiteLink L R) → Fin k)
    (t : Fin k)
    (hpackt :
      PerfectlyPackable
        (colorClass (completeBipartiteLink L R) color t)
        (fun _ => d))
    (hne :
      (colorClass (completeBipartiteLink L R) color t).Nonempty) :
    (∃ l : ι, l ∈ L ∧
      colorClass (completeBipartiteLink L R) color t ⊆ starLink l R) ∨
    (∃ r : ι, r ∈ R ∧
      colorClass (completeBipartiteLink L R) color t ⊆ starLink r L) := by
  have hsub :
      colorClass (completeBipartiteLink L R) color t ⊆
        completeBipartiteLink L R := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
    exact hAS ▸ A.2
  have hinter :
      IntersectingFamily (colorClass (completeBipartiteLink L R) color t) := by
    rcases hpackt with ⟨assign, hsep⟩
    intro A B hneAB
    rcases hsep A B hneAB with ⟨i, hiAB, _⟩
    exact ⟨i, hiAB⟩
  exact
    intersectingFamily_completeBipartite_subfamily_subset_star
      (L := L) (R := R) hLR hsub hinter hne


lemma rowLeft_colorClass_subset_row_star
    {k : ℕ}
    (hLR : Disjoint L R)
    (color : Member (completeBipartiteLink L R) → Fin k)
    (hpack : ∀ t : Fin k,
      PerfectlyPackable
        (colorClass (completeBipartiteLink L R) color t)
        (fun _ => d))
    {l : ι} (hl : l ∈ L)
    {t : Fin k}
    (ht : t ∈ RowLeftColors (L := L) (R := R) color l) :
    colorClass (completeBipartiteLink L R) color t ⊆ starLink l R := by
  classical
  rcases Finset.mem_filter.mp ht with ⟨_, hrow⟩
  rcases hrow with ⟨hnotRight, ⟨S, hS, hlS⟩⟩
  have hne : (colorClass (completeBipartiteLink L R) color t).Nonempty := ⟨S, hS⟩
  rcases colorClass_nonempty_left_or_right_star
      (L := L) (R := R) (d := d) hLR color t (hpack t) hne with hL | hR
  · rcases hL with ⟨l₀, hl₀, hsub₀⟩
    have hSstar : S ∈ starLink l₀ R := hsub₀ hS
    rcases Finset.mem_image.mp hSstar with ⟨r, hrR, hSr⟩
    have hlEq : l₀ = l := by
      have hlmem : l ∈ ({l₀, r} : Finset ι) := by
        simpa [hSr] using hlS
      rw [Finset.mem_insert, Finset.mem_singleton] at hlmem
      rcases hlmem with h | h
      · exact h.symm
      · have hlR : l ∈ R := by simpa [h] using hrR
        exact False.elim ((Finset.disjoint_left.mp hLR) hl hlR)
    simpa [hlEq] using hsub₀
  · exact False.elim (hnotRight hR)

lemma rowLeft_colorClass_card_le
    {k : ℕ}
    (hLR : Disjoint L R)
    (color : Member (completeBipartiteLink L R) → Fin k)
    (hpack : ∀ t : Fin k,
      PerfectlyPackable
        (colorClass (completeBipartiteLink L R) color t)
        (fun _ => d))
    (_ : 0 < d)
    {l : ι} (hl : l ∈ L)
    {t : Fin k}
    (ht : t ∈ RowLeftColors (L := L) (R := R) color l) :
    (colorClass (completeBipartiteLink L R) color t).card ≤ d := by
  classical
  let G := completeBipartiteLink L R
  have hsubT : colorClass G color t ⊆ starLink l R :=
    rowLeft_colorClass_subset_row_star
      (L := L) (R := R) (d := d) hLR color hpack hl ht
  let coord : Member (colorClass G color t) → Fin d := fun A =>
    (Classical.choose (hpack t) A) l
  have hcoord_inj : Function.Injective coord := by
    intro A B hcoord
    by_contra hne
    rcases (Classical.choose_spec (hpack t)) A B hne with ⟨i, hi, hneqi⟩
    have hAstar : A.1 ∈ starLink l R := hsubT A.2
    have hBstar : B.1 ∈ starLink l R := hsubT B.2
    rcases Finset.mem_image.mp hAstar with ⟨rA, hrAR, hAeq⟩
    rcases Finset.mem_image.mp hBstar with ⟨rB, hrBR, hBeq⟩
    have hiA : i ∈ ({l, rA} : Finset ι) := by
      simpa [hAeq] using (Finset.mem_inter.mp hi).1
    have hiB : i ∈ ({l, rB} : Finset ι) := by
      simpa [hBeq] using (Finset.mem_inter.mp hi).2
    have hiEqL : i = l := by
      rw [Finset.mem_insert, Finset.mem_singleton] at hiA hiB
      rcases hiA with hil | hirA
      · exact hil
      · rcases hiB with hil | hirB
        · have : rA ∈ L := by simpa [hirA.symm.trans hil] using hl
          exact False.elim ((Finset.disjoint_left.mp hLR) this hrAR)
        · have hrAB : rA = rB := hirA.symm.trans hirB
          have hABset : A.1 = B.1 := by
            calc
              A.1 = ({l, rA} : Finset ι) := by simpa using hAeq.symm
              _ = ({l, rB} : Finset ι) := by simp [hrAB]
              _ = B.1 := by simpa using hBeq
          exact False.elim (hne (Subtype.ext hABset))
    subst i
    exact hneqi hcoord
  have hcard := Fintype.card_le_of_injective coord hcoord_inj
  simpa [coord, G]
    using hcard

lemma rowLeftColors_lower_bound
    {k : ℕ}
    (hLR : Disjoint L R)
    (color : Member (completeBipartiteLink L R) → Fin k)
    (hpack : ∀ t : Fin k,
      PerfectlyPackable
        (colorClass (completeBipartiteLink L R) color t)
        (fun _ => d))
    {l : ι} (hl : l ∈ L) :
    (R.card - (RightColors (L := L) (R := R) color).card + d - 1) / d
      ≤ (RowLeftColors (L := L) (R := R) color l).card := by
  classical
  by_cases hd : 0 < d
  · let G := completeBipartiteLink L R
    let edge : ↥R → Member G := fun r =>
      ⟨({l, r.1} : Finset ι),
        (mem_completeBipartiteLink_iff).2 ⟨l, hl, r.1, r.2, rfl⟩⟩
    have hedgeClass (r : ↥R) :
        ({l, r.1} : Finset ι) ∈ colorClass G color (color (edge r)) := by
      refine Finset.mem_image.mpr ?_
      refine ⟨edge r, ?_, rfl⟩
      refine Finset.mem_filter.mpr ?_
      exact ⟨by simp [edge], rfl⟩
    have right_center_of_row_edge
        {c r : ι} (hc : c ∈ R) (hr : r ∈ R)
        (hmem : ({l, r} : Finset ι) ∈ starLink c L) :
        r = c := by
      rcases Finset.mem_image.mp hmem with ⟨p, hpL, hcp⟩
      have hlmem : l ∈ ({c, p} : Finset ι) := by
        simp [hcp]
      rw [Finset.mem_insert, Finset.mem_singleton] at hlmem
      rcases hlmem with hlc | hlp
      · have : l ∈ R := hlc ▸ hc
        exact False.elim ((Finset.disjoint_left.mp hLR) hl this)
      have hrmem : r ∈ ({c, p} : Finset ι) := by
        simp [hcp]
      rw [Finset.mem_insert, Finset.mem_singleton] at hrmem
      rcases hrmem with hrc | hrp
      · exact hrc
      · have : r ∈ L := hrp ▸ hpL
        exact False.elim ((Finset.disjoint_left.mp hLR) this hr)
    let rowFiber : Fin k → Finset ↥R := fun t =>
      R.attach.filter fun r => color (edge r) = t
    have hrowFiber_card_sum :
        (∑ t : Fin k, (rowFiber t).card) = R.card := by
      have hdisj :
          ∀ t₁ ∈ (Finset.univ : Finset (Fin k)),
            ∀ t₂ ∈ (Finset.univ : Finset (Fin k)),
              t₁ ≠ t₂ → Disjoint (rowFiber t₁) (rowFiber t₂) := by
        intro t₁ _ t₂ _ hneq
        refine Finset.disjoint_left.mpr ?_
        intro r hr₁ hr₂
        have hr₁' := Finset.mem_filter.mp hr₁
        have hr₂' := Finset.mem_filter.mp hr₂
        exact hneq (hr₁'.2.symm.trans hr₂'.2)
      have hUnion :
          (Finset.univ : Finset (Fin k)).biUnion rowFiber = R.attach := by
        ext r
        simp [rowFiber]
      calc
        (∑ t : Fin k, (rowFiber t).card)
            = ((Finset.univ : Finset (Fin k)).biUnion rowFiber).card := by
                symm
                exact Finset.card_biUnion hdisj
        _ = R.attach.card := by rw [hUnion]
        _ = R.card := by simp
    have hfiber_right_le_one {t : Fin k}
        (ht : t ∈ RightColors (L := L) (R := R) color) :
        (rowFiber t).card ≤ 1 := by
      rcases Finset.mem_filter.mp ht with ⟨_, hRight⟩
      rcases hRight with ⟨c, hc, hsub⟩
      have hsubset : rowFiber t ⊆ ({⟨c, hc⟩} : Finset ↥R) := by
        intro r hr
        apply Finset.mem_singleton.mpr
        apply Subtype.ext
        have hrmem : ({l, r.1} : Finset ι) ∈ colorClass G color t := by
          have hrt := (Finset.mem_filter.mp hr).2
          simpa [hrt] using hedgeClass r
        have hstar : ({l, r.1} : Finset ι) ∈ starLink c L := hsub hrmem
        exact right_center_of_row_edge (c := c) hc r.2 hstar
      exact le_trans (Finset.card_le_card hsubset) (by simp)
    have hfiber_nonright_le_d {t : Fin k}
        (htR : t ∉ RightColors (L := L) (R := R) color) :
        (rowFiber t).card ≤ d := by
      by_cases hne : (rowFiber t).Nonempty
      · rcases hne with ⟨r, hr⟩
        have htRow : t ∈ RowLeftColors (L := L) (R := R) color l := by
          refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
          refine ⟨?_, ?_⟩
          · intro hIR
            exact htR (by simpa [RightColors] using hIR)
          · refine ⟨({l, r.1} : Finset ι), ?_, by simp⟩
            have hrt := (Finset.mem_filter.mp hr).2
            simpa [hrt] using hedgeClass r
        have hclass_le :
            (colorClass G color t).card ≤ d :=
          rowLeft_colorClass_card_le
            (L := L) (R := R) (d := d)
            hLR color hpack hd hl htRow
        let toClass : ↥(rowFiber t) → Member (colorClass G color t) := fun r =>
          ⟨({l, r.1.1} : Finset ι), by
            have hrt := (Finset.mem_filter.mp r.2).2
            simpa [hrt] using hedgeClass r.1⟩
        have htoClass_inj : Function.Injective toClass := by
          intro r₁ r₂ hEq
          apply Subtype.ext
          have hset : ({l, r₁.1.1} : Finset ι) = ({l, r₂.1.1} : Finset ι) :=
            congrArg Subtype.val hEq
          have hrmem : r₁.1.1 ∈ ({l, r₂.1.1} : Finset ι) := by
            simpa [hset] using (show r₁.1.1 ∈ ({l, r₁.1.1} : Finset ι) by simp)
          rw [Finset.mem_insert, Finset.mem_singleton] at hrmem
          rcases hrmem with hrl | hrr
          · have : r₁.1.1 ∈ L := by simpa [hrl] using hl
            exact False.elim ((Finset.disjoint_left.mp hLR) this r₁.1.2)
          · exact Subtype.ext hrr
        have hcard' :
            (rowFiber t).card ≤ (colorClass G color t).card := by
          simpa [toClass] using (Fintype.card_le_of_injective toClass htoClass_inj)
        exact le_trans hcard' hclass_le
      · have hempty : rowFiber t = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hempty]
        simp
    let nonRightColors : Finset (Fin k) :=
      Finset.univ.filter fun t => t ∉ RightColors (L := L) (R := R) color
    have hsum_split :
        (∑ t : Fin k, (rowFiber t).card) =
          Finset.sum (RightColors (L := L) (R := R) color) (fun t => (rowFiber t).card) +
            Finset.sum nonRightColors (fun t => (rowFiber t).card) := by
      symm
      simpa [nonRightColors, Finset.sum_filter] using
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin k)))
          (p := fun t => t ∈ RightColors (L := L) (R := R) color)
          (f := fun t => (rowFiber t).card))
    have hright_sum_aux :
        ∀ s : Finset (Fin k),
          s ⊆ RightColors (L := L) (R := R) color →
            Finset.sum s (fun t => (rowFiber t).card) ≤ s.card := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · intro hs
        simp
      · intro a s ha ih hs
        have haR : a ∈ RightColors (L := L) (R := R) color := by
          exact hs (Finset.mem_insert_self a s)
        have hs' : s ⊆ RightColors (L := L) (R := R) color := by
          intro t ht
          exact hs (Finset.mem_insert_of_mem ht)
        have ih' := ih hs'
        have hfa : (rowFiber a).card ≤ 1 := hfiber_right_le_one haR
        calc
          Finset.sum (insert a s) (fun t => (rowFiber t).card)
              = (rowFiber a).card + Finset.sum s (fun t => (rowFiber t).card) := by
                  simp [ha]
          _ ≤ 1 + s.card := Nat.add_le_add hfa ih'
          _ = (insert a s).card := by simp [ha, Nat.add_comm]
    have hright_sum :
        Finset.sum (RightColors (L := L) (R := R) color) (fun t => (rowFiber t).card)
          ≤ (RightColors (L := L) (R := R) color).card := by
      exact hright_sum_aux (RightColors (L := L) (R := R) color) (by intro t ht; exact ht)
    have hnonright_sum :
        Finset.sum nonRightColors (fun t => (rowFiber t).card)
          ≤ (RowLeftColors (L := L) (R := R) color l).card * d := by
      let g : Fin k → ℕ := fun t =>
        if t ∈ RowLeftColors (L := L) (R := R) color l then d else 0
      have hle_g_aux :
          ∀ s : Finset (Fin k), s ⊆ nonRightColors →
            Finset.sum s (fun t => (rowFiber t).card) ≤ Finset.sum s g := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · intro hs
          simp [g]
        · intro a s ha ih hs
          have haNR : a ∈ nonRightColors := by
            exact hs (Finset.mem_insert_self a s)
          have hs' : s ⊆ nonRightColors := by
            intro t ht
            exact hs (Finset.mem_insert_of_mem ht)
          have ih' := ih hs'
          have haBound : (rowFiber a).card ≤ g a := by
            have htR : a ∉ RightColors (L := L) (R := R) color :=
              (Finset.mem_filter.mp haNR).2
            by_cases haRow : a ∈ RowLeftColors (L := L) (R := R) color l
            · have htd : (rowFiber a).card ≤ d := hfiber_nonright_le_d htR
              simpa [g, haRow] using htd
            · have hne : ¬ (rowFiber a).Nonempty := by
                intro hne
                rcases hne with ⟨r, hr⟩
                have hrt := (Finset.mem_filter.mp hr).2
                have haRow' : a ∈ RowLeftColors (L := L) (R := R) color l := by
                  refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
                  refine ⟨?_, ?_⟩
                  · intro hIR
                    exact htR (by simpa [RightColors] using hIR)
                  · refine ⟨({l, r.1} : Finset ι), ?_, by simp⟩
                    simpa [hrt] using hedgeClass r
                exact haRow haRow'
              have hempty : rowFiber a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
              have hzero : (rowFiber a).card = 0 := by simp [hempty]
              simp [g, haRow, hzero]
          calc
            Finset.sum (insert a s) (fun t => (rowFiber t).card)
                = (rowFiber a).card + Finset.sum s (fun t => (rowFiber t).card) := by
                    simp [ha]
            _ ≤ g a + Finset.sum s g := Nat.add_le_add haBound ih'
            _ = Finset.sum (insert a s) g := by
                  rw [Finset.sum_insert ha]
      have hle_g :
          Finset.sum nonRightColors (fun t => (rowFiber t).card)
            ≤ Finset.sum nonRightColors g := by
        exact hle_g_aux nonRightColors (by intro t ht; exact ht)
      calc
        Finset.sum nonRightColors (fun t => (rowFiber t).card)
            ≤ Finset.sum nonRightColors g := hle_g
        _ = Finset.sum (nonRightColors.filter
              (fun t => t ∈ RowLeftColors (L := L) (R := R) color l)) (fun _ => d) := by
              symm
              exact Finset.sum_filter
                (s := nonRightColors)
                (p := fun t => t ∈ RowLeftColors (L := L) (R := R) color l)
                (f := fun _ => d)
        _ = Finset.sum (RowLeftColors (L := L) (R := R) color l) (fun _ => d) := by
              have hfilterEq :
                  nonRightColors.filter
                    (fun t => t ∈ RowLeftColors (L := L) (R := R) color l) =
                    RowLeftColors (L := L) (R := R) color l := by
                ext t
                constructor
                · intro ht
                  exact (Finset.mem_filter.mp ht).2
                · intro ht
                  refine Finset.mem_filter.mpr ?_
                  refine ⟨?_, ht⟩
                  have hnotRight : ¬ IsRightColor (L := L) (R := R) color t := by
                    exact (Finset.mem_filter.mp ht).2.1
                  exact Finset.mem_filter.mpr ⟨by simp, by simpa [RightColors] using hnotRight⟩
              rw [hfilterEq]
        _ = (RowLeftColors (L := L) (R := R) color l).card * d := by
              simp [Nat.mul_comm]
    have hcard :
        R.card ≤
          (RightColors (L := L) (R := R) color).card +
            (RowLeftColors (L := L) (R := R) color l).card * d := by
      calc
        R.card = (∑ t : Fin k, (rowFiber t).card) := by symm; exact hrowFiber_card_sum
        _ =
          (Finset.sum (RightColors (L := L) (R := R) color) (fun t => (rowFiber t).card) +
            Finset.sum nonRightColors (fun t => (rowFiber t).card)) := hsum_split
        _ ≤ (RightColors (L := L) (R := R) color).card +
              (RowLeftColors (L := L) (R := R) color l).card * d := by
              exact Nat.add_le_add hright_sum hnonright_sum
    have hsubbound :
        R.card - (RightColors (L := L) (R := R) color).card
          ≤ (RowLeftColors (L := L) (R := R) color l).card * d := by
      exact (Nat.sub_le_iff_le_add).2 (by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcard)
    have hd1 : d - 1 < d := by
      cases d with
      | zero => cases Nat.lt_asymm hd hd
      | succ d' => simp
    have hlt :
        (R.card - (RightColors (L := L) (R := R) color).card + d - 1) / d
          < (RowLeftColors (L := L) (R := R) color l).card + 1 := by
      apply (Nat.div_lt_iff_lt_mul hd).2
      calc
        R.card - (RightColors (L := L) (R := R) color).card + d - 1
            = (R.card - (RightColors (L := L) (R := R) color).card) + (d - 1) := by
                rw [Nat.add_sub_assoc (Nat.succ_le_of_lt hd)]
        _ ≤ (RowLeftColors (L := L) (R := R) color l).card * d + (d - 1) := by
              exact Nat.add_le_add_right hsubbound (d - 1)
        _ < (RowLeftColors (L := L) (R := R) color l).card * d + d := by
              exact Nat.add_lt_add_left hd1 _
        _ = ((RowLeftColors (L := L) (R := R) color l).card + 1) * d := by
              rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_succ_iff.mp hlt
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    simp [hd0]

lemma rowLeftColors_total_le_nonright
    {k : ℕ}
    (hLR : Disjoint L R)
    (color : Member (completeBipartiteLink L R) → Fin k)
    (hpack : ∀ t : Fin k,
      PerfectlyPackable
        (colorClass (completeBipartiteLink L R) color t)
        (fun _ => d)) :
    L.card *
        ((R.card - (RightColors (L := L) (R := R) color).card + d - 1) / d)
      ≤
      k - (RightColors (L := L) (R := R) color).card := by
  classical
  let q : ℕ :=
    (R.card - (RightColors (L := L) (R := R) color).card + d - 1) / d
  let nonRightColors : Finset (Fin k) :=
    Finset.univ.filter fun t => ¬ IsRightColor (L := L) (R := R) color t
  have hdisj :
      ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
        Disjoint
          (RowLeftColors (L := L) (R := R) color l₁)
          (RowLeftColors (L := L) (R := R) color l₂) := by
    intro l₁ hl₁ l₂ hl₂ hneq
    refine Finset.disjoint_left.mpr ?_
    intro t ht₁ ht₂
    have hsub₁ :
        colorClass (completeBipartiteLink L R) color t ⊆ starLink l₁ R := by
      rcases Finset.mem_filter.mp ht₁ with ⟨_, hrow₁⟩
      rcases hrow₁ with ⟨hnotRight₁, ⟨S, hS, hl₁S⟩⟩
      have hne :
          (colorClass (completeBipartiteLink L R) color t).Nonempty := ⟨S, hS⟩
      rcases colorClass_nonempty_left_or_right_star
          (L := L) (R := R) (d := d)
          hLR color t (hpack t) hne with hL | hR
      · rcases hL with ⟨l₀, hl₀, hsub₀⟩
        have hSstar : S ∈ starLink l₀ R := hsub₀ hS
        rcases Finset.mem_image.mp hSstar with ⟨r, hrR, hSr⟩
        have hlEq : l₀ = l₁ := by
          have hl₁mem : l₁ ∈ ({l₀, r} : Finset ι) := by
            simpa [hSr] using hl₁S
          rw [Finset.mem_insert, Finset.mem_singleton] at hl₁mem
          rcases hl₁mem with h | h
          · exact h.symm
          · have hl₁R : l₁ ∈ R := by simpa [h] using hrR
            exact False.elim ((Finset.disjoint_left.mp hLR) hl₁ hl₁R)
        simpa [hlEq] using hsub₀
      · exact False.elim (hnotRight₁ hR)
    rcases Finset.mem_filter.mp ht₂ with ⟨_, hrow₂⟩
    rcases hrow₂.2 with ⟨S, hS, hl₂S⟩
    have hSstar : S ∈ starLink l₁ R := hsub₁ hS
    rcases Finset.mem_image.mp hSstar with ⟨r, hrR, hSr⟩
    have hlEq : l₂ = l₁ := by
      have hl₂mem : l₂ ∈ ({l₁, r} : Finset ι) := by
        simpa [hSr] using hl₂S
      rw [Finset.mem_insert, Finset.mem_singleton] at hl₂mem
      rcases hl₂mem with h | h
      · exact h
      · have hl₂R : l₂ ∈ R := by simpa [h] using hrR
        exact False.elim ((Finset.disjoint_left.mp hLR) hl₂ hl₂R)
    exact hneq hlEq.symm
  have hUnionSub :
      L.biUnion (fun l => RowLeftColors (L := L) (R := R) color l) ⊆ nonRightColors := by
    intro t ht
    rcases Finset.mem_biUnion.mp ht with ⟨l, hl, htl⟩
    rcases Finset.mem_filter.mp htl with ⟨_, hrow⟩
    exact Finset.mem_filter.mpr ⟨by simp, hrow.1⟩
  have hnrCard :
      nonRightColors.card = k - (RightColors (L := L) (R := R) color).card := by
    have hsum :
        nonRightColors.card + (RightColors (L := L) (R := R) color).card = k := by
      dsimp [nonRightColors, RightColors]
      simpa [Nat.add_comm] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin k)))
          (p := IsRightColor (L := L) (R := R) color))
    exact Nat.eq_sub_of_add_eq hsum
  have hcardUnion :
      (L.biUnion fun l => RowLeftColors (L := L) (R := R) color l).card =
        Finset.sum L (fun l =>
          (RowLeftColors (L := L) (R := R) color l).card) := by
    refine Finset.card_biUnion ?_
    intro l₁ hl₁ l₂ hl₂ hneq
    exact hdisj l₁ hl₁ l₂ hl₂ hneq
  have hsumLowerAux :
      ∀ s : Finset ι, s ⊆ L →
        s.card * q ≤ Finset.sum s (fun l =>
          (RowLeftColors (L := L) (R := R) color l).card) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hs
      simp
    · intro a s ha ih hs
      have haL : a ∈ L := hs (by simp [ha])
      have hsL : s ⊆ L := by
        intro x hx
        exact hs (by simp [hx])
      have ih' := ih hsL
      have haRow :
          q ≤ (RowLeftColors (L := L) (R := R) color a).card := by
        simpa [q] using
          rowLeftColors_lower_bound
            (L := L) (R := R) (d := d)
            hLR color hpack haL
      calc
        (insert a s).card * q = q + s.card * q := by
          simp [ha, Nat.succ_mul, Nat.add_comm]
        _ ≤ (RowLeftColors (L := L) (R := R) color a).card
              + Finset.sum s (fun l =>
                  (RowLeftColors (L := L) (R := R) color l).card) := by
            exact Nat.add_le_add haRow ih'
        _ = Finset.sum (insert a s) (fun l =>
              (RowLeftColors (L := L) (R := R) color l).card) := by
            simp [ha]
  have hsumLower :
      L.card * q ≤
        Finset.sum L (fun l =>
          (RowLeftColors (L := L) (R := R) color l).card) := by
    exact hsumLowerAux L (by intro x hx; exact hx)
  have hsumUpper :
      Finset.sum L (fun l =>
        (RowLeftColors (L := L) (R := R) color l).card)
        ≤ k - (RightColors (L := L) (R := R) color).card := by
    calc
      Finset.sum L (fun l =>
          (RowLeftColors (L := L) (R := R) color l).card)
          = (L.biUnion fun l => RowLeftColors (L := L) (R := R) color l).card := by
              symm
              exact hcardUnion
      _ ≤ nonRightColors.card := Finset.card_le_card hUnionSub
      _ = k - (RightColors (L := L) (R := R) color).card := hnrCard
  simpa [q] using le_trans hsumLower hsumUpper

/-- Combinatorial core of the small-side lower bound. After normalizing a `k`-color
packing of `K_{a,b}` so that every color class is empty or contained in a single
left/right star, let `y` be the number of right-star colors. Then each row still
needs at least `ceil((b-y)/d)` left-star colors, because a right-star color can hit
that row in at most one column while a left-star color can cover at most `d` columns. -/
lemma normalized_completeBipartite_smallSide_profile
    {k : ℕ}
    (hLR : Disjoint L R)
    (_ : L.card ≤ R.card)
    (_ : 0 < d) (_ : L.card < d)
    (hchi :
      ChiPackLinkLe (completeBipartiteLink L R) (fun _ => d) k) :
    ∃ y : ℕ,
      y ≤ k ∧
      L.card * ((R.card - y + d - 1) / d) ≤ k - y := by
  classical
  rcases hchi with ⟨color, hpack⟩
  let rightColors : Finset (Fin k) :=
    RightColors (L := L) (R := R) color
  refine ⟨rightColors.card, ?_, ?_⟩
  · have hle :
        rightColors.card ≤ (Finset.univ : Finset (Fin k)).card := by
      simpa [rightColors, RightColors] using
        (Finset.card_filter_le
          (s := (Finset.univ : Finset (Fin k)))
          (p := IsRightColor (L := L) (R := R) color))
    simpa using hle
  · simpa [rightColors] using
      rowLeftColors_total_le_nonright
        (L := L) (R := R) (d := d) hLR color hpack

theorem chiPackLe_completeBipartite_smallSide_lower
    (hLR : Disjoint L R)
    (hcard : L.card ≤ R.card)
    (hd : 0 < d) (hsmall : L.card < d)
    {k : ℕ}
    (hchi :
      ChiPackLinkLe (completeBipartiteLink L R) (fun _ => d) k) :
    bipartiteSmallSideValue L.card R.card d ≤ k := by
  rcases normalized_completeBipartite_smallSide_profile
      (L := L) (R := R) (d := d) hLR hcard hd hsmall hchi with
    ⟨y, hyk, hleft⟩
  have hprof :
      bipartiteSmallSideValue L.card R.card d ≤
        y + L.card * ((R.card - y + d - 1) / d) := by
    exact bipartiteSmallSideValue_le_profile
      (a := L.card) (b := R.card) (d := d) (y := y) hd hsmall hcard
  have hy' : y + L.card * ((R.card - y + d - 1) / d) ≤ k := by
    have h1 : y + L.card * ((R.card - y + d - 1) / d) ≤ y + (k - y) :=
      Nat.add_le_add_left hleft y
    have h2 : y + (k - y) = k := Nat.add_sub_of_le hyk
    exact h2 ▸ h1
  exact le_trans hprof hy'

lemma perfectlyPackable_mono
    {cap : ι → ℕ}
    {H K : SupportFamily ι}
    (hHK : H ⊆ K)
    (hK : PerfectlyPackable K cap) :
    PerfectlyPackable H cap := by
  rcases hK with ⟨assign, hsep⟩
  refine ⟨fun A => assign ⟨A.1, hHK A.2⟩, ?_⟩
  intro A B hAB
  exact hsep ⟨A.1, hHK A.2⟩ ⟨B.1, hHK B.2⟩ (by
    intro h
    apply hAB
    apply Subtype.ext
    exact congrArg (fun X : Member K => X.1) h)

lemma perfectlyPackable_subset_singleton_left_completeBipartite
    {c : ι} {R : Finset ι} {H : SupportFamily ι}
    (hd : 0 < d)
    (hcR : c ∉ R)
    (hsub : H ⊆ completeBipartiteLink ({c} : Finset ι) R)
    (hcard : R.card ≤ d) :
    PerfectlyPackable H (fun _ => d) := by
  apply perfectlyPackable_mono hsub
  exact
    (perfectlyPackable_completeBipartiteLink_singleton_left_iff
      (cap := fun _ => d) (fun _ => hd) hcR).2 hcard

lemma perfectlyPackable_subset_singleton_right_completeBipartite
    {L : Finset ι} {c : ι} {H : SupportFamily ι}
    (hd : 0 < d)
    (hcL : c ∉ L)
    (hsub : H ⊆ completeBipartiteLink L ({c} : Finset ι))
    (hcard : L.card ≤ d) :
    PerfectlyPackable H (fun _ => d) := by
  apply perfectlyPackable_mono hsub
  exact
    (perfectlyPackable_completeBipartiteLink_singleton_right_iff
      (cap := fun _ => d) (fun _ => hd) hcL).2 hcard

lemma bipartiteSmallSideValue_eq_rightRemainder
    {a b d : ℕ}
    (hrem : b % d ≤ a) :
    bipartiteSmallSideValue a b d = a * (b / d) + b % d := by
  simp [bipartiteSmallSideValue, Nat.min_eq_right hrem]

lemma bipartiteSmallSideValue_eq_leftRemainder
    {a b d : ℕ}
    (hrem : a ≤ b % d) :
    bipartiteSmallSideValue a b d = a * (b / d) + a := by
  simp [bipartiteSmallSideValue, Nat.min_eq_left hrem]

noncomputable def leftIndex
    (eL : ↥L ≃ Fin L.card)
    (A : Member (completeBipartiteLink L R)) : Fin L.card := by
  classical
  let h := (mem_completeBipartiteLink_iff).1 A.2
  let l : ι := Classical.choose h
  have hl : l ∈ L := (Classical.choose_spec h).1
  exact eL ⟨l, hl⟩

noncomputable def rightIndex
    (eR : ↥R ≃ Fin R.card)
    (A : Member (completeBipartiteLink L R)) : Fin R.card := by
  classical
  let h := (mem_completeBipartiteLink_iff).1 A.2
  let h' := (Classical.choose_spec h).2
  let r : ι := Classical.choose h'
  have hr : r ∈ R := (Classical.choose_spec h').1
  exact eR ⟨r, hr⟩

noncomputable def rightRemainderColoring
    (eL : ↥L ≃ Fin L.card)
    (eR : ↥R ≃ Fin R.card)
    (hd : 0 < d)
    (_ : R.card % d ≤ L.card) :
    Member (completeBipartiteLink L R) →
      RightRemainderColor L.card (R.card / d) (R.card % d) := by
  classical
  intro A
  let i := leftIndex (L := L) (R := R) eL A
  let j := rightIndex (L := L) (R := R) eR A
  by_cases hfull : j.1 < (R.card / d) * d
  · exact Sum.inl ⟨i, ⟨j.1 / d, by
      exact (Nat.div_lt_iff_lt_mul hd).2 hfull⟩⟩
  · refine Sum.inr ⟨j.1 - (R.card / d) * d, ?_⟩
    have hjlt : j.1 < R.card := j.2
    have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
    have hge : (R.card / d) * d ≤ j.1 := Nat.le_of_not_gt hfull
    have hltrem : j.1 - (R.card / d) * d < R.card % d := by
      apply Nat.sub_lt_left_of_lt_add hge
      simp [hqdr]
    exact hltrem

lemma colorClass_rightRemainder_inl_subset
    (eL : ↥L ≃ Fin L.card)
    (eR : ↥R ≃ Fin R.card)
    (hd : 0 < d)
    (hrem : R.card % d ≤ L.card)
    (t : Fin L.card × Fin (R.card / d)) :
    ∃ l : ι, l ∈ L ∧
      ∃ B : Finset ι, B ⊆ R ∧ B.card ≤ d ∧
        colorClass
          (completeBipartiteLink L R)
          (rightRemainderColoring (L := L) (R := R) eL eR hd hrem)
          (Sum.inl t)
        ⊆ completeBipartiteLink ({l} : Finset ι) B := by
  classical
  let l0 : ι := (eL.symm t.1).1
  have hl0 : l0 ∈ L := (eL.symm t.1).2
  let B : Finset ι :=
    (Finset.univ.image fun m : Fin d =>
      (eR.symm
        ⟨t.2.1 * d + m.1, by
          have hm : m.1 < d := m.2
          have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt t.2.2
          calc
            t.2.1 * d + m.1 < t.2.1 * d + d := by
              exact Nat.add_lt_add_left hm _
            _ = (t.2.1 + 1) * d := by
              rw [Nat.add_mul, Nat.one_mul]
            _ ≤ (R.card / d) * d := by
              exact Nat.mul_le_mul_right d hsucc
            _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).1)
  refine ⟨l0, hl0, B, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨m, -, hm⟩
    exact by
      rw [← hm]
      exact (eR.symm
        ⟨t.2.1 * d + m.1, by
          have hm' : m.1 < d := m.2
          have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt t.2.2
          calc
            t.2.1 * d + m.1 < t.2.1 * d + d := by
              exact Nat.add_lt_add_left hm' _
            _ = (t.2.1 + 1) * d := by
              rw [Nat.add_mul, Nat.one_mul]
            _ ≤ (R.card / d) * d := by
              exact Nat.mul_le_mul_right d hsucc
            _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).2
  · dsimp [B]
    exact le_trans Finset.card_image_le (by simp)
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
    rcases Finset.mem_filter.mp hA with ⟨_, hAt⟩
    let h := (mem_completeBipartiteLink_iff).1 A.2
    let l : ι := Classical.choose h
    have hl : l ∈ L := (Classical.choose_spec h).1
    let h' := (Classical.choose_spec h).2
    let rA : ι := Classical.choose h'
    have hrA : rA ∈ R := (Classical.choose_spec h').1
    have hpairA : A.1 = ({l, rA} : Finset ι) := (Classical.choose_spec h').2
    have hleftIdx :
        leftIndex (L := L) (R := R) eL A = eL ⟨l, hl⟩ := by
      simp [leftIndex, l]
    have hrightIdx :
        rightIndex (L := L) (R := R) eR A = eR ⟨rA, hrA⟩ := by
      simp [rightIndex, rA]
    have hfull : (rightIndex (L := L) (R := R) eR A).1 < (R.card / d) * d := by
      by_contra hnot
      simp [rightRemainderColoring, hnot] at hAt
    have hAt' := hAt
    simp only [rightRemainderColoring, hfull, ↓reduceDIte, Sum.inl.injEq] at hAt'
    have hlEqFin : leftIndex (L := L) (R := R) eL A = t.1 := by
      exact congrArg Prod.fst hAt'
    have hblockFin :
        ⟨(rightIndex (L := L) (R := R) eR A).1 / d,
          (Nat.div_lt_iff_lt_mul hd).2 hfull⟩ = t.2 := by
      exact congrArg Prod.snd hAt'
    have hblock :
        (rightIndex (L := L) (R := R) eR A).1 / d = t.2.1 := by
      exact congrArg Fin.val hblockFin
    have hlEqSub : ⟨l, hl⟩ = eL.symm t.1 := by
      apply eL.injective
      calc
        eL ⟨l, hl⟩ = leftIndex (L := L) (R := R) eL A := hleftIdx.symm
        _ = t.1 := hlEqFin
        _ = eL (eL.symm t.1) := by simp
    have hlEq : l = l0 := by
      exact congrArg Subtype.val hlEqSub
    let m : Fin d := ⟨(rightIndex (L := L) (R := R) eR A).1 % d,
      Nat.mod_lt _ hd⟩
    have hmIdx :
        t.2.1 * d + m.1 = (rightIndex (L := L) (R := R) eR A).1 := by
      calc
        t.2.1 * d + m.1
            = t.2.1 * d + ((rightIndex (L := L) (R := R) eR A).1 % d) := rfl
        _ = ((rightIndex (L := L) (R := R) eR A).1 / d) * d
              + ((rightIndex (L := L) (R := R) eR A).1 % d) := by
              rw [hblock]
        _ = (rightIndex (L := L) (R := R) eR A).1 := by
              simpa [Nat.add_comm, Nat.mul_comm] using
                (Nat.mod_add_div ((rightIndex (L := L) (R := R) eR A).1) d)
    have hrEqSub :
        eR.symm
          ⟨t.2.1 * d + m.1, by
            have hm' : m.1 < d := m.2
            have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt t.2.2
            calc
              t.2.1 * d + m.1 < t.2.1 * d + d := by
                exact Nat.add_lt_add_left hm' _
              _ = (t.2.1 + 1) * d := by
                rw [Nat.add_mul, Nat.one_mul]
              _ ≤ (R.card / d) * d := by
                exact Nat.mul_le_mul_right d hsucc
              _ ≤ R.card := Nat.div_mul_le_self R.card d⟩
        = ⟨rA, hrA⟩ := by
      apply eR.injective
      apply Fin.ext
      calc
        ↑(eR (eR.symm
            ⟨t.2.1 * d + m.1, by
              have hm' : m.1 < d := m.2
              have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt t.2.2
              calc
                t.2.1 * d + m.1 < t.2.1 * d + d := by
                  exact Nat.add_lt_add_left hm' _
                _ = (t.2.1 + 1) * d := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ ≤ (R.card / d) * d := by
                  exact Nat.mul_le_mul_right d hsucc
                _ ≤ R.card := Nat.div_mul_le_self R.card d⟩)) = t.2.1 * d + m.1 := by
              simp
        _ = (rightIndex (L := L) (R := R) eR A).1 := hmIdx
        _ = (eR ⟨rA, hrA⟩).1 := by
              simpa using congrArg Fin.val hrightIdx
    have hrEq :
        rA =
          (eR.symm
            ⟨t.2.1 * d + m.1, by
              have hm' : m.1 < d := m.2
              have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt t.2.2
              calc
                t.2.1 * d + m.1 < t.2.1 * d + d := by
                  exact Nat.add_lt_add_left hm' _
                _ = (t.2.1 + 1) * d := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ ≤ (R.card / d) * d := by
                  exact Nat.mul_le_mul_right d hsucc
                _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).1 := by
      exact (congrArg Subtype.val hrEqSub).symm
    have hrB : rA ∈ B := by
      refine Finset.mem_image.mpr ?_
      refine ⟨m, by simp, ?_⟩
      exact hrEq.symm
    refine (mem_completeBipartiteLink_iff).2 ?_
    refine ⟨l0, by simp, rA, hrB, ?_⟩
    calc
      S = A.1 := hAS.symm
      _ = ({l, rA} : Finset ι) := hpairA
      _ = ({l0, rA} : Finset ι) := by simp [hlEq]

lemma colorClass_rightRemainder_inr_subset
    (eL : ↥L ≃ Fin L.card)
    (eR : ↥R ≃ Fin R.card)
    (hd : 0 < d)
    (hrem : R.card % d ≤ L.card)
    (t : Fin (R.card % d)) :
    ∃ r : ι, r ∈ R ∧
      colorClass
        (completeBipartiteLink L R)
        (rightRemainderColoring (L := L) (R := R) eL eR hd hrem)
        (Sum.inr t)
      ⊆ completeBipartiteLink L ({r} : Finset ι) := by
  classical
  let j0 : Fin R.card :=
    ⟨(R.card / d) * d + t.1, by
      have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
      calc
        (R.card / d) * d + t.1 < (R.card / d) * d + (R.card % d) := by
          exact Nat.add_lt_add_left t.2 _
        _ = R.card := hqdr⟩
  refine ⟨(eR.symm j0).1, (eR.symm j0).2, ?_⟩
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
  rcases Finset.mem_filter.mp hA with ⟨hAatt, hAt⟩
  let h := (mem_completeBipartiteLink_iff).1 A.2
  let l : ι := Classical.choose h
  have hl : l ∈ L := (Classical.choose_spec h).1
  let h' := (Classical.choose_spec h).2
  let rA : ι := Classical.choose h'
  have hrA : rA ∈ R := (Classical.choose_spec h').1
  have hpairA : A.1 = ({l, rA} : Finset ι) := (Classical.choose_spec h').2
  have hidx :
      rightIndex (L := L) (R := R) eR A = eR ⟨rA, hrA⟩ := by
    simp [rightIndex, rA]
  have hnotfull : ¬ (rightIndex (L := L) (R := R) eR A).1 < (R.card / d) * d := by
    intro hfull
    simp [rightRemainderColoring, hfull] at hAt
  have hval :
      (rightIndex (L := L) (R := R) eR A).1 - (R.card / d) * d = t.1 := by
    have hAt' := hAt
    simp only [rightRemainderColoring, hnotfull, ↓reduceDIte, Sum.inr.injEq] at hAt'
    exact congrArg Fin.val hAt'
  have hge :
      (R.card / d) * d ≤ (rightIndex (L := L) (R := R) eR A).1 :=
    Nat.le_of_not_gt hnotfull
  have hjval :
      (rightIndex (L := L) (R := R) eR A).1 = (R.card / d) * d + t.1 := by
    simpa [Nat.add_comm] using (Nat.sub_eq_iff_eq_add hge).mp hval
  have hj0eq : rightIndex (L := L) (R := R) eR A = j0 := by
    apply Fin.ext
    simpa [j0] using hjval
  have hrEqSub : ⟨rA, hrA⟩ = eR.symm j0 := by
    apply eR.injective
    calc
      eR ⟨rA, hrA⟩ = rightIndex (L := L) (R := R) eR A := hidx.symm
      _ = j0 := hj0eq
      _ = eR (eR.symm j0) := by simp
  have hrEq : rA = (eR.symm j0).1 := by
    exact congrArg Subtype.val hrEqSub
  have hSin :
      S ∈ completeBipartiteLink L ({(eR.symm j0).1} : Finset ι) := by
    refine (mem_completeBipartiteLink_iff).2 ?_
    refine ⟨l, hl, (eR.symm j0).1, by simp, ?_⟩
    calc
      S = A.1 := hAS.symm
      _ = ({l, rA} : Finset ι) := hpairA
      _ = ({l, (eR.symm j0).1} : Finset ι) := by
            simp [hrEq]
  exact hSin

theorem chiPackLe_completeBipartite_smallSide_upper_rightRemainder
    (hLR : Disjoint L R)
    (_ : L.card ≤ R.card)
    (hd : 0 < d) (hsmall : L.card < d)
    (hrem : R.card % d ≤ L.card) :
    ChiPackLinkLe
      (completeBipartiteLink L R)
      (fun _ => d)
      (L.card * (R.card / d) + R.card % d) := by
  classical
  let eL : ↥L ≃ Fin L.card := by
    simpa using (Fintype.equivFin ↥L)
  let eR : ↥R ≃ Fin R.card := by
    simpa using (Fintype.equivFin ↥R)
  let color :=
    rightRemainderColoring (L := L) (R := R) eL eR hd hrem
  refine chiPackLe_of_fintypeColoring
    (G := completeBipartiteLink L R)
    (cap := fun _ => d)
    (κ := RightRemainderColor L.card (R.card / d) (R.card % d))
    (k := L.card * (R.card / d) + R.card % d)
    (color := color)
    ?_ ?_
  · exact card_rightRemainderColor L.card (R.card / d) (R.card % d)
  · intro t
    cases t with
    | inl t =>
        rcases colorClass_rightRemainder_inl_subset
            (L := L) (R := R) eL eR hd hrem t with
          ⟨l, hl, B, hBR, hBcard, hsub⟩
        have hlR : l ∉ B := by
          intro hlB
          have : l ∈ R := hBR hlB
          exact (Finset.disjoint_left.mp hLR) hl this
        exact perfectlyPackable_subset_singleton_left_completeBipartite
          (d := d) hd hlR hsub hBcard
    | inr t =>
        rcases colorClass_rightRemainder_inr_subset
            (L := L) (R := R) eL eR hd hrem t with
          ⟨r, hr, hsub⟩
        have hrL : r ∉ L := by
          intro hrL'
          exact (Finset.disjoint_left.mp hLR) hrL' hr
        exact perfectlyPackable_subset_singleton_right_completeBipartite
          (d := d) hd hrL hsub (Nat.le_of_lt hsmall)

noncomputable def leftRemainderColoring
    (eL : ↥L ≃ Fin L.card)
    (eR : ↥R ≃ Fin R.card)
    (hd : 0 < d) :
    Member (completeBipartiteLink L R) →
      LeftRemainderColor L.card (R.card / d) := by
  classical
  intro A
  let i := leftIndex (L := L) (R := R) eL A
  let j := rightIndex (L := L) (R := R) eR A
  refine ⟨i, ?_⟩
  by_cases hfull : j.1 < (R.card / d) * d
  · exact ⟨j.1 / d, Nat.lt_succ_of_lt ((Nat.div_lt_iff_lt_mul hd).2 hfull)⟩
  · exact ⟨R.card / d, by simp⟩

lemma colorClass_leftRemainder_subset
    (eL : ↥L ≃ Fin L.card)
    (eR : ↥R ≃ Fin R.card)
    (hd : 0 < d)
    (t : LeftRemainderColor L.card (R.card / d)) :
    ∃ l : ι, l ∈ L ∧
      ∃ B : Finset ι, B ⊆ R ∧ B.card ≤ d ∧
        colorClass
          (completeBipartiteLink L R)
          (leftRemainderColoring (L := L) (R := R) eL eR hd)
          t
        ⊆ completeBipartiteLink ({l} : Finset ι) B := by
  classical
  by_cases hfullT : t.2.1 < R.card / d
  · let l0 : ι := (eL.symm t.1).1
    have hl0 : l0 ∈ L := (eL.symm t.1).2
    let B : Finset ι :=
      (Finset.univ.image fun m : Fin d =>
        (eR.symm
          ⟨t.2.1 * d + m.1, by
            have hm : m.1 < d := m.2
            have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt hfullT
            calc
              t.2.1 * d + m.1 < t.2.1 * d + d := by
                exact Nat.add_lt_add_left hm _
              _ = (t.2.1 + 1) * d := by
                rw [Nat.add_mul, Nat.one_mul]
              _ ≤ (R.card / d) * d := by
                exact Nat.mul_le_mul_right d hsucc
              _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).1)
    refine ⟨l0, hl0, B, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨m, -, hm⟩
      rw [← hm]
      exact
        (eR.symm
          ⟨t.2.1 * d + m.1, by
            have hm' : m.1 < d := m.2
            have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt hfullT
            calc
              t.2.1 * d + m.1 < t.2.1 * d + d := by
                exact Nat.add_lt_add_left hm' _
              _ = (t.2.1 + 1) * d := by
                rw [Nat.add_mul, Nat.one_mul]
              _ ≤ (R.card / d) * d := by
                exact Nat.mul_le_mul_right d hsucc
              _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).2
    · dsimp [B]
      exact le_trans Finset.card_image_le (by simp)
    · intro S hS
      rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
      rcases Finset.mem_filter.mp hA with ⟨_, hAt⟩
      let h := (mem_completeBipartiteLink_iff).1 A.2
      let l : ι := Classical.choose h
      have hl : l ∈ L := (Classical.choose_spec h).1
      let h' := (Classical.choose_spec h).2
      let rA : ι := Classical.choose h'
      have hrA : rA ∈ R := (Classical.choose_spec h').1
      have hpairA : A.1 = ({l, rA} : Finset ι) := (Classical.choose_spec h').2
      have hleftIdx :
          leftIndex (L := L) (R := R) eL A = eL ⟨l, hl⟩ := by
        simp [leftIndex, l]
      have hrightIdx :
          rightIndex (L := L) (R := R) eR A = eR ⟨rA, hrA⟩ := by
        simp [rightIndex, rA]
      have hfullA :
          (rightIndex (L := L) (R := R) eR A).1 < (R.card / d) * d := by
        by_contra hnot
        have hAt' := hAt
        simp only [leftRemainderColoring, hnot, ↓reduceDIte] at hAt'
        have hEqBlock : ⟨R.card / d, by simp⟩ = t.2 := by
          exact congrArg Prod.snd hAt'
        have hEqVal : R.card / d = t.2.1 := by
          exact congrArg Fin.val hEqBlock
        exact (Nat.ne_of_lt hfullT) hEqVal.symm
      have hAt' := hAt
      simp only [leftRemainderColoring, hfullA, ↓reduceDIte] at hAt'
      have hlEqFin : leftIndex (L := L) (R := R) eL A = t.1 := by
        exact congrArg Prod.fst hAt'
      have hblockFin :
          ⟨(rightIndex (L := L) (R := R) eR A).1 / d,
            Nat.lt_succ_of_lt ((Nat.div_lt_iff_lt_mul hd).2 hfullA)⟩ = t.2 := by
        exact congrArg Prod.snd hAt'
      have hblock :
          (rightIndex (L := L) (R := R) eR A).1 / d = t.2.1 := by
        exact congrArg Fin.val hblockFin
      have hlEqSub : ⟨l, hl⟩ = eL.symm t.1 := by
        apply eL.injective
        calc
          eL ⟨l, hl⟩ = leftIndex (L := L) (R := R) eL A := hleftIdx.symm
          _ = t.1 := hlEqFin
          _ = eL (eL.symm t.1) := by simp
      have hlEq : l = l0 := by
        exact congrArg Subtype.val hlEqSub
      let m : Fin d :=
        ⟨(rightIndex (L := L) (R := R) eR A).1 % d, Nat.mod_lt _ hd⟩
      have hmIdx :
          t.2.1 * d + m.1 = (rightIndex (L := L) (R := R) eR A).1 := by
        calc
          t.2.1 * d + m.1
              = t.2.1 * d + ((rightIndex (L := L) (R := R) eR A).1 % d) := rfl
          _ = ((rightIndex (L := L) (R := R) eR A).1 / d) * d
                + ((rightIndex (L := L) (R := R) eR A).1 % d) := by
                rw [hblock]
          _ = (rightIndex (L := L) (R := R) eR A).1 := by
                simpa [Nat.add_comm, Nat.mul_comm] using
                  (Nat.mod_add_div ((rightIndex (L := L) (R := R) eR A).1) d)
      have hrEqSub :
          eR.symm
            ⟨t.2.1 * d + m.1, by
              have hm' : m.1 < d := m.2
              have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt hfullT
              calc
                t.2.1 * d + m.1 < t.2.1 * d + d := by
                  exact Nat.add_lt_add_left hm' _
                _ = (t.2.1 + 1) * d := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ ≤ (R.card / d) * d := by
                  exact Nat.mul_le_mul_right d hsucc
                _ ≤ R.card := Nat.div_mul_le_self R.card d⟩
          = ⟨rA, hrA⟩ := by
        apply eR.injective
        apply Fin.ext
        calc
          ↑(eR (eR.symm
              ⟨t.2.1 * d + m.1, by
                have hm' : m.1 < d := m.2
                have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt hfullT
                calc
                  t.2.1 * d + m.1 < t.2.1 * d + d := by
                    exact Nat.add_lt_add_left hm' _
                  _ = (t.2.1 + 1) * d := by
                    rw [Nat.add_mul, Nat.one_mul]
                  _ ≤ (R.card / d) * d := by
                    exact Nat.mul_le_mul_right d hsucc
                  _ ≤ R.card := Nat.div_mul_le_self R.card d⟩)) = t.2.1 * d + m.1 := by
                simp
          _ = (rightIndex (L := L) (R := R) eR A).1 := hmIdx
          _ = (eR ⟨rA, hrA⟩).1 := by
                simpa using congrArg Fin.val hrightIdx
      have hrEq :
          rA =
            (eR.symm
              ⟨t.2.1 * d + m.1, by
                have hm' : m.1 < d := m.2
                have hsucc : t.2.1 + 1 ≤ R.card / d := Nat.succ_le_of_lt hfullT
                calc
                  t.2.1 * d + m.1 < t.2.1 * d + d := by
                    exact Nat.add_lt_add_left hm' _
                  _ = (t.2.1 + 1) * d := by
                    rw [Nat.add_mul, Nat.one_mul]
                  _ ≤ (R.card / d) * d := by
                    exact Nat.mul_le_mul_right d hsucc
                  _ ≤ R.card := Nat.div_mul_le_self R.card d⟩).1 := by
        exact (congrArg Subtype.val hrEqSub).symm
      have hrB : rA ∈ B := by
        refine Finset.mem_image.mpr ?_
        refine ⟨m, by simp, ?_⟩
        exact hrEq.symm
      refine (mem_completeBipartiteLink_iff).2 ?_
      refine ⟨l0, by simp, rA, hrB, ?_⟩
      calc
        S = A.1 := hAS.symm
        _ = ({l, rA} : Finset ι) := hpairA
        _ = ({l0, rA} : Finset ι) := by simp [hlEq]
  · have hqeq : t.2.1 = R.card / d := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp t.2.2
      · exact Nat.le_of_not_gt hfullT
    let l0 : ι := (eL.symm t.1).1
    have hl0 : l0 ∈ L := (eL.symm t.1).2
    let B : Finset ι :=
      (Finset.univ.image fun m : Fin (R.card % d) =>
        (eR.symm
          ⟨(R.card / d) * d + m.1, by
            have hm : m.1 < R.card % d := m.2
            have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
              simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
            calc
              (R.card / d) * d + m.1 < (R.card / d) * d + (R.card % d) := by
                exact Nat.add_lt_add_left hm _
              _ = R.card := hqdr⟩).1)
    refine ⟨l0, hl0, B, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨m, -, hm⟩
      rw [← hm]
      exact
        (eR.symm
          ⟨(R.card / d) * d + m.1, by
            have hm' : m.1 < R.card % d := m.2
            have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
              simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
            calc
              (R.card / d) * d + m.1 < (R.card / d) * d + (R.card % d) := by
                exact Nat.add_lt_add_left hm' _
              _ = R.card := hqdr⟩).2
    · dsimp [B]
      have h1 : B.card ≤ R.card % d := by
        exact le_trans Finset.card_image_le (by simp)
      exact le_trans h1 (Nat.le_of_lt (Nat.mod_lt _ hd))
    · intro S hS
      rcases Finset.mem_image.mp hS with ⟨A, hA, hAS⟩
      rcases Finset.mem_filter.mp hA with ⟨_, hAt⟩
      let h := (mem_completeBipartiteLink_iff).1 A.2
      let l : ι := Classical.choose h
      have hl : l ∈ L := (Classical.choose_spec h).1
      let h' := (Classical.choose_spec h).2
      let rA : ι := Classical.choose h'
      have hrA : rA ∈ R := (Classical.choose_spec h').1
      have hpairA : A.1 = ({l, rA} : Finset ι) := (Classical.choose_spec h').2
      have hleftIdx :
          leftIndex (L := L) (R := R) eL A = eL ⟨l, hl⟩ := by
        simp [leftIndex, l]
      have hrightIdx :
          rightIndex (L := L) (R := R) eR A = eR ⟨rA, hrA⟩ := by
        simp [rightIndex, rA]
      have hnotfullA :
          ¬ (rightIndex (L := L) (R := R) eR A).1 < (R.card / d) * d := by
        intro hfullA
        have hAt' := hAt
        simp only [leftRemainderColoring, hfullA, ↓reduceDIte] at hAt'
        have hEqBlock :
            ⟨(rightIndex (L := L) (R := R) eR A).1 / d,
              Nat.lt_succ_of_lt ((Nat.div_lt_iff_lt_mul hd).2 hfullA)⟩ = t.2 := by
          exact congrArg Prod.snd hAt'
        have hEqVal :
            (rightIndex (L := L) (R := R) eR A).1 / d = t.2.1 := by
          exact congrArg Fin.val hEqBlock
        exact (Nat.ne_of_lt ((Nat.div_lt_iff_lt_mul hd).2 hfullA)) (hEqVal.trans hqeq)
      have hAt' := hAt
      simp only [leftRemainderColoring, hnotfullA, ↓reduceDIte] at hAt'
      have hlEqFin : leftIndex (L := L) (R := R) eL A = t.1 := by
        exact congrArg Prod.fst hAt'
      have hlEqSub : ⟨l, hl⟩ = eL.symm t.1 := by
        apply eL.injective
        calc
          eL ⟨l, hl⟩ = leftIndex (L := L) (R := R) eL A := hleftIdx.symm
          _ = t.1 := hlEqFin
          _ = eL (eL.symm t.1) := by simp
      have hlEq : l = l0 := by
        exact congrArg Subtype.val hlEqSub
      have hge :
          (R.card / d) * d ≤ (rightIndex (L := L) (R := R) eR A).1 :=
        Nat.le_of_not_gt hnotfullA
      let m : Fin (R.card % d) :=
        ⟨(rightIndex (L := L) (R := R) eR A).1 - (R.card / d) * d, by
          have hjlt : (rightIndex (L := L) (R := R) eR A).1 < R.card :=
            (rightIndex (L := L) (R := R) eR A).2
          have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
          have hltrem :
              (rightIndex (L := L) (R := R) eR A).1 - (R.card / d) * d < R.card % d := by
            apply Nat.sub_lt_left_of_lt_add hge
            simp [hqdr]
          exact hltrem⟩
      have hmIdx :
          (R.card / d) * d + m.1 = (rightIndex (L := L) (R := R) eR A).1 := by
        have hmIdx' :
            (rightIndex (L := L) (R := R) eR A).1 =
              m.1 + (R.card / d) * d := by
          dsimp [m]
          exact (Nat.sub_eq_iff_eq_add hge).mp rfl
        simpa [Nat.add_comm] using hmIdx'.symm
      have hrEqSub :
          eR.symm
            ⟨(R.card / d) * d + m.1, by
              have hm' : m.1 < R.card % d := m.2
              have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
                simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
              calc
                (R.card / d) * d + m.1 < (R.card / d) * d + (R.card % d) := by
                  exact Nat.add_lt_add_left hm' _
                _ = R.card := hqdr⟩
          = ⟨rA, hrA⟩ := by
        apply eR.injective
        apply Fin.ext
        calc
          ↑(eR (eR.symm
              ⟨(R.card / d) * d + m.1, by
                have hm' : m.1 < R.card % d := m.2
                have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
                  simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
                calc
                  (R.card / d) * d + m.1 < (R.card / d) * d + (R.card % d) := by
                    exact Nat.add_lt_add_left hm' _
                  _ = R.card := hqdr⟩)) = (R.card / d) * d + m.1 := by
                simp
          _ = (rightIndex (L := L) (R := R) eR A).1 := hmIdx
          _ = (eR ⟨rA, hrA⟩).1 := by
                simpa using congrArg Fin.val hrightIdx
      have hrEq :
          rA =
            (eR.symm
              ⟨(R.card / d) * d + m.1, by
                have hm' : m.1 < R.card % d := m.2
                have hqdr : (R.card / d) * d + (R.card % d) = R.card := by
                  simpa [Nat.mul_comm] using (Nat.div_add_mod R.card d)
                calc
                  (R.card / d) * d + m.1 < (R.card / d) * d + (R.card % d) := by
                    exact Nat.add_lt_add_left hm' _
                  _ = R.card := hqdr⟩).1 := by
        exact (congrArg Subtype.val hrEqSub).symm
      have hrB : rA ∈ B := by
        refine Finset.mem_image.mpr ?_
        refine ⟨m, by simp, ?_⟩
        exact hrEq.symm
      refine (mem_completeBipartiteLink_iff).2 ?_
      refine ⟨l0, by simp, rA, hrB, ?_⟩
      calc
        S = A.1 := hAS.symm
        _ = ({l, rA} : Finset ι) := hpairA
        _ = ({l0, rA} : Finset ι) := by simp [hlEq]

/-- Upper-bound construction, remainder covered by left-star colors. -/
theorem chiPackLe_completeBipartite_smallSide_upper_leftRemainder
    (hLR : Disjoint L R)
    (_ : L.card ≤ R.card)
    (hd : 0 < d) (_ : L.card < d)
    (_ : L.card ≤ R.card % d) :
    ChiPackLinkLe
      (completeBipartiteLink L R)
      (fun _ => d)
      (L.card * (R.card / d) + L.card) := by
  classical
  let eL : ↥L ≃ Fin L.card := by
    simpa using (Fintype.equivFin ↥L)
  let eR : ↥R ≃ Fin R.card := by
    simpa using (Fintype.equivFin ↥R)
  let color :=
    leftRemainderColoring (L := L) (R := R) eL eR hd
  refine chiPackLe_of_fintypeColoring
    (G := completeBipartiteLink L R)
    (cap := fun _ => d)
    (κ := LeftRemainderColor L.card (R.card / d))
    (k := L.card * (R.card / d) + L.card)
    (color := color)
    ?_ ?_
  · exact card_leftRemainderColor L.card (R.card / d)
  · intro t
    rcases colorClass_leftRemainder_subset
        (L := L) (R := R) eL eR hd t with
      ⟨l, hl, B, hBR, hBcard, hsub⟩
    have hlR : l ∉ B := by
      intro hlB
      have : l ∈ R := hBR hlB
      exact (Finset.disjoint_left.mp hLR) hl this
    exact perfectlyPackable_subset_singleton_left_completeBipartite
      (d := d) hd hlR hsub hBcard

theorem chiPackLe_completeBipartite_smallSide_upper
    (hLR : Disjoint L R)
    (hcard : L.card ≤ R.card)
    (hd : 0 < d) (hsmall : L.card < d) :
    ChiPackLinkLe
      (completeBipartiteLink L R)
      (fun _ => d)
      (bipartiteSmallSideValue L.card R.card d) := by
  by_cases hrem : R.card % d ≤ L.card
  · simpa [bipartiteSmallSideValue_eq_rightRemainder hrem] using
      chiPackLe_completeBipartite_smallSide_upper_rightRemainder
        (L := L) (R := R) hLR hcard hd hsmall hrem
  · have hrem' : L.card ≤ R.card % d := Nat.le_of_not_ge hrem
    simpa [bipartiteSmallSideValue_eq_leftRemainder hrem'] using
      chiPackLe_completeBipartite_smallSide_upper_leftRemainder
        (L := L) (R := R) hLR hcard hd hsmall hrem'

theorem chiPackLink_completeBipartite_smallSide_eq
    (hLR : Disjoint L R)
    (hcard : L.card ≤ R.card)
    (hd : 0 < d) (hsmall : L.card < d) :
    chiPackLink
        (completeBipartiteLink L R)
        (fun _ => d)
        (fun _ => hd) =
      bipartiteSmallSideValue L.card R.card d := by
  apply le_antisymm
  · apply chiPackLink_le_of
      (G := completeBipartiteLink L R)
      (cap := fun _ => d)
      (hcap := fun _ => hd)
    exact
      chiPackLe_completeBipartite_smallSide_upper
        (L := L) (R := R) hLR hcard hd hsmall
  · exact
      chiPackLe_completeBipartite_smallSide_lower
        (L := L) (R := R) hLR hcard hd hsmall
        (k := chiPackLink
          (completeBipartiteLink L R)
          (fun _ => d)
          (fun _ => hd))
        (chiPackLink_spec
          (G := completeBipartiteLink L R)
          (cap := fun _ => d)
          (hcap := fun _ => hd))

end BipartiteExact

end Erdos278
