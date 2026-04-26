# Erdős Problem #278 and companions — corrected frontier note v10

**Date:** April 25, 2026  
**Status:** Paper-worthy, but the paper must be reframed. The stable core is **squarefree congruence packing via common-core graph links**. Several weighted results from v8/v9 are still useful as **packable-subgraph optimization**, but they should not be advertised as full #278 maximum-density theorems without additional layer-union upper bounds.

---

## 0. Why v10 exists

The v9 frontier note promoted a star-triangle / separator-interface framework for weighted common-core graph links. That framework is still valuable, but a new critical pass found two serious issues:

1. **Packable-subgraph optimization was being conflated with full #278 maximum coverage.** In #278, overlapping non-packable cylinders may still add union measure. Thus the weighted graph-link objective must be distinguished from the true union-measure objective.
2. **The nonuniform clique-link \(n-2\) criterion was wrong as stated.** It used a two-vertex deletion and \(c_i-2\). The actual one-triangle-plus-stars construction uses three triangle vertices and star centers with base load \(3\), hence \(b_i-3\).

This correction is significant but not catastrophic. The project remains paper-worthy because the squarefree packing theory, common-core graph-link framework, and star-triangle normal form are still coherent and reusable.

---

## 1. Public context

Erdős #278 asks for the maximum density covered by a finite family of prescribed congruence moduli. The minimum-density side is known by the aligned-residue inclusion-exclusion construction; the maximum side is open.

Erdős #202 and #1190 concern disjoint congruence classes and reciprocal mass of disjoint systems. The packability side of this project remains directly relevant to those problems.

Cambie's 2025 note gives external support for the strategic view that #278 should not be expected to have a single clean universal formula. The right target remains exact structural families and finite mechanisms.

---

## 2. Stable core framework

### 2.1 Squarefree cylinder model

For squarefree
\[
Q=\prod_i p_i,
\]
work in
\[
X=\prod_i\Omega_i.
\]
A squarefree modulus
\[
n_S=\prod_{i\in S}p_i
\]
becomes an \(S\)-cylinder
\[
C_S(a)=\{x:x_i=a_i\text{ for all }i\in S\}
\]
with density
\[
\mu(C_S)=1/n_S.
\]

### 2.2 Singleton residual-box reduction

Singleton supports reduce maximum coverage to a residual box with coordinate sizes
\[
d_i=p_i-1\quad\text{or}\quad p_i.
\]
This remains a valid maximum-coverage tool, not a perfect-packing theorem by itself.

### 2.3 Perfect packing

A support family is perfectly packable iff it admits intersection-separating local patterns:
\[
a_S|_{S\cap T}\ne a_T|_{S\cap T}
\]
for all distinct supports \(S,T\). If a whole family is perfectly packable, then it gives an exact #278 maximum for that family because the union bound is attained.

### 2.4 Common-core graph links

For
\[
\mathcal H=C*\mathcal L,
\]
with petal supports disjoint from the core, let
\[
D_C=\prod_{i\in C}d_i.
\]
Then
\[
C*\mathcal L\text{ perfectly packable}\iff \chi_{\mathrm{pack}}(\mathcal L)\le D_C.
\]
When \(\mathcal L\) is a graph \(G\), this becomes the graph-link invariant \(\chi_d(G)\).

---

## 3. Stable packability results

The following remain in the stable bucket:

- pair-support theorem: pair supports are packable iff matching number \(\le1\) and local degrees fit capacities;
- common-core theorem;
- star formula \(\chi_d(K_{1,r})=\lceil r/d\rceil\);
- complete bipartite packability formula, with Lean currently covering the small-side regime;
- uniform clique-link theorem for \(d\ge3\), as a project-level theorem not yet Lean-formalized;
- binary clique-link formula, likewise project-level;
- star-triangle normal form for arbitrary graph-link \(\chi_d(F)\).

---

## 4. Corrected clique-link nonuniform theorem

The v9 theorem deleted two vertices and used capacities \(c_i-2\). This is false: for example, it would incorrectly imply \(\chi_3(K_5)=3\), contradicting the volume lower bound \(\lceil10/3\rceil=4\).

The corrected construction is:

- choose a triangle \(x,y,z\) with capacities at least \(2\);
- every other vertex is a star center;
- a star center \(v\) must cover the three edges from \(v\) to the triangle, plus assigned edges to other star centers.

So the tournament capacity is
\[
outdeg(v)\le d_v-3.
\]
After sorting the star-center capacities as
\[
b_1\le\cdots\le b_{n-3},
\]
the relevant prefix condition is
\[
\sum_{i=1}^k(b_i-3)\ge\binom{k}{2}
\qquad(1\le k\le n-3).
\]

The arithmetic clique-link theorem is probably salvageable, but its proof must delete three small capacities rather than two and should include small-case checks.

---

## 5. Weighted / algorithmic results after correction

The star-triangle normal form remains correct:
\[
\chi_d(F)=
\min_{\mathcal T,\vec H}
\left(
|\mathcal T|+
\sum_v\left\lceil\frac{m_v}{d_v}\right\rceil
\right),
\]
where \(\mathcal T\) is a set of edge-disjoint admissible triangles and \(\vec H\) orients the remaining edges.

But the objective it controls is the packable-subgraph objective
\[
P_t(G)=\max\{w(F):F\subseteq E(G),\chi_d(F)\le t\},
\]
not the full #278 maximum coverage objective.

Stable algorithmic consequences for \(P_t\):

1. fixed-budget exact XP algorithm by enumerating triangle colors and packet counts, then solving a max-flow / capacitated incidence assignment;
2. fixed-treewidth DP schema for \(P_t\);
3. tree and triangle-free special cases as simplified orientation-cost problems.

These are useful for disjoint constructions and lower bounds, but should not be called exact #278 maximum theorems.

---

## 6. Main demotion: packable-subgraph does not equal full union maximum

A one-layer \(K_4\) shows the problem.

With uniform coordinate size \(p\), the packable one-layer optimum has value
\[
3p^{-2},
\]
because one intersecting edge family in \(K_4\) has at most three edges.

But assigning distinct local labels to the incident edges at each vertex lets all adjacent edge-cylinders be disjoint. The six edge cylinders then have union measure
\[
6p^{-2}-3p^{-4},
\]
which is strictly larger than \(3p^{-2}\). Thus overlapping but non-packable supports can still improve #278 maximum coverage.

This invalidates the old phrasing that weighted clique/bipartite graph-link optimization gave exact #278 maxima in those non-perfect regimes.

---

## 7. New true maximum-coverage frontier

Define \(U_d(H)\) to be the true one-layer union optimum for a graph \(H\): choose one pair-cylinder for every edge of \(H\), maximizing union measure.

For common-core graph links with budget \(t=D_C\), the full union problem becomes a layer partition problem:
\[
E(G)=E_1\sqcup\cdots\sqcup E_t,
\]
with contribution
\[
\sum_r U_d(G[E_r])
\]
up to the core-density factor.

The key one-layer combinatorics is local consistency: an intersection of edge-cylinders is nonempty iff all selected edge labels are locally consistent at every vertex.

In the full-capacity regime \(d_v\ge\deg_H(v)\), assigning distinct labels to incident edges gives the lower bound
\[
U_d(H)\ge
\sum_{\emptyset\ne M\text{ matching in }H}
(-1)^{|M|+1}
\prod_{v\in V(M)}\frac1{d_v}.
\]

The best next theorem target is:

> Prove or refute that this proper-local-label construction is optimal for \(U_d(H)\) in the full-capacity one-layer regime.

---

## 8. Paper-worthiness after correction

Paper-worthiness remains. The paper is no longer accurately described as "exact weighted #278 maximum formulas beyond packing." It should instead be:

> **Squarefree congruence packing via common-core graph links, plus packable-subgraph optimization and the layer-union bridge to full #278 maximum coverage.**

This is still one paper, not a new separate project, but it requires reorganization.

---

## 9. Current recommended paper outline

1. Public context and why no universal formula should be expected.
2. Squarefree product-space cylinder model.
3. Perfect packing and intersection-separating patterns.
4. Pair supports and common-core theorem.
5. Graph-link invariant \(\chi_d(G)\).
6. Stable packability families: stars, complete bipartite links, clique links.
7. Corrected nonuniform clique-link criterion and arithmetic clique-link corollary.
8. Star-triangle normal form for \(\chi_d(F)\).
9. Packable-subgraph optimization \(P_t(G)\): fixed-budget and fixed-treewidth exact algorithms.
10. Why \(P_t\) is not full #278 maximum: the \(K_4\) one-layer example.
11. True layer-union objective \(U_d(H)\) and matching-polynomial lower bound.
12. Lean formalization status and roadmap.

---

## 10. Current best next targets

1. Patch the paper and repo to remove overclaims.
2. Stabilize the corrected nonuniform clique-link proof.
3. Develop the one-layer union objective \(U_d(H)\).
4. Formalize the stable packing spine and star-triangle normal form.
5. Only after that, return to bounded-capacity weighted \(K_{a,b}\), now clearly as packable-subgraph optimization unless a layer-union theorem is proved.

---

## References

- T. F. Bloom, Erdős Problem #278, https://www.erdosproblems.com/278, accessed 2026-04-25.
- T. F. Bloom, Erdős Problem #202, https://www.erdosproblems.com/202, accessed 2026-04-25.
- T. F. Bloom, Erdős Problem #1190, https://www.erdosproblems.com/1190, accessed 2026-04-25.
- S. Cambie, *Proving it is impossible; on Erdős problem #278*, arXiv:2508.18270, 2025.
- H. G. Landau, *On dominance relations and the structure of animal societies: III. The condition for a score structure*, Bull. Math. Biophys. 15 (1953), 143-148.
