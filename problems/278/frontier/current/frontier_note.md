# Erdős Problem #278 and companions — latest frontier note (v9)

**Date:** April 18, 2026  
**Status:** Still not a full solution to #278. The project remains clearly paper-worthy, and the main change since v8 is a shift from explicit formulas on a few dense families to a more general **star–triangle / separator-interface exact-solvability framework** for weighted common-core graph links.

---

## 0. Purpose of this note

This note updates the previous v8 frontier note. It is meant to be usable by a fresh, skeptical reader starting from the public problem pages for Erdős #278, #202, and #1190.

It records:

1. the public problem context;
2. the squarefree / common-core graph-link framework;
3. the exact theorems consolidated through v8;
4. the new post-v8 conceptual consolidation;
5. the new exact algorithmic families that now look genuinely solid;
6. the parameterized extensions that look promising but are **not yet fully consolidated**;
7. the current best next targets.

**Gap from v8.** This is still **more material for the current paper**, not a different paper. The center of gravity has not changed, but the paper now wants a stronger algorithmic section: exact solvability via local star–triangle structure and separator signatures.

---

## 1. Public context

### 1.1 Erdős #278

Problem #278 asks:

> Let \(A=\{n_1<\cdots<n_r\}\) be a finite set of positive integers. What is the maximum density of integers covered by a suitable choice of congruences \(a_i \pmod{n_i}\)?

It also asks whether the minimum density is achieved when all residues are aligned. The public problem page records that the minimum side is settled by the inclusion–exclusion lower bound, so the live side is the **maximum** covered density. [P278]

### 1.2 Erdős #202

Problem #202 asks how large a pairwise-disjoint congruence system with distinct moduli \(n_i\le N\) can be. [P202]

### 1.3 Erdős #1190

Problem #1190 asks for the maximum of \(\sum 1/n_i\) over finite disjoint congruence systems with all \(n_i>m\). [P1190]

### 1.4 Strategic interpretation

The project remains best understood as a finite structural theory for exact local disjointness and weighted near-disjointness in squarefree families. That theory is directly relevant to the disjointness phenomena underlying #202 and #1190, while still organized around the actual maximum-density problem in #278.

---

## 2. Core framework carried from v8

### 2.1 Squarefree product-space model

Let
\[
Q=\prod_{i=1}^d p_i
\]
be squarefree. Work in the product space
\[
X=\prod_{i=1}^d \Omega_i,
\]
where initially \(|\Omega_i|=p_i\), and after singleton reduction a coordinate may shrink to \(p_i-1\).

A squarefree modulus
\[
n_S=\prod_{i\in S} p_i
\]
corresponds to an \(S\)-cylinder
\[
C_S(a)=\{x\in X:x_i=a_i \text{ for all } i\in S\},
\]
with density
\[
\mu(C_S)=\prod_{i\in S}\frac1{p_i}=\frac1{n_S}.
\]

### 2.2 Singleton residual-box reduction

If singleton supports \(\{i\}\) are present for \(i\in T\), choose those cylinders first. Then everything outside the residual box
\[
R_T=\{x_i\neq 0 \text{ for all } i\in T\}
\]
is already covered, and the residual coordinate sizes become
\[
d_i=
\begin{cases}
p_i-1,& i\in T,\\
p_i,& i\notin T.
\end{cases}
\]

For maximum coverage, higher-rank cylinders may then be chosen inside \(R_T\).

### 2.3 Perfect packing and common-core graph links

A support family \(\mathcal H\) is perfectly packable iff one can assign patterns that are pairwise intersection-separating on overlaps.

If every support contains a fixed core \(C\), write
\[
\mathcal H=C*\mathcal L=\{C\cup L:L\in\mathcal L\}.
\]
Let
\[
D_C=\prod_{i\in C} d_i
\]
be the number of available core patterns.

When \(\mathcal L\) is a graph \(G\), the main invariant is
\[
\chi_d(G),
\]
the minimum number of colors needed to partition \(E(G)\) into packable pair-support classes. Then
\[
C*G \text{ is perfectly packable } \iff \chi_d(G)\le D_C.
\]

This remains the project’s main operational reduction.

---

## 3. Consolidated exact results already in hand

This section collects the pieces that were already consolidated by v8 and still stand.

### 3.1 Packability side

- pair-support theorem;
- common-core theorem;
- exact \(\chi_d\) formulas for stars;
- exact \(\chi_d\) formulas for complete bipartite links;
- exact \(\chi_2(K_n)\);
- exact \(\chi_d(K_n)=\max(\lceil \binom n2/d\rceil,n-2)\) for all \(d\ge 3\);
- exact nonuniform clique-link \(n-2\) criterion via the Landau-type prefix inequalities;
- arithmetic clique-link theorem:
  \[
  \chi_{(d_i)}(K_n)=n-2
  \]
  for actual prime-based residual capacities after the capacity-1 collapse issue is removed, hence perfect packability iff
  \[
  D_C\ge n-2.
  \]

### 3.2 Weighted side through v8

- clique-link threshold theorem for \(0\le t\le n-4\);
- clique-link near-threshold theorem at \(t=n-3\), with the exact “omit a light triangle vs. omit a light 3-edge star” dichotomy;
- the full-clique regime for \(t\ge n-2\);
- triangle-free full-capacity reduction to weighted \(t\)-vertex edge coverage;
- exact weighted full-capacity \(K_{a,b}\);
- exact weighted one-sided-full \(K_{a,b}\);
- exact weighted arbitrary bipartite one-full-side theorem.

These remain the baseline from which the new v9 step-back proceeds.

---

## 4. New conceptual consolidation after v8

The main post-v8 progress is conceptual before it is classificatory.

### 4.1 Star–triangle normal form

For a simple graph \(F\), every intersecting family of edges is either:

1. a star; or
2. a triangle.

Therefore the minimum star/triangle cost of \(F\) is
\[
\boxed{
\chi_d(F)=
\min_{\mathcal T,\ \vec H}
\left(
|\mathcal T|+\sum_{v\in V(F)}\left\lceil\frac{m_v}{d_v}\right\rceil
\right),
}
\]
where

- \(\mathcal T\) ranges over sets of edge-disjoint triangles of \(F\);
- \(H:=F\setminus \bigcup_{T\in\mathcal T}E(T)\);
- \(\vec H\) ranges over orientations of \(H\);
- \(m_v\) is the indegree of \(v\) in \(\vec H\).

#### Why this is exact

- Any decomposition of \(E(F)\) into intersecting families splits uniquely into triangle colors and star colors.
- Remove the triangle colors. In the remaining graph, every chosen edge belongs to a star and can be oriented toward its star center.
- If \(m_v\) nontriangle edges are oriented into \(v\), they can be packetized into exactly \(\lceil m_v/d_v\rceil\) star colors at \(v\).
- Conversely, any orientation of \(H\) gives such a packetization.

So the weighted optimization problem becomes:

> maximize the total selected edge weight subject to a budget bound on  
> \(|\mathcal T|+\sum_v \lceil m_v/d_v\rceil\).

This is the right global formulation of the current weighted frontier.

### 4.2 Separator/interface gluing principle

Let \(X\subseteq V(G)\) be a separator. After fixing the internal pattern on \(G[X]\), each component \(C\) of \(G-X\) interacts with the rest of the graph only through a finite **signature** on \(X\), consisting of:

- residue increments at vertices of \(X\) coming from nontriangle edges oriented into \(X\), naturally taken modulo \(d_x\);
- local budget used inside \(C\);
- local weight gained inside \(C\);
- and which edges of \(G[X]\) are consumed by mixed triangles that pass through \(C\).

Different components of \(G-X\) then combine by ordinary knapsack-style convolution on these signatures.

This is the real meta-explanation behind the newer exact weighted results. The earlier tree / cactus / one-full-side bipartite successes were not isolated tricks; they were manifestations of this separator-signature principle.

---

## 5. New exact algorithmic families that now look consolidated

The following feel solid enough to promote into the main frontier.

### 5.1 Tree links

If \(T\) is a tree with positive edge weights and capacities \(d_v\), then the weighted optimization problem
\[
M_t(T):=\max\Big\{\sum_{e\in F} w_e : F\subseteq E(T),\ \chi_d(F)\le t\Big\}
\]
is exactly computable by dynamic programming.

Because a tree is triangle-free, the star–triangle normal form reduces to an orientation-cost problem:
\[
\chi_d(F)=\min_{\vec F}\sum_v \left\lceil\frac{m_v}{d_v}\right\rceil.
\]
A rooted-tree DP needs only to communicate upward:

- budget used in the processed subtree;
- the residue / count information at the root relevant to future carries;
- and the state of the parent edge (absent / oriented to parent / oriented to root).

This gives exact solvability for weighted tree links.

### 5.2 Bounded-treewidth graph links

For fixed treewidth \(k\), the weighted problem is exactly computable by dynamic programming on a nice tree decomposition.

The bag state tracks:

- budget spent so far;
- for each bag vertex \(v\), the current residue of incoming nontriangle edges modulo \(d_v\);
- finite local interface data for selected/oriented bag edges;
- and finite triangle-interface information recording which triangle pieces are still “open” inside the bag.

When partial solutions are merged, the only nontrivial arithmetic at a vertex is the packet carry
\[
\left\lfloor \frac{r_v+r_v'}{d_v}\right\rfloor,
\]
and when a vertex is forgotten, one closes out the final remainder.

This subsumes trees and cacti and gives exact weighted solvability for fixed-treewidth classes such as:

- trees;
- cacti;
- series-parallel graphs;
- outerplanar graphs;
- more generally any fixed-treewidth graph-link family.

### 5.3 Triangle-free graphs with full capacity as a special orientation-only regime

The earlier full-capacity triangle-free theorem from v8 now fits naturally as the degenerate case of the star–triangle normal form in which:

- there are no triangles at all, and
- every selected star can simply be taken whole.

So the weighted problem collapses to weighted edge coverage by up to \(t\) chosen vertices. This is now best viewed as the simplest member of the new orientation/interface framework.

---

## 6. Promising parameterized extensions not yet fully consolidated

The recent combos suggested several broader exact families, but after the later recalibration pass they should not yet be promoted to the same status as the items in Section 5.

### 6.1 Bounded feedback-vertex-set

It looks plausible that a feedback-vertex-set modulator \(Z\) can be handled exactly by:

- solving each forest component of \(G-Z\) by a component table indexed by its interface to \(Z\);
- then convolving those tables over \(Z\).

This is very likely true, but the full writeup and pressure-test are not yet complete.

### 6.2 Bounded vertex cover

A bounded vertex cover \(C\) should allow exact DP over the independent outside vertices, each contributing a local signature against the small core \(C\). Again: plausible and promising, but not yet fully written.

### 6.3 Bounded twin-cover

This is the densest-looking promising extension. If \(X\) is a twin-cover, then \(G-X\) is a disjoint union of cliques with uniform neighborhoods into \(X\), which strongly suggests a clique-module signature DP over the core \(X\). This looks like the most interesting “dense parameterized” next theorem target, but it still belongs in the provisional bucket for now.

---

## 7. What should now be demoted

The stricter step-back after the recalibration combo suggests demoting the following from “current theorem target” status.

### 7.1 Fully bounded two-sided \(K_{a,b}\) closed forms

This is still a live and important target, but the naive Ferrers / northwest-prefix picture is false, and no replacement closed form is yet trustworthy.

### 7.2 Dense modular-structure dreams

Clean exact theorems for neighborhood diversity, modular width, or unrestricted substitution-type dense classes have **not** survived pressure-testing yet. They may still be reachable later, but they are not the right thing to advertise as the immediate frontier.

### 7.3 Over-reading quick combo outputs

Some recent ambitious combos produced plausible exact families quickly. After the explicit project-file correction on combo depth, the right move is to keep those items that fit a clear separator/interface proof scheme and demote the rest until the proof skeleton is fully stabilized.

---

## 8. Consequences for the three Erdős problems

### 8.1 Consequences for #278

The project now provides exact maximum formulas or exact algorithms for several broad squarefree families:

1. the earlier low-dimensional catalogues;
2. all perfectly packable common-core graph links via \(\chi_d(G)\);
3. arithmetic clique links, with exact perfect-packing threshold \(D_C\ge n-2\);
4. weighted arithmetic clique-link maxima in all currently solved clique regimes;
5. exact weighted one-full-side bipartite families;
6. exact weighted fixed-treewidth graph-link families.

This is still not a full solution of #278. But it is now much more than a clique-link story: the project has an explicit algorithmic route for exact weighted optimization on broad sparse graph-link classes.

### 8.2 Consequences for #202 and #1190

The disjointness side still inherits the earlier exact packability library. The weighted side now also has a meaningful exact restricted-model optimization theory. This does not solve the global asymptotic questions in #202 or #1190, but it does deepen the finite structural connection to them.

---

## 9. Step-back assessment

### 9.1 Paper-worthiness and paper scale

Paper-worthiness had already been crossed by v7 and remained crossed in v8. The gap from v8 to v9 is still **more material for the current paper**, not “time for a different paper.”

What changes is the organization of the current paper. The paper should no longer stop at:

- packability theory,
- arithmetic clique links,
- and a few weighted explicit formulas.

It now wants an additional section centered on:

> **exact weighted solvability via star–triangle decompositions and separator signatures**.

### 9.2 What is now the clearest center of gravity?

The project’s real center is now:

> **common-core squarefree graph links, with exact weighted optimization obtained either by explicit formula or by finite-state dynamic programming forced by local star–triangle structure.**

That is a cleaner and more robust description than the v8 phrasing.

### 9.3 Calibration update

The long run of very ambitious combos initially suggested “keep pushing higher.”  
The later stricter recalibration combo suggested the opposite correction:

- very high targets are **not** generally yielding at the same rate anymore;
- the best next move is probably a normal combo, or a paper/proof-writing pass, rather than another aggressive overshoot.

So the local calibration has now come back down.

---

## 10. Current best next targets

### 10.1 Best theorem-writing target

Write up and stabilize the proof of the **star–triangle normal form** and the **bounded-treewidth exact DP theorem**. These now look like the most reusable post-v8 advances.

### 10.2 Best live theorem target

Return to the still-open and very concrete family:

> **weighted complete bipartite links with bounded capacities on both sides**

but do so in a normal-depth combo, not a heavily overshooting one.

### 10.3 Best dense-side exploratory target

If one wants a denser parameterized target after that, the best candidate is:

> **bounded twin-cover exact solvability**

since it has a clear small-core / clique-module interface flavor and seems more plausible than unrestricted modular-width ambitions.

---

## 11. Recommended next action

Two tracks make sense.

### 11.1 Paper track

Start turning the current frontier into a paper-oriented writeup with the following arc:

1. public problem context;
2. squarefree product-space model and singleton reduction;
3. perfect packing, pair-support theorem, common-core theorem;
4. exact \(\chi_d\) families;
5. arithmetic clique-link theorem;
6. weighted clique-link theorems;
7. weighted one-full-side bipartite theorems;
8. star–triangle normal form;
9. exact weighted solvability by separator signatures (including fixed-treewidth);
10. bounded-bipartite and dense-parameterized open frontier.

### 11.2 Live theorem track

If the objective is another theorem push before formalization, the best next combo should probably be **normal** and aimed at bounded-capacity weighted \(K_{a,b}\), with the separator/interface toolkit in mind but without forcing an over-ambitious target on every hit.

---

## References / citations

- **[P278]** T. F. Bloom, *Erdős Problem #278*, current public problem page, accessed 2026-04-18.
- **[P202]** T. F. Bloom, *Erdős Problem #202*, current public problem page, accessed 2026-04-18.
- **[P1190]** T. F. Bloom, *Erdős Problem #1190*, current public problem page, accessed 2026-04-18.
- **[FN-v8]** `erdos278_frontier_note_v8_apr2026.md`.
- **[TC]** `Some-Terminology-and-Conventions.txt`.
- **[TC-A1]** `Some-Terminology-and-Conventions-Addendum.txt`.
- **[TC-A2]** `Some-Terminology-and-Conventions-Addendum2.txt`.
- **[TC-A3]** `STaC-Addendum3.txt`.
