# Erdős Problem #278 and companions — frontier note v12

**Date:** April 25, 2026  
**Status:** Still not a full solution to Erdős #278. The project remains paper-worthy. The main update since v11 is a finite residual-core certificate program for the corrected full-union clique threshold \(K_n,t=n-4\), including a crucial empty-color correction.

---

## 0. Purpose of this note

This note updates frontier v11. It records the corrected full-union progress after v10 and v11, with an explicit separation between:

1. stable theorem-level results;
2. certificate-backed results that need a careful writeup/checker artifact before paper promotion;
3. still-open targets.

The v10 warning remains the governing discipline:

> Packable-subgraph optimization is not the same as full #278 maximum coverage.

The post-v10 work is therefore about the actual **layer-union** objective, not the old packable-subgraph surrogate.

---

## 1. Stable background retained from v10/v11

### 1.1 Squarefree product-space model

For squarefree \(Q=\prod_i p_i\), a support \(S\) gives an \(S\)-cylinder in \(X=\prod_i\Omega_i\), with density
\[
\mu(C_S)=\prod_{i\in S}\frac1{p_i}=\frac1{n_S}.
\]

Singleton supports reduce to a residual box with coordinate sizes \(p_i\) or \(p_i-1\). This remains a maximum-coverage reduction, not a perfect-packing theorem by itself.

### 1.2 Perfect packing and common-core graph links

Perfect packing is equivalent to intersection-separating local patterns. If a whole support family is perfectly packable, the union bound is attained and one obtains an exact #278 maximum for that family.

For common-core graph links
\[
C*G=\{C\cup e:e\in E(G)\},
\]
with core budget
\[
D_C=\prod_{i\in C}d_i,
\]
the packability threshold is governed by \(\chi_d(G)\):
\[
C*G\text{ perfectly packable}\iff \chi_d(G)\le D_C.
\]

This remains the zero-defect case of the full layer-union theory.

---

## 2. Corrected full-union object

For a graph link \(H\), define the one-layer union objective
\[
U_d(H)=\max_{\text{endpoint labelings}}
\mu\left(\bigcup_{uv\in E(H)}C_{uv}\right).
\]

For a common-core graph link with \(t=D_C\) core patterns, the corrected full-union residual objective is
\[
\operatorname{Opt}_{\mathrm{full}}(G,t)
=
\max_{E(G)=E_1\sqcup\cdots\sqcup E_t}
\sum_{r=1}^t U_d(G[E_r]),
\]
up to the common core-density normalization.

This is the true #278 maximum-coverage object in the full-capacity graph-link regime.

---

## 3. Stable theorem: full-capacity one-layer matching formula

Assume
\[
d_v\ge \deg_H(v)\qquad(\forall v\in V(H)).
\]
Then an optimal one-layer labeling may be chosen proper at every vertex, meaning incident edges at a vertex use distinct local labels.

### Theorem 3.1

Under the full-capacity hypothesis,
\[
\boxed{
U_d(H)=
\sum_{\varnothing\ne M\text{ matching in }H}
(-1)^{|M|+1}
\prod_{v\in V(M)}\frac1{d_v}.
}
\]

Proof idea: refining labels at one vertex cannot decrease coverage pointwise. Full capacity allows refining until all incident edges use distinct labels. Then intersections of edge-cylinders survive exactly for graph matchings, and inclusion-exclusion gives the formula.

Uniform clique case: if \(d_v=d\),
\[
U(K_n)=
\sum_{k=1}^{\lfloor n/2\rfloor}
(-1)^{k+1}
\frac{n!}{2^k k!(n-2k)!}d^{-2k}.
\]

Uniform bipartite case with \(q=(d_Ld_R)^{-1}\):
\[
U(K_{a,b})=
\sum_{k=1}^{\min(a,b)}
(-1)^{k+1}k!\binom ak\binom bk q^k.
\]

---

## 4. Stable theorem: local defect-cover lemma

For uniform full-capacity clique layers, set
\[
q=d^{-2}.
\]
For \(H\subseteq K_n\), define
\[
D(H)=|E(H)|q-U(H).
\]
Let \(\Gamma_H\) be the disjointness/conflict graph of \(H\): vertices are edges of \(H\), and two vertices are adjacent iff the corresponding edges of \(K_n\) are disjoint.

### Theorem 4.1

\[
\boxed{D(H)\ge \tau(\Gamma_H)q^2.}
\]

Proof idea: induct on \(\tau(\Gamma_H)\). Removing an edge-vertex from a minimum vertex cover lowers \(\tau\) by one. Adding it back increases defect by the measure of its intersection with the previous union; since it has a conflict-neighbor, this increase is at least \(q^2\).

---

## 5. Stable theorem: exact full-union clique value at \(t=n-3\)

Let \(d\ge n-1\) and \(q=d^{-2}\).

### Theorem 5.1

\[
\boxed{
\operatorname{Opt}_{\mathrm{full}}(K_n,n-3)=
\binom n2q-3q^2.
}
\]

Proof idea: in any \((n-3)\)-layer partition, delete a minimum conflict-cover from each layer. The remaining layers are intersecting, and \(n-3\) intersecting families cover at most \(\binom n2-3\) edges. Hence total conflict-cover size is at least \(3\), so the defect-cover lemma gives loss at least \(3q^2\). Equality is attained by \(n-4\) star layers plus one \(K_4\) layer.

### Common-core corollary

For \(C*K_n\) with \(D_C=n-3\) and uniform full petal capacity \(d\ge n-1\), the residual maximum is
\[
\frac1{D_C}\left(\binom n2d^{-2}-3d^{-4}\right).
\]

---

## 6. Stable base case: \(K_6,t=2=n-4\)

### Theorem 6.1

For uniform full petal capacity \(d\ge5\), with \(q=d^{-2}\),
\[
\boxed{
\operatorname{Opt}_{\mathrm{full}}(K_6,2)=15q-15q^2.
}
\]

Construction: one star layer plus one \(K_5\)-layer.

Lower-bound idea: \(K_6\) has \(15\) perfect matchings. In any two-coloring of a perfect matching's three edges, two share a color. Each monochromatic disjoint edge-pair belongs to a unique perfect matching. Thus every two-coloring has at least \(15\) monochromatic disjoint pairs, and the higher-order correction is controlled by \(q\le1/25\).

---

## 7. New v12 update: residual-core certificate program for \(K_n,t=n-4\)

The next conjectured full-union theorem is
\[
\boxed{
\operatorname{Opt}_{\mathrm{full}}(K_n,n-4)
\stackrel{?}{=}
\binom n2q-15q^2
\qquad(d\ge n-1).
}
\]

Candidate construction: \(n-5\) star layers plus one \(K_5\)-layer. The \(K_5\)-layer has exactly \(15\) disjoint edge-pairs and no three-edge matching, so the defect is \(15q^2\).

### 7.1 Residual-core reduction

Assume a putative counterexample. Delete a vertex cover from each color's conflict graph. If the first-order defect were below \(15\), at most \(14\) edge-vertices are deleted. The remaining color classes are intersecting and cover at least
\[
\binom n2-14
\]
edges.

If the remaining intersecting skeleton has \(s\) star classes and \(h\) triangle classes, set
\[
r=n-s.
\]
The standard support bound
\[
|E_{\mathrm{skel}}|\le s(n-s)+\binom s2+3h,
\]
with \(h\le r-4\), forces
\[
4\le r\le7.
\]

Thus the global supersaturation problem reduces to residual cores on at most seven vertices.

### 7.2 Key v12 correction: empty colors

The residual insertion model must include **empty colors**.

If the residual core has size \(r\) and the skeleton contains \(h<r-4\) residual triangle colors, then
\[
r-4-h
\]
colors are empty after the deletion step. Residual edges can be assigned to these empty colors with no skeleton-base cost. Earlier informal residual checks that omitted these colors had the wrong model, even though the corrected finite certificate still supports the same lower bound.

The residual model must include:

1. triangle skeleton colors;
2. empty colors;
3. star colors with correct score/leaf-size costs \(r-2,r-1,r,\ldots\);
4. internal conflicts among residual edges assigned to the same color;
5. the full defect polynomial, not just first-order pair counts.

### 7.3 Certificate-level finite table

The finite certificate v1 records the following minima for the normalized defect \(\mathrm{defect}/q^2\):

\[
\begin{array}{c|c|c|c|c}
r&h&\text{residual edges}&\text{empty colors}&\min(\mathrm{defect}/q^2)\\
\hline
4&0&6&0&15\\
5&0&10&1&15\\
5&1&7&0&15\\
6&0&15&2&15\\
6&1&12&1&15\\
6&2&9&0&15\\
6&2&9&0&15\\
7&2&15&1&15\\
7&2&15&1&15\\
7&3&12&0&16\\
7&3&12&0&16\\
7&3&12&0&16
\end{array}
\]

Repeated rows correspond to non-isomorphic edge-disjoint triangle skeletons.

### 7.4 Current status of \(K_n,t=n-4\)

The theorem is now **certificate-backed but not yet fully paper-polished**.

The correct status is:

\[
\boxed{
\operatorname{Opt}_{\mathrm{full}}(K_n,n-4)=
\binom n2d^{-2}-15d^{-4}
}
\]

is essentially reduced to the finite residual certificate. It should be promoted to theorem only once the paper includes either:

- an executable checker/certificate file in the repo; or
- a human-checkable residual case table with proof of the entries.

---

## 8. Consequences for #278

The project now has genuine corrected full-union results for restricted squarefree common-core clique links:

1. full-capacity one-layer graph links have a matching-polynomial formula;
2. full-capacity common-core graph links reduce to layer partitions;
3. full-capacity clique links at \(D_C=n-3\) are exactly solved;
4. \(K_6,D_C=2\) is exactly solved;
5. \(K_n,D_C=n-4\) is at certificate-backed status pending final packaging.

This is still not a full solution to #278. It is, however, real movement on the corrected maximum-coverage side, not merely packing.

---

## 9. Lean/formalization status

No Lean source change is required by the v12 update. The current Lean code formalizes the stable packing spine and complete-bipartite small-side packability, not the new layer-union residual-core certificate.

If desired, a future Lean or external-verifier target is:

- define \(U_d(H)\) in a finite product space;
- formalize the full-capacity one-layer matching formula;
- formalize/check the finite residual-core certificate for \(K_n,t=n-4\).

For now, the finite certificate should live as an external computational artifact, not as a Lean theorem.

---

## 10. Paper-worthiness and paper scale

The project remains paper-worthy, and this is still **more material for the current #278 paper**, not a separate paper.

However, the paper should now be updated from v10 to include a new full-union section:

1. one-layer full-capacity matching formula;
2. layer-partition formulation;
3. defect-cover lemma;
4. exact \(K_n,t=n-3\) theorem;
5. certificate-backed \(K_n,t=n-4\) status and residual checker.

---

## 11. Current best next action

Do not run another broad combo yet. The best next action is packaging and verification:

1. put the residual-core certificate in the repo;
2. add a checker or a human-readable certificate table;
3. update the frontier/current artifacts to v12;
4. patch the paper to include the new full-union section;
5. only then resume theorem-pushing, likely toward either a fully human proof of the residual table or the bipartite analogue.

---

## References

- T. F. Bloom, *Erdős Problem #278*, https://www.erdosproblems.com/278.
- T. F. Bloom, *Erdős Problem #202*, https://www.erdosproblems.com/202.
- T. F. Bloom, *Erdős Problem #1190*, https://www.erdosproblems.com/1190.
- S. Cambie, *Proving it is impossible; on Erdős problem #278*, arXiv:2508.18270.
- Frontier note v10, `erdos278_frontier_note_v10_corrected.md`.
- Frontier note v11, `erdos278_frontier_note_v11_full_union.md`.
- Residual-core certificate v1, `erdos278_residual_core_certificate_v1.md`.
