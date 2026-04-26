# Problem 278 — Maximum density of congruence covers

## Public problem

Erdős Problem #278 asks:

> Let \(A=\{n_1<\cdots<n_r\}\) be a finite set of positive integers. What is the maximum density of integers covered by a suitable choice of congruences \(a_i \pmod {n_i}\)? Is the minimum density achieved when all \(a_i\) are equal?

Public page:

- https://www.erdosproblems.com/278

Related public pages:

- https://www.erdosproblems.com/202
- https://www.erdosproblems.com/1190

## Current status

This problem folder contains paper-worthy partial progress, but **not** a full solution of Erdős #278.

As of the corrected v10 frontier, the stable part of the project is:

- the squarefree product-space cylinder model;
- perfect packing as intersection-separating colorings;
- the pair-support theorem;
- the common-core theorem;
- the graph-link invariant \(\chi_d(G)\);
- exact packability results for several graph-link families;
- a Lean formalization of the stable packing spine and the complete-bipartite small-side theorem.

The main v10 correction is that **packable-subgraph optimization is not the same as the full #278 maximum-coverage objective**. Weighted graph-link optimization results should be read as exact packable-subgraph / disjoint-construction results unless a separate union-measure upper bound is proved.

## Corrected v10 framing

The current mathematical center is:

> squarefree common-core graph links; exact packability; packable-subgraph optimization; and the layer-union frontier for true #278 maximum coverage.

The key distinction is:

- **Perfect packing** gives exact #278 maxima when the whole support family can be made pairwise disjoint.
- **Packable-subgraph optimization** gives exact disjoint-construction optima and lower bounds for #278.
- **Full #278 maximum coverage** requires optimizing actual union measure, including overlapping cylinders.

The true full-coverage frontier is now the one-layer union objective \(U_d(H)\): given a graph link \(H\), choose one pair-cylinder for every edge and maximize the actual union measure.

As of v12, the project has post-v10 full-union results: a full-capacity one-layer matching-polynomial formula, an exact \(K_n,t=n-3\) theorem, and a certificate-backed \(K_n,t=n-4\) residual-core program. The \(K_n,t=n-4\) theorem should remain certificate-backed / proof-writing-needed until the residual table is packaged as an executable checker or human-checkable proof.

## Canonical current artifacts

- Current paper draft: `paper/current/erdos278_paper.tex`
- Current paper PDF: `paper/current/erdos278_paper.pdf`
- Current frontier note: `frontier/current/frontier_note.md`
- Current visualizer YAML: `frontier/current/frontier_visualizer.yaml`
- Correction notice: `corrections/v10_correction_notice.md`
- Lean formalization: `formalization/lean/`

## Lean formalization status

The Lean development currently formalizes the stable packing material, not the demoted weighted-overclaim material.

Current Lean coverage includes:

- product-space cylinder definitions;
- cylinder disjointness and perfect packing;
- the pair-support theorem;
- the common-core theorem with an explicit core/link disjointness hypothesis;
- graph-link definitions and color-count predicates;
- stars and exact star criteria;
- complete-bipartite setup and structural lemmas;
- exact complete-bipartite formula in the small-side regime \(a<d\).

See `formalization/README.md` for the module map and roadmap.

## Current best mathematical targets

1. Develop the true layer-union theory \(U_d(H)\).
2. Prove or refute optimality of proper local labeling in the full-capacity one-layer regime.
3. Write the corrected nonuniform clique-link criterion carefully.
4. Finish the remaining complete-bipartite packability formalization.
5. Formalize the star–triangle normal form for the packable-color invariant \(\chi_d(F)\).

## Correction history

The v10 correction notice records the main change from v9:

- packable-subgraph optimization is not full #278 maximum coverage;
- the old nonuniform clique-link criterion using `c_i - 2` was wrong;
- arbitrary-weight clique threshold formulas were demoted;
- the weighted graph-link material was reframed as packable-subgraph optimization unless a separate union-measure theorem is proved.