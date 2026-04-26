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

As of the v12 frontier, the stable part of the project is:

- the squarefree product-space cylinder model;
- perfect packing as intersection-separating colorings;
- the pair-support theorem;
- the common-core theorem;
- the graph-link invariant \(\chi_d(G)\);
- exact packability results for several graph-link families;
- a corrected full-union layer objective for true maximum coverage;
- a full-capacity one-layer matching-polynomial theorem;
- an exact full-union theorem for \(K_n,t=n-3\);
- a certificate-backed residual-core program for \(K_n,t=n-4\);
- a Lean formalization of the stable packing spine and the complete-bipartite small-side theorem.

The project remains organized around exact structural families rather than a claimed universal formula for the full #278 maximum.

## Corrected v10/v12 framing

The current mathematical center is:

> squarefree common-core graph links; exact packability; corrected full-union layer optimization; and residual-core certificates for near-threshold clique layers.

The key distinction introduced in v10 is:

- **Perfect packing** gives exact #278 maxima when the whole support family can be made pairwise disjoint.
- **Packable-subgraph optimization** gives exact disjoint-construction optima and lower bounds for #278.
- **Full #278 maximum coverage** requires optimizing actual union measure, including overlapping cylinders.

The v12 work is on the full-union side. It studies the one-layer objective \(U_d(H)\), where a graph link \(H\) chooses one pair-cylinder for every edge and maximizes the actual union measure.

## Canonical current artifacts

- Current paper draft: `paper/current/erdos278_paper.tex`
- Current paper PDF: `paper/current/erdos278_paper.pdf`
- Optional current paper Markdown: `paper/current/erdos278_paper.md`
- Current frontier note: `frontier/current/frontier_note.md`
- Current visualizer YAML: `frontier/current/frontier_visualizer.yaml`
- Correction notice: `corrections/v10_correction_notice.md`
- Certificates: `certificates/`
- Lean formalization: `formalization/lean/`

## Certificates

The `certificates/` directory contains finite verification artifacts that support specific proof steps in the current frontier.

A certificate is not the same thing as a paper draft, frontier note, or Lean formalization. It is a finite verification artifact: a table, checker, finite case analysis, or generated witness that supports a specific theorem or proof step.

The current certificate is the residual-core certificate for the corrected full-union \(K_n,t=n-4\) program. It verifies the finite residual cases that remain after reducing the problem to residual cores of size \(r\le 7\).

This certificate is relevant because the \(K_n,t=n-4\) theorem is not currently Lean-formalized and should remain marked as **certificate-backed / proof-writing-needed** until the finite table is packaged as either a human-checkable proof or a stronger executable checker.

The key correction recorded by the certificate is that the residual model must include **empty colors**: if the residual core has size \(r\) and the intersecting skeleton has \(h<r-4\) triangle colors, then \(r-4-h\) colors are empty after deletion and may receive residual edges.

## Lean formalization status

The Lean development currently formalizes the stable packing material, not the full-union residual-core results.

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

1. Turn the residual-core certificate for \(K_n,t=n-4\) into a polished proof.
2. Decide whether the residual table should remain as a certificate, become an executable checker, or be translated into a human-checkable finite case proof.
3. Extend the corrected full-union layer method beyond the clique cases \(t=n-3\) and certificate-backed \(t=n-4\).
4. Attack the full-capacity bipartite layer-union analogue.
5. Keep the Lean formalization aligned with the stable packing spine, and only formalize full-union results once their proof objects are stable.
6. Continue treating packable-subgraph optimization and full union-measure optimization as distinct objects.

## Correction history

The v10 correction notice records the main change from v9:

- packable-subgraph optimization is not full #278 maximum coverage;
- the old nonuniform clique-link criterion using `c_i - 2` was wrong;
- arbitrary-weight clique threshold formulas were demoted;
- the weighted graph-link material was reframed as packable-subgraph optimization unless a separate union-measure theorem is proved.

The v12 update records the first substantial post-v10 full-union progress:

- full-capacity one-layer matching-polynomial formula;
- exact corrected full-union theorem for \(K_n,t=n-3\);
- certificate-backed residual-core program for \(K_n,t=n-4\), including the empty-color correction.
