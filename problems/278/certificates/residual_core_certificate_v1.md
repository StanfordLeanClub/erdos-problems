# Erdős #278 residual-core checker v1

This note records the finite residual-core certificate produced during the post-v11 attack on the corrected full-union clique theorem

\[
\operatorname{Opt}_{\mathrm{full}}(K_n,n-4)
\stackrel{?}{=}
\binom n2 d^{-2}-15d^{-4}.
\]

## Key correction found during the checker pass

The residual insertion model must include **empty colors**.

If the intersecting skeleton has residual core size \(r\) and \(h<r-4\) residual triangle colors, then \(r-4-h\) colors are empty after the deletion step. Residual edges may be assigned to these empty colors with no skeleton-base cost. Earlier informal residual tables that omitted these colors were too optimistic structurally, although the corrected check still gives the desired lower bound.

## What was checked

For every relevant residual core:

- \(4\le r\le 7\);
- \(0\le h\le r-4\);
- \(h\) edge-disjoint triangle skeletons in \(K_r\), up to isomorphism;
- \(\binom r2-3h\le 15\) residual edges;

the finite MILP minimized the **full residual defect polynomial**, not just the first-order monochromatic-disjoint-pair count.

The model includes:

1. triangle skeleton bins;
2. empty color bins, count \(r-4-h\);
3. star skeleton bins with conservative cheap score sequence \(r-2,r-1,r,\ldots\);
4. all residual-edge assignments to these bins;
5. all matching contributions to the union defect polynomial.

The check was made at

\[
q=\frac1{(r-1)^2},
\]

which is the largest local value relevant to a residual core of size \(r\). For the full theorem, \(q=d^{-2}\le (n-1)^{-2}\), so this is the conservative endpoint to justify in the written proof.

## Certified residual table

The output table was:

```text
case  r  h  residual_edges  empty_colors  min defect/q^2
00    4  0        6              0              15
01    5  0       10              1              15
02    5  1        7              0              15
03    6  0       15              2              15
04    6  1       12              1              15
05    6  2        9              0              15
06    6  2        9              0              15
07    7  2       15              1              15
08    7  2       15              1              15
09    7  3       12              0              16
10    7  3       12              0              16
11    7  3       12              0              16
```

The duplicated rows correspond to the non-isomorphic edge-disjoint triangle skeleton types in the given \((r,h)\) case.

## Consequence

The finite residual-core obstruction appears resolved:

\[
\mathrm{defect}\ge 15q^2
\]

in every residual case.

This is stronger than the first-order statement \(m_2\ge15\): it includes the higher matching corrections in the true full-union defect expansion.

## Current theorem status

This certificate strongly supports promoting the following theorem after the proof is written carefully:

\[
\operatorname{Opt}_{\mathrm{full}}(K_n,n-4)
=
\binom n2d^{-2}-15d^{-4}
\qquad(d\ge n-1).
\]

Remaining proof-writing tasks:

1. write the residual-core reduction rigorously;
2. justify the finite list \(r\le7\) and the residual cases in the table;
3. explain the empty-color correction;
4. include either this finite certificate or a human-checkable version of the residual table;
5. justify why checking at \(q=1/(r-1)^2\) suffices for the full range \(q\le(n-1)^{-2}\).
