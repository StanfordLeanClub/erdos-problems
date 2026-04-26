# Certificates for Problem 278

This directory contains finite certificates and checker artifacts used to support claims in the current frontier note and paper draft.

A **certificate** is not the same thing as a frontier note, paper draft, or Lean formalization.

- A frontier note explains the current mathematical frontier and records what the project currently treats as established, provisional, or open.
- A paper draft gives the polished mathematical narrative.
- Lean code is machine-checked formalization.
- A certificate is a finite verification artifact: it records a finite case analysis, computation, table, or checker output that supports a specific theorem or proof step.

## Current certificates

### `residual_core_certificate_v1.md`

This certificate supports the corrected full-union clique-link target

\[
\operatorname{Opt}_{\mathrm{full}}(K_n,n-4)
=
\binom n2 d^{-2}-15d^{-4}
\qquad(d\ge n-1).
\]

It verifies the finite residual-core obstruction that remains after reducing the problem to residual cores of size \(r\le 7\).

The key correction recorded in the certificate is that the residual insertion model must include **empty colors**: if the residual core has size \(r\) and the intersecting skeleton has \(h<r-4\) triangle colors, then \(r-4-h\) colors are empty after deletion and may receive residual edges.

### `residual_core_certificate_checker_v1.py`

This is a lightweight checker scaffold documenting the finite-check model. It is currently an external certificate/checker target, not a Lean formalization.

## Relevance to the problem

The certificate belongs to the **full-union** side of Erdős #278, not merely the packability side.

The project’s v10 correction separated packable-subgraph optimization from the actual #278 maximum-coverage objective. The residual-core certificate is part of the post-v10 effort to prove exact theorems for the corrected full-union objective.

## Status

The \(K_n,t=n-4\) theorem should be treated as:

> certificate-backed / proof-writing-needed

until the residual table is either converted into a fully human-checkable proof or formalized / independently verified by a stronger executable checker.
