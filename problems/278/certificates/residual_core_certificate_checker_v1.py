#!/usr/bin/env python3
"""
Finite residual-core checker for the corrected full-union K_n, t=n-4 target.

This is a compact checker scaffold. The main conversation run used the same
MILP model to certify the residual cases listed in
`erdos278_residual_core_certificate_v1.md`.

The key modeling points are:
  * include triangle skeleton colors;
  * include empty colors when h < r-4;
  * include star skeleton colors with cheap score sequence r-2, r-1, r, ...;
  * minimize the full defect polynomial, not merely the first-order pair count.

To keep this handoff file lightweight, see the certificate note for the verified
case table. A fuller executable checker can be added to the repo once we decide
where verification tools should live.
"""

print("See erdos278_residual_core_certificate_v1.md for the certified residual table.")
