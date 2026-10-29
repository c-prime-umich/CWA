#!/usr/bin/env python
# Author: Timothy J. Welch
"""MATLAB-compatible ``interp1`` (linear) used across the CWA / ECWA port.

MATLAB's ``interp1(xi, yi, xq, "linear", "extrap")`` is not available in NumPy
(``np.interp`` is strictly 1-D and clamps at the boundaries).  This helper
reproduces the semantics needed by the pipeline:

  * ``xi``  : (N,) strictly increasing sample coordinates
  * ``yi``  : (N,) or (N, K) values (K parallel series, one per column)
  * ``xq``  : (Q,) or scalar query points
  * ``extrap``: when True, linearly extrapolate outside ``[xi[0], xi[-1]]``
                (MATLAB ``"extrap"``); when False, return NaN there (MATLAB default).
"""
import numpy as np

__all__ = ["interp1"]


def interp1(xi, yi, xq, extrap=False):
    """Linear interpolation matching MATLAB ``interp1`` for the cases used here."""
    xi = np.asarray(xi, dtype=float).ravel()
    yi = np.asarray(yi, dtype=float)
    xq = np.asarray(xq, dtype=float)
    scalar_q = xq.ndim == 0
    xq = xq.ravel()

    N = xi.size
    if yi.ndim == 1:
        yi2 = yi.reshape(N, 1)
    else:
        yi2 = yi.reshape(N, -1)

    # position of each query in the sorted xi (side='left' => pos in [0, N]).
    # Choose a valid segment [i0, i1] with i1 > i0, using the boundary segment
    # for queries that fall outside so that extrapolation is linear.
    pos = np.searchsorted(xi, xq, side="left")
    i0 = np.clip(pos - 1, 0, N - 2)
    i1 = np.clip(pos, 1, N - 1)

    x0 = xi[i0]
    x1 = xi[i1]
    denom = x1 - x0
    t = (xq - x0) / denom

    y0 = yi2[i0]                      # (Q, K)
    y1 = yi2[i1]
    val = y0 * (1.0 - t[:, None]) + y1 * t[:, None]

    if not extrap:
        inside = (xq >= xi[0]) & (xq <= xi[-1])
        val = np.where(inside[:, None], val, np.nan)

    out = val[:, 0] if val.shape[1] == 1 else val
    return out[0] if scalar_q else out
