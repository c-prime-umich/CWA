#!/usr/bin/env python
# Author: Timothy J. Welch
"""XT-diagram reader (port of CWA_MATLAB/XTReader_mod.m).

``XTReader_mod`` returns the angular grid ``thetap``, the time vector ``t`` and
the light matrix ``lights`` (sensors x frames).  The plotting branch (the
``nargout < 1`` case in the reference) has no effect on the analysis and is
omitted.
"""
import numpy as np

__all__ = ["xt_reader"]


def xt_reader(XTStruct):
    """Return ``(t, thetap, lights, fps, Nb)``.

    Parameters
    ----------
    XTStruct : dict with keys ``XT`` (Nb, Nfr), ``t0`` (scalar or (1, Nfr)), ``fps``.

    Notes
    -----
    ``t = (0:Nfr-1)/fps + t0`` is evaluated element-wise so that both a scalar
    ``t0`` (full diagram) and a per-frame ``t0`` vector (short diagram) are
    handled exactly as in MATLAB.
    """
    XT = np.asarray(XTStruct["XT"], dtype=float)
    t0 = np.asarray(XTStruct["t0"], dtype=float)
    fps = float(XTStruct["fps"])

    Nb, Nfr = XT.shape
    dth = 2 * np.pi / Nb
    thetap = np.arange(Nb) * dth                 # 0 : dth : 2*pi - dth
    t = np.arange(Nfr) / fps + t0                # element-wise; t0 scalar or (1,Nfr)
    return t, thetap, XT, fps, Nb
