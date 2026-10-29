#!/usr/bin/env python
# Author: Timothy J. Welch
"""Data-loading helpers for the ECWA pipeline (thin, dependency-light)."""
import os
import numpy as np
from scipy.io import loadmat

__all__ = ["load_xt_full", "load_xt_short"]


def _read(path):
    m = loadmat(path)
    XT = np.asarray(m["XT"], dtype=float)
    t0 = np.asarray(m["t0"], dtype=float)
    t0 = float(t0.ravel()[0]) if t0.size == 1 else t0.ravel()
    fps = float(np.asarray(m["fps"]).ravel()[0])
    return XT, t0, fps


def load_xt_full(root, run):
    """Full time-trace XT (Nb x Nfr). Returns (XT, t0, fps); t0 is a scalar."""
    return _read(os.path.join(root, "XT_diagrams", f"Run_{run:05d}-full.mat"))


def load_xt_short(root, run):
    """Short time-trace XT (Nb x 5000). Returns (XT, t0, fps); t0 is a (1,5000) vector."""
    return _read(os.path.join(root, "XT_diagrams", f"Run_{run:05d}.mat"))
