#!/usr/bin/env python
# Author: Timothy J. Welch
"""Detonation-property lookup (port of the ``H2AirDetProp.xlsx`` usage).

MATLAB reads the workbook with ``readmatrix`` and looks up the Chapman-Jouguet
detonation velocity via ``interp1(dat(:,1), dat(:,9), phi)`` where column 1 is
the equivalence ratio ``Phi`` and column 9 is ``D [m/s]``.

The workbook layout is: a single header row, then 121 numeric data rows and a
trailing pair of note columns.  Reading the first nine numeric columns (skipping
the header) reproduces MATLAB's numeric block exactly.
"""
import numpy as np
import pandas as pd

__all__ = ["load_det_props", "ucj_at_phi"]


def load_det_props(xlsx_path):
    """Return the numeric (n, 9) data matrix from ``H2AirDetProp.xlsx``.

    Columns: 0 = Phi, 8 = D [m/s] (9th column), matching ``dat(:,1)`` / ``dat(:,9)``.
    """
    df = pd.read_excel(xlsx_path, header=0)
    dat = df.iloc[:, :9].to_numpy(dtype=float)
    return dat


def ucj_at_phi(dat, phi):
    """Interpolated Chapman-Jouguet detonation velocity [m/s] at equivalence ratio ``phi``."""
    return float(np.interp(phi, dat[:, 0], dat[:, 8]))
