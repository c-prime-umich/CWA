#!/usr/bin/env python
# Author: Timothy J. Welch
"""Shared ECWA helpers ported from ECWA_MATLAB.

Every function here is a faithful translation of the MATLAB source.  Several
(``clean_xt``, ``movmean``, ``add_wave``) were already validated against the
saved run-3433 artifacts before being promoted into the pipeline:
  * ``clean_xt`` reproduces ``BG.csv`` (per-sensor, per-20-frame min).  It now
    also background-subtracts the trailing column(s) beyond the last full block
    (a deliberate fix; the original MATLAB left them raw), so it differs from the
    saved ``BG.csv`` only in that trailing column.
  * ``movmean(k=1000)`` matches the reduced sigma/A/v CSVs to ~1e-14
    (MATLAB even-window centres with 500 samples left + 499 right).
"""
import numpy as np

from common.interp import interp1

__all__ = ["periodic_gaussian", "gauss_syn_func_resolved", "clean_xt",
           "fillna_linear", "movmean", "checker", "add_wave", "xt_prepper"]

_TWO_PI = 2.0 * np.pi


def periodic_gaussian(x, x0, A, sigma):
    """Gaussian on the periodic domain [0, 2*pi).  Port of ``periodicGaussian``."""
    dx = np.mod((x - x0) + np.pi, _TWO_PI) - np.pi
    return A * np.exp(-(dx ** 2) / (2.0 * sigma ** 2))


def gauss_syn_func_resolved(Nb, A, sigma, xc):
    """One resolved-frame Gaussian profile.  Port of ``Gaussian_Syn_Func_Resolved``."""
    thetap_syn = np.arange(Nb) * (_TWO_PI / Nb)
    return periodic_gaussian(thetap_syn, xc, A, sigma)


def clean_xt(XT, win=20):
    """Windowed per-sensor background removal.

    Port of the "Clean XTData" loop in both runners.  For each ``win``-frame
    block the per-sensor minimum over the block is subtracted; negatives clipped.
    Unlike the original MATLAB loop (``for i = 0:(Nfr-1)/win-1``), which left the
    trailing column(s) beyond the last full block raw, they are now also
    background-subtracted as a final partial block so every timestep is included.
    (This deliberately deviates from the saved MATLAB ``BG.csv`` in the trailing
    column, which was left raw and otherwise skewed per-frame amplitudes.)
    """
    Nfr = XT.shape[1]
    Xt = XT.copy()
    nblocks = (Nfr - 1) // win
    for i in range(nblocks):
        c0, c1 = i * win, i * win + win
        block = Xt[:, c0:c1]
        Xt[:, c0:c1] = block - block.min(axis=1, keepdims=True)
    c0 = nblocks * win
    if c0 < Nfr:                                # include the trailing partial block
        block = Xt[:, c0:Nfr]
        Xt[:, c0:Nfr] = block - block.min(axis=1, keepdims=True)
    Xt[Xt < 0] = 0
    return Xt


def fillna_linear(x):
    """Fill NaNs by linear interpolation over valid-index positions.  Port of ``fillNaNsLinear``."""
    x = np.asarray(x, dtype=float).ravel()
    y = x.copy()
    good = ~np.isnan(x)
    if good.sum() >= 2:
        xi = np.where(good)[0].astype(float)
        yi = x[good]
        xq = np.where(~good)[0].astype(float)
        y[~good] = interp1(xi, yi, xq, extrap=True)
    return y


def movmean(x, k, left_bias=1):
    """MATLAB ``movmean(x, k)`` (1-D).

    For the even window used here (k=1000) MATLAB centres with ``k//2`` samples
    before and ``k//2 - 1`` after; at the edges the window is truncated to the
    available data.  ``left_bias`` selects the even-window convention and was
    locked to ``1`` by reproducing the saved reduced CSVs to ~1e-14.
    """
    x = np.asarray(x, dtype=float).ravel()
    n = x.size
    left = (k - 1) // 2 + left_bias
    right = (k - 1) - left
    cs = np.concatenate([[0.0], np.cumsum(x)])
    lo = np.clip(np.arange(n) - left, 0, n)
    hi = np.clip(np.arange(n) + right + 1, 0, n)
    return (cs[hi] - cs[lo]) / (hi - lo)


def checker(XT, XT_syn, verbose=True):
    """L1 residual-energy fraction.  Port of ``checker.m``."""
    XT_energy = np.abs(XT).sum()
    ep = np.abs(XT_syn - XT).sum() / XT_energy
    if verbose:
        print(f"residual energy fraction = {ep:.6e}")
    return ep


def add_wave(XT_syn, Nfr, thetap_syn, theta0_start, v, A, sigma, dt, win=20):
    """Add reconstructed wave(s).  Port/generalisation of ``add_wave`` (Gauss_Syn_Runner.m).

    ``A``/``sigma``/``v`` are the reduced (every-``win``-th, smoothed) series,
    interpolated back to full rate with the centre(s) advected by ``v``.

    * ``n_gauss=1``: ``theta0_start`` scalar, ``A``/``sigma`` ``(n_reduced,)`` ->
      a single Gaussian (byte-for-byte the v1 behaviour).
    * ``n_gauss=2``: ``theta0_start`` ``(2,)``, ``A``/``sigma`` ``(2, n_reduced)``,
      ``v`` shared ``(n_reduced,)`` -> two Gaussians, both advected by the same
      system velocity.
    """
    XT_syn = XT_syn.copy()
    t_dummy = np.arange(1, Nfr + 1, win)            # 1 : win : Nfr
    theta0_start = np.atleast_1d(np.asarray(theta0_start, dtype=float))
    n_gauss = theta0_start.size
    A = np.asarray(A, dtype=float)
    sigma = np.asarray(sigma, dtype=float)
    v = np.asarray(v, dtype=float)
    for g in range(n_gauss):
        th0 = float(theta0_start[g])
        Ag = A[g] if A.ndim > 1 else A
        sg = sigma[g] if sigma.ndim > 1 else sigma
        XT_syn[:, 0] += periodic_gaussian(thetap_syn, th0, Ag[0], sg[0])
        theta0 = th0
        for i in range(2, Nfr + 1):                 # 1-based frame index
            A_it = interp1(t_dummy, Ag, float(i))
            sigma_it = interp1(t_dummy, sg, float(i))
            v_it = interp1(t_dummy, v, float(i - 1))
            theta0 = theta0 + v_it * dt
            XT_syn[:, i - 1] += periodic_gaussian(thetap_syn, theta0, A_it, sigma_it)
    return XT_syn


def _gauss_synth(Nb, thetap, theta0, sigma, A):
    """(Nb, Nfr) synthesis: the sum of ``n_gauss`` periodic Gaussians.

    ``theta0``/``sigma``/``A`` are ``(Nfr,)`` (one Gaussian) or ``(n_gauss, Nfr)``.
    """
    thetap = np.asarray(thetap, dtype=float)
    theta0 = np.atleast_2d(np.asarray(theta0, dtype=float))
    sigma = np.atleast_2d(np.asarray(sigma, dtype=float))
    A = np.atleast_2d(np.asarray(A, dtype=float))
    Nfr = theta0.shape[1]
    XT_syn = np.zeros((Nb, Nfr))
    for g in range(theta0.shape[0]):
        dx = np.mod(thetap[None, :] - theta0[g][:, None] + np.pi, _TWO_PI) - np.pi
        XT_syn += (A[g][:, None] * np.exp(-(dx ** 2) / (2.0 * sigma[g][:, None] ** 2))).T
    return XT_syn


def xt_prepper(XT, Nfr, Nb, theta0, sigma, A):
    """Subtract 2x the synthesized wave (one or more Gaussians).

    Port of ``XT_Prepper`` in Gauss_Opt_Runner.m.  ``n_gauss=1`` (``theta0``/``sigma``/
    ``A`` each ``(Nfr,)``) is byte-for-byte the reference; ``n_gauss=2`` (each
    ``(2, Nfr)``) removes both Gaussians of the system.
    """
    thetap_syn = np.arange(Nb) * (_TWO_PI / Nb)
    XT_syn = _gauss_synth(Nb, thetap_syn, theta0, sigma, A)
    XT_cleared = XT - 2.0 * XT_syn
    XT_cleared[XT_cleared < 0] = 0
    return XT_cleared
