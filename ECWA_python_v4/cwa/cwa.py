#!/usr/bin/env python
# Author: Timothy J. Welch
"""Core CWA analysis ported from CWA_MATLAB/CWA.m.

This module implements the *time-resolved* phase-shifted analysis
(``PhaseShiftTimeAnalysis`` in CWA.m, lines 362-671) which is the part that
produces the ``plot4`` struct consumed downstream by the ECWA Gaussian
reconstruction pipeline.  ``plot4`` depends only on the *full* XT diagram plus
the run parameters (``phi``, ``Dm``); it is independent of the short diagram
and the ``times`` window (those feed the single-block plot1/plot2/plot3
section, which is added separately for completeness).

Fidelity notes
--------------
* Index bases are translated 1-based (MATLAB) -> 0-based (NumPy) at every
  slice; the ``round(Na/2)`` pivot uses MATLAB's round-half-away-from-zero.
* The circular spatial shift (``circshift``) is vectorised with
  ``take_along_axis`` -- identical to the per-row ``circshift`` in the source.
* The Radon geometry (line intersections, sorting, nearest-bin lookup) is
  independent of the time block ``m`` (it depends only on the wave index ``n``
  and the fixed ``f``/``a_tr`` grids), so it is precomputed once per wave and
  the per-block work reduces to a masked gather plus the diagonal selection
  that the reference ``diag(countsM)`` performs.
"""
import numpy as np

from .xt_reader import xt_reader
from common.interp import interp1
from common.det_props import ucj_at_phi

__all__ = ["cwa", "phase_shift_time_analysis", "build_plot4",
           "_matlab_round", "_nearest_idx", "_intersect2vec"]


# ---------------------------------------------------------------------------
# small numeric helpers
# ---------------------------------------------------------------------------
def _matlab_round(x):
    """MATLAB ``round`` (halves away from zero)."""
    x = np.asarray(x, dtype=float)
    return np.sign(x) * np.floor(np.abs(x) + 0.5)


def _nearest_idx(grid, x):
    """Index (0-based) of the nearest value in a strictly increasing ``grid``.

    Reproduces MATLAB ``[~, k] = min(abs(x - grid))`` (ties -> lower index) for
    every element of ``x`` via a binary search, which is exact for a sorted grid.
    NaN queries return a valid in-range index (they never reach the diagonal in
    practice because the corresponding segment length is zeroed).
    """
    grid = np.asarray(grid, dtype=float)
    x = np.asarray(x, dtype=float)
    i = np.searchsorted(grid, x, side="left")
    i = np.clip(i, 1, grid.size - 1)
    il = i - 1
    dl = np.abs(x - grid[il])
    dh = np.abs(x - grid[i])
    return np.where(dh < dl, i, il)


def _intersect2vec(L1, L2):
    """Vectorised line/segment intersection.  Port of nested ``intersect2vec``.

    ``L1``/``L2`` are ``(n, 4)`` arrays ``[x0, y0, xhat, yhat]``; returns
    ``(X, Y)`` of shape ``(rows(L2), rows(L1))``.
    """
    L1 = np.array(L1, dtype=float, copy=True)
    L2 = np.array(L2, dtype=float, copy=True)
    x1, y1 = L1[:, 0], L1[:, 1]
    x2, y2 = L2[:, 0], L2[:, 1]
    L1[L1[:, 2] == 0, 2] = 1e-10
    L1[L1[:, 3] == 0, 3] = 1e-10
    L2[L2[:, 2] == 0, 2] = 1e-10
    L2[L2[:, 3] == 0, 3] = 1e-10
    m1 = L1[:, 3] / L1[:, 2]
    m2 = L2[:, 3] / L2[:, 2]
    a1 = m1[None, :]
    a2 = m2[:, None]
    b1 = -np.ones((1, m1.size))
    b2 = -np.ones((m2.size, 1))
    c1 = (y1 - m1 * x1)[None, :]
    c2 = (y2 - m2 * x2)[:, None]
    den = a1 * b2 - a2 * b1
    X = (b1 * c2 - b2 * c1) / den
    Y = (a2 * c1 - a1 * c2) / den
    return X, Y


def _phase_sweep_block(inter, a_tr, fps, Cd):
    """FFT-power (collapsed over sensors) for every phase-shift ``a_tr``.

    ``inter`` is the spatially-interpolated block (Nfr, Nb); returns
    ``(len(a_tr), nFreqBins)`` where ``nFreqBins = (Nfr-1)/2+1`` (Nfr trimmed
    to even).  Equivalent to looping ``circshift`` + ``fftwrap`` per ``a``.
    """
    Nfr_b, Nb_b = inter.shape
    a = a_tr[:, None, None]
    k = np.arange(Nfr_b)[None, :, None]
    s = (Cd * np.arange(Nb_b))[None, None, :] / Nb_b
    phish_raw = a * k / fps + s
    phishM = phish_raw - Cd * np.floor(phish_raw / Cd)
    shiftIdx = (np.argmax(phishM, axis=2) + 1)                 # MATLAB 1-based
    cols = (np.arange(Nb_b)[None, None, :] - shiftIdx[:, :, None]) % Nb_b
    vals = np.take_along_axis(np.broadcast_to(inter[None, :, :], phishM.shape), cols, axis=2)
    L = Nfr_b if Nfr_b % 2 == 0 else Nfr_b - 1
    vals = vals[:, :L, :]
    y = np.fft.fft(vals, axis=1)
    P2 = np.abs(y) / L
    P = P2[:, :L // 2 + 1, :]
    P[:, 1:L // 2, :] = 2 * P[:, 1:L // 2, :]
    return np.max(P, axis=2)


def _radon_geometry_time(a_tr, f, bf_ext, ba_ext, inda0, waveL):
    """Precompute the per-wave Radon gather (m-independent) for the time analysis.

    Returns, for each wave ``n`` (1..waveL), a tuple ``(disMM, IfMM0, IaMM0)`` of
    shape ``(Nlocs, Na)`` each.  The reference computes
    ``countsM = ftpnew(indCM') * disMM`` -- a **matrix product** -- and then
    ``lights(n,:) = diag(countsM)'``, which equals the line integral
    ``sum_k ftpnew(IaMM0[k,i], IfMM0[k,i]) * disMM[k,i]`` over every segment
    ``k`` for each trace ``i``.  Because the geometry depends only on ``n`` and
    the fixed ``f``/``a_tr`` grids (not the block ``m``), these arrays are
    built once per wave.
    """
    Na = len(a_tr)
    Nbf = len(bf_ext)
    Nba = len(ba_ext)
    Nlocs = 2 * Nbf + Nba + 1
    geo = []
    for n in range(1, waveL + 1):
        mLp = np.array([n, 1.0]); mLp /= np.linalg.norm(mLp)
        mLm = np.array([n, -1.0]); mLm /= np.linalg.norm(mLm)
        posM = np.column_stack([np.zeros(Na), a_tr, np.full(Na, mLp[0]), np.full(Na, mLp[1])])
        negM = np.column_stack([np.zeros(Na), a_tr, np.full(Na, mLm[0]), np.full(Na, mLm[1])])
        Xfp, Yfp = _intersect2vec(posM, bf_ext)
        Xfm, Yfm = _intersect2vec(negM, bf_ext)
        Xap, Yap = _intersect2vec(posM, ba_ext)
        Xam, Yam = _intersect2vec(negM, ba_ext)
        Xa = Xap.copy(); Xa[inda0] = Xam[inda0]
        Ya = Yap.copy(); Ya[inda0] = Yam[inda0]

        locsXM = np.zeros((Nlocs, Na))
        locsYM = np.zeros((Nlocs, Na))
        locsXM[0:2 * Nbf:2] = Xfp
        locsXM[1:2 * Nbf:2] = Xfm
        locsYM[0:2 * Nbf:2] = Yfp
        locsYM[1:2 * Nbf:2] = Yfm
        locsXM[2 * Nbf:2 * Nbf + Nba] = Xa
        locsYM[2 * Nbf:2 * Nbf + Nba] = Ya
        locsYM[2 * Nbf + Nba] = a_tr                    # ray origin (0, a)

        tar1 = locsXM < f[-1]
        tar2 = (locsYM > a_tr[0]) & (locsYM < a_tr[-1])
        keep = tar1 & tar2
        locsXM[~keep] = np.nan
        locsYM[~keep] = np.nan

        IM = np.argsort(locsYM, axis=0)
        locsXM = np.take_along_axis(locsXM, IM, axis=0)
        locsYM = np.take_along_axis(locsYM, IM, axis=0)
        locs2XM = np.vstack([locsXM[1:], np.zeros((1, Na))])
        locs2YM = np.vstack([locsYM[1:], np.zeros((1, Na))])
        disMM = np.sqrt((locsXM - locs2XM) ** 2 + (locsYM - locs2YM) ** 2)
        disMM[np.isnan(disMM)] = 0.0
        midXM = (locsXM + locs2XM) / 2
        midYM = (locsYM + locs2YM) / 2
        IfMM0 = _nearest_idx(f, midXM).astype(np.intp)
        IaMM0 = _nearest_idx(a_tr, midYM).astype(np.intp)
        geo.append((disMM, IfMM0, IaMM0))
    return geo


# ---------------------------------------------------------------------------
# time-resolved analysis -> the source of plot4
# ---------------------------------------------------------------------------
def phase_shift_time_analysis(lights_full, t_full, fps_full, Cd, Ucj, fD,
                              Vr=150, dv=20):
    """Port of CWA.m ``PhaseShiftTimeAnalysis`` (full/time-resolved data)."""
    Nfr_full, Nb_full = lights_full.shape
    lights_full = lights_full - np.mean(lights_full)

    a_tr_raw = np.arange(-3000, 3000 + dv, dv)          # -3000:20:3000
    Na = a_tr_raw.size
    Nfr = 71
    Ntp = int(np.floor(len(t_full) / Nfr))
    nFreqBins = (Nfr - 1) // 2 + 1                       # 36
    L = Nfr - 1                                          # trimmed even length

    vecb_full = np.linspace(0, Cd, Nb_full)
    query = Cd * np.arange(Nb_full) / Nb_full

    ftpsomega = np.zeros((Na, nFreqBins, Ntp))
    ttp = np.zeros(Ntp)
    for m in range(Ntp):
        c0, c1 = m * Nfr, (m + 1) * Nfr
        subxt = lights_full[c0:c1, :]
        ttp[m] = float(np.mean(t_full[c0:c1]))
        inter = interp1(vecb_full, subxt.T, query).T     # (Nfr, Nb)
        ftpsomega[:, :, m] = _phase_sweep_block(inter, a_tr_raw, fps_full, Cd)

    f = (fps_full * np.arange(nFreqBins) / L) / fD
    a_tr = a_tr_raw / Ucj
    a0 = int(_matlab_round(Na / 2))                      # 1-based pivot (151)
    a0z = a0 - 1                                         # 0-based pivot (150)
    Nf = f.size
    da = a_tr[1] - a_tr[0]
    df = f[1] - f[0]

    i0 = int(np.argmin(np.abs(a_tr - 1)))
    i1 = int(np.argmin(np.abs(a_tr - 1.5)))
    i2 = int(np.argmin(np.abs(a_tr + 1)))
    i3 = int(np.argmin(np.abs(a_tr - 1)))                # == i0
    i4 = int(np.argmin(np.abs(f - 0.08)))
    i5 = int(np.argmin(np.abs(a_tr - 0.3)))
    i6 = int(np.argmin(np.abs(a_tr + 0.3)))

    waveL = 5
    lights_t = np.zeros((waveL, Na, Ntp))
    vdets = np.zeros(Ntp); detins = np.zeros(Ntp); Ndets = np.zeros(Ntp)
    vcdets = np.zeros(Ntp); cdetins = np.zeros(Ntp)
    vcrwps = np.zeros(Ntp); crwpins = np.zeros(Ntp)

    bf = f[:Nf - 1] + 0.5 * df
    ba = a_tr[:Na - 1] + 0.5 * da
    bf_ext = np.column_stack([bf, np.zeros(Nf - 1), np.zeros(Nf - 1), np.ones(Nf - 1)])
    ba_ext = np.column_stack([np.zeros(Na - 1), ba, np.ones(Na - 1), np.zeros(Na - 1)])
    inda0 = ba_ext[:, 1][:, None] <= a_tr[None, :]
    geo = _radon_geometry_time(a_tr, f, bf_ext, ba_ext, inda0, waveL)

    delwin = int(np.floor(Vr / dv))                      # 7
    s0 = np.min(ftpsomega, axis=0).T                     # (Ntp, nFreqBins)

    for m in range(Ntp):
        ftp = ftpsomega[:, :, m]
        background = np.tile(s0[m], (Na, 1))
        ftpnew = ftp - background
        lights = np.zeros((waveL, Na))
        for n in range(1, waveL + 1):
            disMM, IfMM0, IaMM0 = geo[n - 1]
            # line integral: sum over every segment k for each trace i
            lights_n = (ftpnew[IaMM0, IfMM0] * disMM).sum(axis=0)
            if n > 1:
                lightsP = np.roll(lights_n, -1)
                lightsM = np.roll(lights_n, 1)
                indM = (lights_n > lightsP) | (lights_n > lightsM)
                indM[0] = False
                indM[-1] = False
                amin = a_tr[~indM]
                lightsmin = lights_n[~indM]
                lightsoff = interp1(amin, lightsmin, a_tr)
                lights_n = lights_n - lightsoff
            else:
                lights_n = lights_n - np.mean(lights_n[0:(i1 - i0)])
            lights_n = lights_n - np.min(lights_n)
            lights[n - 1] = lights_n
        lights_t[:, :, m] = lights

        # detection (in-place, after lights_t stored -- mirrors CWA.m)
        lights[:, i6:i5 + 1] = 0
        background_th = 4 * np.sqrt(np.mean(lights[1, i0:i1 + 1] ** 2))
        lights[:, 0:i2 + 1] = 0
        lights[:, i3:] = 0
        lights[lights < background_th] = 0

        maxes = np.max(lights, axis=1)
        detn = int(np.argmax(maxes))
        Idet = int(np.argmax(lights[detn, :]))
        if Idet <= 0:                                    # MATLAB: Idet <= 1
            vdets[m] = detins[m] = Ndets[m] = np.nan
            vcdets[m] = cdetins[m] = vcrwps[m] = crwpins[m] = np.nan
        else:
            p = _quadfit(a_tr[Idet - delwin:Idet + delwin + 1],
                         lights[detn, Idet - delwin:Idet + delwin + 1])
            vdets[m] = -p[1] / (2 * p[0])
            Ndets[m] = detn + 1
            detins[m] = ftpnew[Idet, 0:i4 + 1].sum()
            if vdets[m] > 0:
                lights[:, a0z:] = 0
            else:
                lights[:, :a0z + 1] = 0
            v1 = np.max(lights[0]); Icdet = int(np.argmax(lights[0]))
            if v1 > 0:
                # Fit the *gate* plane (lights[0], 1-based lights(1)). The
                # original CWA.m read lights(detn, ...) here -- a cross-plane
                # slip that is harmless when detn==1 but makes the quadratic
                # degenerate (p[0]=0 -> vcdets NaN) for lean runs where detn!=1.
                # (vcrwps below already fits its gate plane correctly.)
                p = _quadfit(a_tr[Icdet - delwin:Icdet + delwin + 1],
                             lights[0, Icdet - delwin:Icdet + delwin + 1])
                vcdets[m] = -p[1] / (2 * p[0])
                cdetins[m] = ftpnew[Icdet, 0:i4 + 1].sum()
            else:
                vcdets[m] = cdetins[m] = np.nan
            v2 = np.max(lights[1]); Icrwp = int(np.argmax(lights[1]))
            if v2 > 0:
                p = _quadfit(a_tr[Icrwp - delwin:Icrwp + delwin + 1],
                             lights[1, Icrwp - delwin:Icrwp + delwin + 1])
                vcrwps[m] = -p[1] / (2 * p[0])
                crwpins[m] = ftpnew[Icrwp, 0:i4 + 1].sum()
            else:
                vcrwps[m] = crwpins[m] = np.nan

    return dict(ttp=ttp, vdets=vdets, detins=detins, vcdets=vcdets,
                cdetins=cdetins, vcrwps=vcrwps, crwpins=crwpins,
                Ndets=Ndets, lights_t=lights_t, a_tr=a_tr)


def _quadfit(x, y):
    from .helpers import quadfit
    return quadfit(x, y)


# ---------------------------------------------------------------------------
# plot4 assembly
# ---------------------------------------------------------------------------
def build_plot4(pst, Ntp):
    """Assemble the ``plot4`` struct from the time-resolved results (CWA.m 648-671)."""
    detins = pst["detins"].astype(float)
    cdetins = pst["cdetins"].astype(float)
    crwpins = pst["crwpins"].astype(float)

    with np.errstate(divide="ignore", invalid="ignore"):
        # CWA.m: intens = [detins cdetins crwpins]  -> horizontal concat (1, 3*Ntp)
        intens = np.concatenate([np.log(detins), np.log(cdetins), np.log(crwpins)])
        log_detins = np.log(detins)
        log_cdetins = np.log(cdetins)
        log_crwpins = np.log(crwpins)
    intens = np.where(np.isinf(intens), np.nan, intens)
    maxI = float(np.nanmax(intens))
    minI = float(np.nanmin(intens))

    return {
        "intens": intens,
        "detins": log_detins,
        "cdetins": log_cdetins,
        "crwpins": log_crwpins,
        "maxI": maxI,
        "minI": minI,
        "ttp": pst["ttp"],
        "vdets": pst["vdets"],
        "vcdets": pst["vcdets"],
        "vcrwps": pst["vcrwps"],
        "Ntp": int(Ntp),
    }


# ---------------------------------------------------------------------------
# top-level
# ---------------------------------------------------------------------------
def cwa(XTStruct, XTStruct_full, phi, Dm, times, dat):
    """Port of CWA.m.

    Currently computes the ``plot4`` struct (the ECWA-relevant artifact) from the
    full XT diagram, and the supporting ``PSTA`` time-resolved struct.  The
    single-block ``plot1``/``plot2``/``plot3``/``PSD`` (short diagram + ``times``)
    is provided by :func:`cwa_single_block` and merged in :func:`run`.
    """
    Ucj = ucj_at_phi(dat, phi)
    Cd = Dm * np.pi * 0.0254
    fD = Ucj / Cd

    t_full, _, lights_full, fps_full, Nb_full = xt_reader(XTStruct_full)
    lights_full = lights_full.T                            # (time, sensor)
    Nfr_full = lights_full.shape[0]

    pst = phase_shift_time_analysis(lights_full, t_full, fps_full, Cd, Ucj, fD)
    plot4 = build_plot4(pst, int(np.floor(Nfr_full / 71)))

    return {
        "Ucj": Ucj, "Cd": Cd, "fD": fD,
        "PSTA": pst, "plot4": plot4,
        "_full": (t_full, lights_full, fps_full, Nb_full),
    }
