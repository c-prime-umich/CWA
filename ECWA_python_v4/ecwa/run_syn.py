#!/usr/bin/env python
# Author: Timothy J. Welch
"""Gaussian synthesis runner (port of ECWA_MATLAB/Gauss_Syn_Runner.m).

Faithfully reproduces the reference:
  * ``XT.csv`` / ``dt.csv`` from the original full XT;
  * background removal (20-frame per-sensor min) -> ``BG.csv`` (every 20th frame);
  * for each wave: load ``wave{i}_opt_results.mat`` (theta0/sigma/A/v, full rate),
    double-smooth ``movmean(movmean(x,1000),1000)``, reduce ``1:20:end``, and
    ``add_wave`` (advect theta from ``theta0(1)`` with the smoothed velocity);
  * ``wave_sys_{i}/theta0.csv`` (scalar), ``sigma.csv``/``A.csv``/``v.csv`` (reduced);
  * ``epsilon = checker(XT, XT_syn + (XT - XT_cleaned))``;
  * the seven reference figures.

The ``mat_dir`` argument selects the optimisation source so the synthesis can be
validated against the reference ``.mat``s (exact) or against the ported optimiser
(sigma differs on fmincon-suboptimal frames).
"""
import os
import shutil
import numpy as np
from scipy.io import loadmat

from .core import clean_xt, movmean, add_wave, checker
from .io import load_xt_full

__all__ = ["gauss_syn_runner"]

_WIN = 20
_K = 1000


def _dsmooth(x):
    """movmean(movmean(x, K), K) -- the reference's double smoothing."""
    return movmean(movmean(np.asarray(x, float).ravel(), _K), _K)


def _reduce(x):
    """1 : win : end (every 20th element)."""
    return x[0::_WIN]


def _reduce_wave(mat_dir, i):
    """Load ``wave{i}_opt_results.mat`` (full rate), double-smooth + reduce, and
    return the reduced series as a ``make_waves``-layout dict
    ``{"th0": (n_g,), "A": (n_g, n_t), "sig": (n_g, n_t), "v": (n_t,)}``.

    This is exactly the reference's per-wave reduce step, factored out so the
    synthesis can either (a) add it straight in with ``add_wave`` (the v1-v3
    behaviour) or (b) hand the reduced series to the PECWA_julia MAP re-fit and
    synthesise the improved one."""
    m = loadmat(os.path.join(mat_dir, f"wave{i}_opt_results.mat"), squeeze_me=True)
    th0_raw = np.asarray(m["theta0"], float)
    sig_raw = np.asarray(m["sigma"], float)
    A_raw = np.asarray(m["A"], float)
    v_raw = np.asarray(m["v"], float)
    # n_gauss=1: theta0 is (Nfr,); n_gauss=2: theta0 is (2, Nfr)
    n_gauss = th0_raw.shape[0] if th0_raw.ndim == 2 else 1
    theta0_starts, sig_red, A_red = [], [], []
    for g in range(n_gauss):
        th0_g = th0_raw[g] if n_gauss > 1 else th0_raw
        sig_g = sig_raw[g] if n_gauss > 1 else sig_raw
        A_g = A_raw[g] if n_gauss > 1 else A_raw
        theta0_starts.append(float(np.asarray(th0_g, float).ravel()[0]))
        sig_red.append(_reduce(_dsmooth(np.asarray(sig_g, float).ravel())))
        A_red.append(_reduce(_dsmooth(np.asarray(A_g, float).ravel())))
    v_red = _reduce(_dsmooth(np.asarray(v_raw, float).ravel()))
    return {"th0": np.array(theta0_starts), "A": np.array(A_red),
            "sig": np.array(sig_red), "v": v_red, "n_gauss": n_gauss}


def _write_csv(path, arr):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    np.savetxt(path, np.atleast_1d(arr).ravel(), delimiter=",")


def gauss_syn_runner(XT, t, fps, mat_dir, out_dir, plot=True, movie=False,
                     re_fit=False, re_fit_kernel="gauss", re_fit_K=1,
                     re_fit_thin=1, re_fit_maxiter=1500, re_fit_gtol=1e-8,
                     re_fit_nu0=None, re_fit_log=True):
    """Run the synthesis.  Returns ``{"epsilon", "XT_syn", "XT_cleaned", "XT_subtraction"}``.

    ``plot`` writes the PNG figures; ``movie`` additionally writes a sliding-window
    animation (mp4/gif) for each x-t diagram.

    With ``re_fit=True`` each wave's reduced series (full-rate mat -> double-smooth
    -> every-20th) is warm-started into the PECWA_julia MAP re-fit
    (``re_fit_kernel`` / ``re_fit_K``) and the *improved* reduced series is what
    gets synthesised.  With ``re_fit=False`` (default) the reference v1-v3 behaviour
    is preserved exactly (the reduced series is added straight in with ``add_wave``).
    """
    Nb, Nfr = XT.shape
    thetap = np.arange(Nb) * (2.0 * np.pi / Nb)
    dt = t[1] - t[0]

    os.makedirs(out_dir, exist_ok=True)
    np.savetxt(os.path.join(out_dir, "XT.csv"), XT, delimiter=",")
    _write_csv(os.path.join(out_dir, "dt.csv"), dt)

    # background removal
    XT_cleaned = clean_xt(XT, win=_WIN)
    XT_subtraction = XT - XT_cleaned
    np.savetxt(os.path.join(out_dir, "BG.csv"), XT_subtraction[:, 0::_WIN], delimiter=",")

    # pass 1: the per-wave reduced series (full-rate mat -> double-smooth -> reduce)
    reduced_waves = [_reduce_wave(mat_dir, i) for i in range(1, 4)]
    Nt = reduced_waves[0]["v"].size

    if re_fit:
        # PECWA_julia MAP re-fit of the reduced series, then synthesise the
        # improved waves (synthesize_waves handles K-component profiles that the
        # reference add_wave cannot).
        from .maprefit import map_refit, synthesize_waves
        ws = reduced_waves
        if re_fit_K > 1 and re_fit_kernel == "gauss":
            # two-stage: Gaussian re-fit first, then K re-fit from that warm start
            # (matches the driver's K-Gaussian; the K re-fit from the base is worse)
            ws, _, _, _, _ = map_refit(
                XT, XT_subtraction, reduced_waves, dt, Nfr, thetap,
                kernel="gauss", thin=re_fit_thin, maxiter=re_fit_maxiter,
                gtol=re_fit_gtol, log=re_fit_log)
        refit_waves, nu, sigN, sigP, _ = map_refit(
            XT, XT_subtraction, ws, dt, Nfr, thetap,
            kernel=re_fit_kernel, thin=re_fit_thin, maxiter=re_fit_maxiter,
            gtol=re_fit_gtol, nu0=re_fit_nu0, K=re_fit_K, log=re_fit_log)
        XT_syn = synthesize_waves(thetap, refit_waves, dt, Nfr, Nt,
                                  kernel=re_fit_kernel, nu=nu, sigN=sigN,
                                  sigP=sigP)
        wave_series = refit_waves
    else:
        # reference v1-v3 behaviour: add the reduced series straight in with add_wave
        XT_syn = np.zeros((Nb, Nfr))
        for w in reduced_waves:
            n_gauss = w["n_gauss"]
            XT_syn = add_wave(XT_syn, Nfr, thetap,
                              w["th0"] if n_gauss > 1 else w["th0"][0],
                              w["v"],
                              w["A"] if n_gauss > 1 else w["A"][0],
                              w["sig"] if n_gauss > 1 else w["sig"][0],
                              dt, win=_WIN)
        wave_series = reduced_waves

    # save the (re-fit or reference) reduced series as wave_sys_{i}
    for i, w in enumerate(wave_series, start=1):
        th0 = np.atleast_1d(np.asarray(w["th0"], float))
        A = np.asarray(w["A"], float)
        sig = np.asarray(w["sig"], float)
        v = np.asarray(w["v"], float).ravel()
        if A.ndim == 2:                       # (n_g, n_t) -> treat as K=1
            A = A[:, None, :]; sig = sig[:, None, :]
        n_g, Kc, _ = A.shape
        wf = os.path.join(out_dir, f"wave_sys_{i}")
        shutil.rmtree(wf, ignore_errors=True)   # drop stale per-gaussian files
        _write_csv(os.path.join(wf, "theta0.csv"), th0)
        if Kc == 1:
            if n_g == 1:
                _write_csv(os.path.join(wf, "A.csv"), A[0, 0])
                _write_csv(os.path.join(wf, "sigma.csv"), sig[0, 0])
            else:
                for g in range(n_g):
                    _write_csv(os.path.join(wf, f"A_{g + 1}.csv"), A[g, 0])
                    _write_csv(os.path.join(wf, f"sigma_{g + 1}.csv"), sig[g, 0])
        else:                                 # K-component profile (re-fit K>1)
            for g in range(n_g):
                for c in range(Kc):
                    _write_csv(os.path.join(wf, f"A_{g + 1}c{c + 1}.csv"), A[g, c])
                    _write_csv(os.path.join(wf, f"sigma_{g + 1}c{c + 1}.csv"), sig[g, c])
        _write_csv(os.path.join(wf, "v.csv"), v)

    XT_syn_tot = XT_syn + XT_subtraction
    epsilon = checker(XT, XT_syn_tot)

    if plot or movie:
        from .plots import save_all_figures
        save_all_figures(t, fps, thetap, XT, XT_cleaned, XT_syn, XT_subtraction,
                         out_dir, win=_WIN, movie=movie)

    return {"epsilon": epsilon, "XT_syn": XT_syn, "XT_cleaned": XT_cleaned,
            "XT_subtraction": XT_subtraction}


if __name__ == "__main__":
    ROOT = "/Users/tjwelch/Desktop/APCL/research_projects/project_A/conversion_partition"
    run = 3433
    XT, t0, fps = load_xt_full(ROOT, run)
    t = np.arange(XT.shape[1]) / fps + t0
    out_dir = os.path.join(ROOT, "ECWA_python_v4", "results", f"run{run}data")
    # Default: synthesize from the PORTED optimiser output (ECWA_python_v4/results/...).
    mat_dir = out_dir
    res = gauss_syn_runner(XT, t, fps, mat_dir, out_dir, plot=True)
    print(f"epsilon = {res['epsilon']:.10e}")
