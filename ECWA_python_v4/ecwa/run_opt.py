#!/usr/bin/env python
# Author: Timothy J. Welch
"""Three-wave Gaussian optimizer runner (port of ECWA_MATLAB/Gauss_Opt_Runner.m).

Velocity: ``v{i} = firstNonNaN(plot4.v{i}) * Dcj``, held constant (the CWA
detection series is sometimes mislabelled, so its mean is not a reliable
velocity). ``Dcj = Ucj(phi)/Cd * 2*pi``.

Fit: the three wave systems are fit JOINTLY by coordinate descent on
``XT_clean = clean(XT)`` (per-sensor min over 20-frame blocks).  Each system is
(re)fit with the *other* systems' 1x contribution removed -- a proper
simultaneous decomposition, not the sequential 2x over-subtraction that
distorts the residual and hides companion waves.  For each system BOTH a
1-Gaussian and a 2-Gaussian model are fit; the 2-Gaussian model is kept only if
its second wave beats the local noise floor in its own region (a relative
signal-to-noise test, no dataset-specific threshold).  So the number of waves
per system is chosen by the data, not the user.

Each wave's ``(theta0, sigma, A, v)`` is written to ``wave{i}_opt_results.mat``.
Note: the reference fits sigma with ``fmincon`` (SQP, nonsmooth L1 objective); the
port uses ``minimize_scalar`` (bounded Brent) which returns the true 1-D minimum.
``theta0``/``A``/``v`` reproduce the reference to ~1e-12 (one boundary frame apart);
``sigma`` differs on a few hundred frames because the reference solver is suboptimal
on the kinked objective. See the validation notes.
"""
import os
import numpy as np
from scipy.io import loadmat, savemat

from .core import clean_xt, _gauss_synth
from .opt import auto_select_waves
from .io import load_xt_full
from common.det_props import load_det_props, ucj_at_phi

__all__ = ["dcj_at", "gauss_opt_runner"]


def dcj_at(phi, Dm, det_props_path):
    """Dcj = Ucj(phi)/Cd * 2*pi, with Cd = Dm*pi*0.0254 (in -> m)."""
    Ucj = ucj_at_phi(load_det_props(det_props_path), phi)
    Cd = Dm * np.pi * 0.0254
    return Ucj / Cd * 2.0 * np.pi


def _save_wave_mat(fname, res):
    """Write a chosen fit: n_gauss=1 -> column vectors, n_gauss=2 -> 2-row blocks
    (the synthesis infers the count from the ``theta0`` shape)."""
    from scipy.io import savemat
    th, sig, A, v = res
    if np.asarray(th).ndim == 1:
        savemat(fname, {"theta0": th.reshape(-1, 1), "sigma": sig.reshape(-1, 1),
                        "A": A.reshape(-1, 1), "v": v.reshape(-1, 1)})
    else:
        savemat(fname, {"theta0": th, "sigma": sig, "A": A, "v": v.reshape(-1, 1)})


def gauss_opt_runner(XT, t, fps, phi, Dm, det_props_path, plot4, out_dir,
                     win=20, log=True, max_iter=6):
    """Run the three sequential wave-system optimizations (automatic 1-vs-2 waves).

    For each wave system BOTH a 1-Gaussian and a 2-Gaussian model are fit on that
    system's layer; the 2-Gaussian model is kept only if its second wave beats the
    local noise floor in its own region (a relative signal-to-noise test, no
    dataset-specific threshold).  So the number of waves per system is chosen by the
    data, not the user.  ``plot4`` is a struct-like object with array attributes
    ``vdets``, ``vcrwps``, ``vcdets``.
    Returns a dict ``{"wave1": (th,sig,A,v), ...}`` and writes
    ``wave{i}_opt_results.mat`` under ``out_dir``.
    """
    Nb, Nfr = XT.shape
    thetap = np.arange(Nb) * (2.0 * np.pi / Nb)
    Dcj = dcj_at(phi, Dm, det_props_path)
    if log:
        print(f"Nb={Nb} Nfr={Nfr} Dcj={Dcj:.6f}", flush=True)

    XT_clean = clean_xt(XT, win=win)
    # The CWA detection series is sometimes mislabelled, so its mean is not a
    # reliable system velocity. Use the first non-NaN detection value, held
    # constant across the record, as each system's velocity instead.
    def _first_nonnan_vel(raw):
        a = np.asarray(raw, float).ravel()
        valid = a[~np.isnan(a)]
        val = float(valid[0]) if valid.size else 0.0
        return np.full(a.shape, val) * Dcj
    v1 = _first_nonnan_vel(plot4.vdets)
    v2 = _first_nonnan_vel(plot4.vcrwps)
    v3 = _first_nonnan_vel(plot4.vcdets)

    os.makedirs(out_dir, exist_ok=True)
    names = [("wave1", v1), ("wave2", v2), ("wave3", v3)]
    n_sys = len(names)

    # Joint coordinate-descent fit of all systems on XT_clean.  Each system is
    # (re)fit with the *other* systems' 1x contribution removed -- a proper
    # simultaneous decomposition, not the sequential 2x over-subtraction that
    # distorts the residual and hides companion waves.  The asynchronous descent
    # wobbles slightly, so keep the iteration with the lowest total residual.
    results = [None] * n_sys
    best, best_resid = None, np.inf
    for it in range(max_iter):
        for k in range(n_sys):
            others = np.zeros_like(XT_clean)
            for j in range(n_sys):
                if j != k and results[j] is not None:
                    sj = results[j][0]
                    others += _gauss_synth(Nb, thetap, sj[0], sj[1], sj[2])
            X_k = np.maximum(XT_clean - others, 0.0)
            results[k] = auto_select_waves(X_k, Nfr, Nb, thetap, t, names[k][1])
        total = np.zeros_like(XT_clean)
        for r in results:
            total += _gauss_synth(Nb, thetap, r[0][0], r[0][1], r[0][2])
        resid = float(np.abs(XT_clean - total).sum())
        flags = [2 if np.asarray(r[0][0]).ndim == 2 else 1 for r in results]
        if log:
            print(f"  joint iter {it + 1}: residual={resid:.4g} waves={flags}", flush=True)
        if resid < best_resid:
            best_resid = resid
            best = list(results)          # arrays are not mutated in later iterations
    results = best

    waves = {}
    for k, (name, vel) in enumerate(names):
        res, use2, R1, R2 = results[k]
        a1 = float(abs(res[2][0][0])) if use2 else float(abs(res[2][0]))
        a2 = float(abs(res[2][1][0])) if use2 else 0.0
        if log:
            print(f"[{name}] R1={R1:.4g} R2={R2:.4g} "
                  f"reduction={100.0 * (R1 - R2) / R1:.1f}% A2/A1={a2 / a1 if a1 else 0:.2f}"
                  f" -> waves={2 if use2 else 1}",
                  flush=True)
        _save_wave_mat(os.path.join(out_dir, f"{name}_opt_results.mat"), res)
        waves[name] = res
    return waves


if __name__ == "__main__":
    # Self-contained convenience: compute the CWA (plot4) via cwa/ and read the
    # detector properties from cwa/ -- no CWA_MATLAB sibling needed.
    from cwa.cwa import cwa
    ROOT = "/Users/tjwelch/Desktop/APCL/research_projects/project_A/conversion_partition"
    _V4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # ECWA_python_v4
    run = 3433
    phi, Dm = 1.46, 5.76
    XT, t0, fps = load_xt_full(ROOT, run)
    t = np.arange(XT.shape[1]) / fps + t0
    det_path = os.path.join(_V4, "cwa", "H2AirDetProp.xlsx")
    cwa_res = cwa({}, {"XT": XT, "t0": t0, "fps": fps}, phi, Dm, [],
                  load_det_props(det_path))
    plot4 = {k: np.asarray(v) for k, v in cwa_res["plot4"].items()}
    out_dir = os.path.join(_V4, "results", f"run{run}data")
    gauss_opt_runner(XT, t, fps, phi, Dm, det_path, plot4, out_dir, log=True)
    print("saved to", out_dir)
