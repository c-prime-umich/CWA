#!/usr/bin/env python
# Author: Timothy J. Welch
"""Per-frame single-wave Gaussian optimizer (port of ECWA_MATLAB/Gauss_Wave_Opt.m).

For each frame the wave amplitude ``A`` and centre ``theta0`` are read off the
data, and the Gaussian width ``sigma`` is fit in the window ``[0.1, 0.7]`` by
minimising the L1 mismatch.  The reference uses ``fmincon`` (SQP) from ``p0=0.3``;
the port uses ``scipy.optimize.minimize_scalar`` (Brent, bounded) -- a 1-D solver
that converges to the same minimum for this unimodal objective.  ``theta0`` and
the search window ``low_j/up_j`` are tracked frame-to-frame exactly as in the
source.

``theta0``/``up_j``/``low_j`` are kept in 1-based indexing internally to mirror the
MATLAB logic and translated to 0-based only at array access.
"""
import numpy as np
from scipy.optimize import minimize_scalar

from .core import periodic_gaussian, _gauss_synth

__all__ = ["gauss_wave_opt", "auto_select_waves", "_fit_residual"]

_TWO_PI = 2.0 * np.pi


def _gauss_wave_opt_1(XT, Nfr, Nb, thetap, t, vdets, fname=None, progress_every=0):
    """v1: optimise one wave (a single periodic Gaussian) across all frames.

    Returns ``(theta0, sigma, A, v)`` (each ``(Nfr,)``).  When ``fname`` is given
    the result is also written as a MATLAB ``.mat`` (column vectors) to match the
    reference output files.
    """
    thetap = np.asarray(thetap, dtype=float)
    A = np.zeros(Nfr)
    theta0 = np.zeros(Nfr)
    sigma = np.zeros(Nfr)
    v = np.zeros(Nfr)
    v[0] = vdets[0]
    vdets_avg = float(np.mean(vdets))
    dt = t[1] - t[0]

    low_j = 1
    up_j = Nb

    for i in range(Nfr):
        # tracked window (possibly wrapping)
        if low_j < up_j:
            XT_i = XT[low_j - 1:up_j, i]
        else:
            XT_i = np.concatenate([XT[0:up_j, i], XT[low_j - 1:Nb, i]])

        A[i] = XT_i.max()
        theta_i = int(np.argmin(np.abs(XT[:, i] - A[i])))
        theta0[i] = thetap[theta_i]

        Ai = A[i]
        xi = theta0[i]

        def obj(p, Ai=Ai, xi=xi, i=i, low_j=low_j, up_j=up_j):
            g = periodic_gaussian(thetap, xi, Ai, p)
            if low_j < up_j:
                diff = g[low_j - 1:up_j] - XT[low_j - 1:up_j, i]
            else:
                diff = (np.concatenate([g[0:up_j], g[low_j - 1:Nb]])
                        - np.concatenate([XT[0:up_j, i], XT[low_j - 1:Nb, i]]))
            return np.abs(diff).sum()

        res = minimize_scalar(obj, bounds=(0.1, 0.7), method="bounded",
                              options={"xatol": 1e-9})
        sigma[i] = res.x

        if i > 0:
            dtheta = theta0[i] - theta0[i - 1]
            if (dtheta / dt) / vdets_avg > 0:
                v[i] = dtheta / dt
            elif vdets_avg < 0:
                v[i] = (dtheta - _TWO_PI) / dt
            else:
                v[i] = (dtheta + _TWO_PI) / dt

        # predict next window edges
        if vdets_avg < 0:
            theta0_guess_up = (theta0[i] + 0.5 * vdets_avg * dt) % _TWO_PI
            theta0_guess_low = (theta0[i] + 1.5 * vdets_avg * dt) % _TWO_PI
        else:
            theta0_guess_up = (theta0[i] + 1.5 * vdets_avg * dt) % _TWO_PI
            theta0_guess_low = (theta0[i] + 0.5 * vdets_avg * dt) % _TWO_PI
        up_j = int(np.argmin(np.abs(thetap - theta0_guess_up))) + 1
        low_j = int(np.argmin(np.abs(thetap - theta0_guess_low))) + 1

        if progress_every and (i + 1) % progress_every == 0:
            print(f"  opt frame {i + 1}/{Nfr}  sigma={sigma[i]:.5f}", flush=True)

    if fname is not None:
        from scipy.io import savemat
        savemat(fname, {
            "theta0": theta0.reshape(-1, 1),
            "sigma": sigma.reshape(-1, 1),
            "A": A.reshape(-1, 1),
            "v": v.reshape(-1, 1),
        })
    return theta0, sigma, A, v


def _top_peak_indices(profile, n, min_sep=8):
    """0-based ring indices of the ``n`` dominant local maxima, each at least
    ``min_sep`` samples apart, in descending order of height.  Seeds the
    multi-Gaussian fit."""
    prof = np.asarray(profile, float)
    Nb = prof.size
    is_peak = np.array([prof[s] >= prof[(s - 1) % Nb] and prof[s] >= prof[(s + 1) % Nb]
                        for s in range(Nb)])
    order = np.argsort(prof)[::-1]
    chosen = []
    for s in order:
        s = int(s)
        if not is_peak[s]:
            continue
        if all(min(abs(s - o), Nb - abs(s - o)) >= min_sep for o in chosen):
            chosen.append(s)
        if len(chosen) >= n:
            break
    return chosen


def _fit_residual(data, thetap, theta0, sigma, A):
    """L1 residual (sum of ``|data - synth|``) of a (n_gauss,) Gaussian fit.

    Used for automatic 1-vs-2 wave model selection: a second wave is kept only if
    it reduces this residual by more than the selection threshold."""
    Nb = data.shape[0]
    synth = _gauss_synth(Nb, thetap, theta0, sigma, A)
    return float(np.abs(data - synth).sum())


def _gauss_wave_opt_2nd(data, primary, Nfr, Nb, thetap, t, vdets, half_win=None):
    """Fit the second wave, discovered as the coherent residual feature.

    The second wave's offset (from the primary) is the one with the largest
    time-averaged residual amplitude, outside the primary's own region (±3 sigma_p).
    A genuine second wave is coherent -- present every frame at a fixed offset -- so
    it dominates the average, whereas scattered noise (which is where a per-frame
    max would latch on) averages out.  The second wave then rides the primary's
    velocity, as a coherent member of the same wave system.  When the two waves of
    a system sit ~pi apart, this discovery lands there naturally; it is a
    consequence of the data, not an assumed separation.
    Returns ``(theta0, sigma, A, v)`` each ``(Nfr,)`` with the shared velocity.
    """
    th_p, sig_p, A_p, v_p = primary
    thetap = np.asarray(thetap, dtype=float)
    dtheta = _TWO_PI / Nb
    if half_win is None:
        dt = t[1] - t[0]
        half_win = max(0.2, 0.75 * abs(float(np.mean(vdets))) * dt)  # ~1 frame motion
    resid = data - _gauss_synth(Nb, thetap, th_p, sig_p, A_p)

    def region_mask(center, half):
        d = np.mod(thetap - center + np.pi, _TWO_PI) - np.pi
        return np.abs(d) <= half

    # align each frame so the primary sits at ring index 0; the column average then
    # gives the coherent residual feature at each offset from the primary
    shifted = np.stack(
        [np.roll(resid[:, i], -int(round(th_p[i] / dtheta))) for i in range(Nfr)],
        axis=1)
    avg_amps = shifted.mean(axis=1)
    ex = int(round(3.0 * float(np.median(sig_p)) / dtheta))   # primary's own region
    avg_amps[:ex] = -np.inf
    avg_amps[-ex:] = -np.inf
    offset = float(thetap[int(np.argmax(avg_amps))])

    th_2 = np.zeros(Nfr)
    A_2 = np.zeros(Nfr)
    sig_2 = np.zeros(Nfr)
    for i in range(Nfr):
        col = resid[:, i]
        sec_loc = th_p[i] + offset           # second wave rides primary + offset
        m = region_mask(sec_loc, half_win)   # narrow window for A / sigma
        A_2[i] = float(col[m].max())
        th_2[i] = sec_loc

        def obj(p, A_i=A_2[i], c=sec_loc, m=m, col=col):
            gg = periodic_gaussian(thetap, c, A_i, p)
            return float(np.abs(gg[m] - col[m]).sum())

        sig_2[i] = float(minimize_scalar(obj, bounds=(0.1, 0.7), method="bounded",
                                         options={"xatol": 1e-9}).x)
    return th_2, sig_2, A_2, v_p


def _gauss_wave_opt_n(XT, Nfr, Nb, thetap, t, vdets, fname, n_gauss=2, progress_every=0):
    """Sequential ``n_gauss`` fit of one wave system across all frames.

    The primary is the v1 1-Gaussian fit of the data; the second Gaussian is fit
    in the ~pi band relative to the primary (see ``_gauss_wave_opt_2nd``) so the
    real second wave is captured, not a shoulder bump.  All Gaussians share the
    system velocity ``v`` (the primary's).  Returns ``(theta0, sigma, A, v)`` where
    ``theta0``/``sigma``/``A`` are ``(n_gauss, Nfr)`` and ``v`` is ``(Nfr,)``.
    When ``fname`` is given the result is written as a MATLAB ``.mat``.
    """
    thetap = np.asarray(thetap, dtype=float)
    prim = _gauss_wave_opt_1(XT, Nfr, Nb, thetap, t, vdets, None, 0)
    parts = [prim[:3]]
    v = prim[3]
    if n_gauss >= 2:
        parts.append(_gauss_wave_opt_2nd(XT, prim, Nfr, Nb, thetap, t, vdets)[:3])
    theta0 = np.stack([p[0] for p in parts])
    sigma = np.stack([p[1] for p in parts])
    A = np.stack([p[2] for p in parts])
    if fname is not None:
        from scipy.io import savemat
        savemat(fname, {"theta0": theta0, "sigma": sigma, "A": A,
                        "v": v.reshape(-1, 1)})
    return theta0, sigma, A, v


def gauss_wave_opt(XT, Nfr, Nb, thetap, t, vdets, fname=None, n_gauss=1, progress_every=0):
    """Optimise one wave system across all ``Nfr`` frames.

    ``n_gauss=1`` reproduces the v1 single-Gaussian optimiser exactly (returns
    ``(theta0, sigma, A, v)`` each ``(Nfr,)``); ``n_gauss=2`` fits two Gaussians
    that share the system velocity ``v`` (returns ``theta0``/``sigma``/``A`` as
    ``(2, Nfr)`` and ``v`` as ``(Nfr,)``).  When ``fname`` is given the result is
    also written as a MATLAB ``.mat``.
    """
    if n_gauss == 1:
        return _gauss_wave_opt_1(XT, Nfr, Nb, thetap, t, vdets, fname, progress_every)
    return _gauss_wave_opt_n(XT, Nfr, Nb, thetap, t, vdets, fname, n_gauss, progress_every)


def auto_select_waves(data, Nfr, Nb, thetap, t, vdets):
    """Fit a wave system as 1 and as 2 waves and auto-select by local signal-to-noise.

    The second wave is discovered freely (the dominant residual crest outside the
    primary's own region).  Two waves are kept only if, in the second wave's own
    region (±3 sigma_2), the second wave's contribution to the fit -- the 1-wave
    residual minus the 2-wave residual -- exceeds the local noise floor (the 2-wave
    residual).  That is a relative signal-to-noise test with no dataset-specific
    constant: a genuine second wave beats the noise in its own region, whereas a
    single-wave system's residual there is just noise and cannot.

    Returns ``(res, use2, R1, R2)`` where ``res`` is the chosen
    ``(theta0, sigma, A, v)`` (``n_gauss=1`` or ``2``), ``use2`` is whether two waves
    were selected, and ``R1``/``R2`` are the 1- and 2-wave L1 residuals."""
    thetap = np.asarray(thetap, dtype=float)
    res2 = _gauss_wave_opt_n(data, Nfr, Nb, thetap, t, vdets, None, n_gauss=2)
    res1 = (res2[0][0], res2[1][0], res2[2][0], res2[3])
    R1 = _fit_residual(data, thetap, res1[0], res1[1], res1[2])
    R2 = _fit_residual(data, thetap, res2[0], res2[1], res2[2])
    # local signal-to-noise in the second wave's region (±3 sigma_2)
    w = 3.0 * float(np.median(res2[1][1]))
    def mask(c):
        d = np.mod(thetap - c + np.pi, _TWO_PI) - np.pi
        return np.abs(d) <= w
    r1 = data - _gauss_synth(Nb, thetap, res1[0], res1[1], res1[2])
    r2 = data - _gauss_synth(Nb, thetap, res2[0], res2[1], res2[2])
    reg1 = reg2 = 0.0
    for i in range(Nfr):
        m = mask(res2[0][1][i])          # the second wave's position at frame i
        reg1 += float(np.abs(r1[:, i][m]).sum())
        reg2 += float(np.abs(r2[:, i][m]).sum())
    use2 = (reg1 - reg2) > reg2          # second wave beats the local noise floor
    return (res2 if use2 else res1), bool(use2), R1, R2
