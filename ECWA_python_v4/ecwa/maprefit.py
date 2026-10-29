#!/usr/bin/env python
# Author: Timothy J. Welch
"""PECWA_julia MAP re-fit port (pure numpy/scipy -- no reverse-mode AD).

Re-fits the *reduced* series that the v4 synthesis consumes (``A``, ``sigma``,
``v`` every-20th-frame + double-smoothed; ``theta0`` scalar per Gaussian) with a
random-walk smoothness prior and a Laplace (1-norm) likelihood, to lower the
checker epsilon WITHOUT changing the wave count (same ``theta0`` starts, same
number of Gaussians, same shared-velocity structure).

Faithful to ``PECWA_julia/fit_map.jl``:
  * params = dimensionless offsets ``delta`` from the warm start
    (``actual = init + scale*delta``; sigma on the log scale), so delta=0
    reproduces the warm start exactly;
  * scales: A=0.05*mean|A|, log-sigma=0.1, v=10 rad/s, theta0=0.1 rad;
  * tau: 2*std(diff(init series)) (random-walk roughness of the warm start);
  * b: mean|XT - (S0 + BG)| (warm-start residual scale);
  * smoothness on the ACTUAL series: sum(diff(x)^2)/(2 tau^2);
  * likelihood: sum|XT - (S + BG)|/b, restricted to the (thinned) training frames.

Kernels (``PECWA_julia/checker_variants.jl``):
  * ``gauss``    : A*exp(-dx^2 / 2 sigma^2)                 (base == v4 add_wave)
  * ``student_t``: A*(1 + dx^2 / (nu sigma^2))^(-(nu+1)/2)  (nu->inf == gauss)
  * ``split``    : A*exp(-dx^2 / 2 sigma_side^2),
                   sigma_side = sigmaP (dx>=0) | sigmaN (dx<0)  (asymmetric)

The synthesis is *vectorized* (a handful of ``(Nb, n_frame)`` array ops) and is
validated bit-for-bit against v4 ``add_wave`` in ``tests/test_maprefit.py``.  The
fit uses an **analytic gradient** (the numpy equivalent of the Julia's reverse-
mode AD) and runs on a thinned frame grid (``thin`` = first ``Nfr//thin`` frames,
dt scaled by ``thin`` -- the Julia ``thin_frames`` trick); the reported epsilon is
always on the full frame set.
"""
import os
import numpy as np
from scipy.optimize import minimize

__all__ = ["interp_series", "synthesize_waves", "synthesize_gauss",
           "make_waves", "synthesize_system", "residual_fraction",
           "map_refit", "check_gradient"]

_TAU = 2.0 * np.pi
_PI = np.pi


# --------------------------------------------------------------------------- #
# Interpolation + vectorized synthesis (reproduces v4 add_wave / Julia checker)
# --------------------------------------------------------------------------- #
def interp_series(series, Nfr, Nt, frame_idx):
    """Map a reduced series ``(Nt,)`` to 0-based frames ``frame_idx``.

    Julia ``interpolate(Nfr, Nt, y, k)``: reduced position
    ``a = (k/(Nfr-1))*(Nt-1)``, linear between ``y[j]`` and ``y[j+1]``.  For the
    v4 grid (Nfr=10001, Nt=501) this is exactly ``interp1(t_dummy, y, k+1)`` with
    ``t_dummy = 1:20:Nfr`` (reduced sample m at frame 20m).
    """
    series = np.asarray(series, float).ravel()
    k = np.asarray(frame_idx, float)
    a = (k / (Nfr - 1)) * (Nt - 1)
    j = np.floor(a).astype(int)
    frac = a - j
    j0 = np.clip(j, 0, Nt - 1)
    j1 = np.clip(j + 1, 0, Nt - 1)
    return series[j0] * (1.0 - frac) + series[j1] * frac


def synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel="gauss", nu=None,
                     sigN=None, sigP=None, frame_idx=None):
    """Vectorized synthesis of the ``waves`` (list of per-system dicts) -> (Nb, nF).

    Each dict: ``th0`` (n_g,), ``A`` (n_g, Nt), ``sig`` (n_g, Nt), ``v`` (Nt,)
    (velocity *shared* across the system's Gaussians).  ``frame_idx`` 0-based
    frames to synthesize (default all ``0..Nfr-1``); ``dt`` is the per-frame
    step (already scaled for a thinned grid).  ``nu``/``sigN``/``sigP`` are
    per-system lists for the student-t / split kernels.
    """
    thetap = np.asarray(thetap, float)
    if frame_idx is None:
        frame_idx = np.arange(Nfr)
    frame_idx = np.asarray(frame_idx, int)
    nF = frame_idx.size
    Nb = thetap.size
    S = np.zeros((Nb, nF))
    vstep_frames = np.arange(0, Nfr - 1)          # v sampled at frame (k-1)
    for sys_i, w in enumerate(waves):
        th0 = np.atleast_1d(np.asarray(w["th0"], float))
        A = np.asarray(w["A"], float)
        sig = np.asarray(w["sig"], float)
        v = np.asarray(w["v"], float).ravel()                   # (Nt,)
        n_g = th0.size
        if A.ndim == 2:                                          # (n_g, Nt) -> K=1
            A = A[:, None, :]; sig = sig[:, None, :]
        Kc = A.shape[1]
        base_full = np.zeros(Nfr)
        base_full[1:] = np.cumsum(interp_series(v, Nfr, Nt, vstep_frames) * dt)
        base = base_full[frame_idx]                              # (nF,)
        for g in range(n_g):
            theta = th0[g] + base
            dx = np.mod(thetap[:, None] - theta[None, :] + _PI, _TAU) - _PI
            for c in range(Kc):
                A_f = interp_series(A[g, c], Nfr, Nt, frame_idx)
                sig_f = interp_series(sig[g, c], Nfr, Nt, frame_idx)
                if kernel == "gauss":
                    S += A_f[None, :] * _kernel(dx, sig_f[None, :], "gauss")
                elif kernel == "student_t":
                    nvg = float(np.atleast_1d(np.asarray(nu[sys_i]))[g])
                    S += A_f[None, :] * _kernel(dx, sig_f[None, :], "student_t", nu=nvg)
                elif kernel == "split":
                    sN = np.atleast_2d(np.asarray(sigN[sys_i], float))[g]
                    sP = np.atleast_2d(np.asarray(sigP[sys_i], float))[g]
                    sN_f = interp_series(sN, Nfr, Nt, frame_idx)
                    sP_f = interp_series(sP, Nfr, Nt, frame_idx)
                    S += A_f[None, :] * _kernel_split(dx, sN_f[None, :], sP_f[None, :])
                else:
                    raise ValueError(f"unknown kernel {kernel!r}")
    return S


def _kernel(dx, sig, kind, nu=None):
    """Unit-height profile (no A).  ``sig`` is (nF,) broadcast over rows of dx."""
    if kind == "gauss":
        return np.exp(-(dx ** 2) / (2.0 * sig ** 2))
    if kind == "student_t":
        return (1.0 + dx ** 2 / (nu * sig ** 2)) ** (-(nu + 1.0) / 2.0)
    raise ValueError(kind)


def _kernel_split(dx, sigN, sigP):
    """Asymmetric Gaussian: sigmaP for dx>=0, sigmaN for dx<0.  (nF,) sigs."""
    s = np.where(dx >= 0.0, sigP, sigN)
    return np.exp(-(dx ** 2) / (2.0 * s ** 2))


def synthesize_gauss(thetap, th0, A, sig, v, dt, Nfr, win=20, kernel="gauss",
                     nu=None, sigN=None, sigP=None):
    """v4-``add_wave``-compatible single-system synthesis on the full grid."""
    v = np.asarray(v, float).ravel()
    Nt = v.size
    wave = {"th0": np.atleast_1d(np.asarray(th0, float)),
            "A": np.atleast_2d(np.asarray(A, float)),
            "sig": np.atleast_2d(np.asarray(sig, float)), "v": v}
    return synthesize_waves(thetap, [wave], dt, Nfr, Nt, kernel=kernel,
                            nu=[np.atleast_1d(nu)] if nu is not None else None,
                            sigN=[np.atleast_2d(sigN)] if sigN is not None else None,
                            sigP=[np.atleast_2d(sigP)] if sigP is not None else None,
                            frame_idx=np.arange(Nfr))


def make_waves(results_dir):
    """Load the three v4 wave systems' reduced series as a list of dicts.

    Each dict: ``{'th0': (n_g,), 'A': (n_g, Nt), 'sig': (n_g, Nt), 'v': (Nt,)}``
    where ``n_g`` is 1 or 2 (the v4 auto-selected wave count for that system).
    """
    waves = []
    for i in range(1, 4):
        d = os.path.join(results_dir, f"wave_sys_{i}")
        th0 = np.atleast_1d(np.loadtxt(os.path.join(d, "theta0.csv"), delimiter=","))
        n_g = th0.size
        if n_g == 1:
            A = np.atleast_2d(np.loadtxt(os.path.join(d, "A.csv"), delimiter=","))
            sig = np.atleast_2d(np.loadtxt(os.path.join(d, "sigma.csv"), delimiter=","))
        else:
            A = np.stack([np.loadtxt(os.path.join(d, f"A_{g}.csv"), delimiter=",")
                          for g in range(1, n_g + 1)])
            sig = np.stack([np.loadtxt(os.path.join(d, f"sigma_{g}.csv"), delimiter=",")
                            for g in range(1, n_g + 1)])
        v = np.loadtxt(os.path.join(d, "v.csv"), delimiter=",")
        waves.append({"th0": th0, "A": A, "sig": sig, "v": v})
    return waves


def load_refit_waves(res_dir):
    """Load a saved re-fit series (the driver's ``save_refit`` ``waves.npz``
    layout) back into the ``waves`` structure.  Handles any K (number of
    components per position) and any position count.  Pairs with
    ``synthesize_waves`` to reproduce the re-fit synthesis / epsilon.
    Inverse of the driver's ``save_refit``."""
    waves = []
    i = 1
    while True:
        f = os.path.join(res_dir, f"wave_sys_{i}", "waves.npz")
        if not os.path.exists(f):
            break
        z = np.load(f)
        waves.append({"th0": np.asarray(z["th0"]), "A": np.asarray(z["A"]),
                      "sig": np.asarray(z["sig"]), "v": np.asarray(z["v"])})
        i += 1
    return waves


def synthesize_system(waves, thetap, dt, Nfr, Nt, kernel="gauss", nu=None,
                      sigN=None, sigP=None, frame_idx=None):
    """Synthesize the three wave systems together -> (Nb, nF)."""
    return synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel=kernel, nu=nu,
                            sigN=sigN, sigP=sigP, frame_idx=frame_idx)


def residual_fraction(XT, S_tot):
    """checker epsilon = ||XT - S_tot||_1 / ||XT||_1."""
    return float(np.abs(XT - S_tot).sum() / np.abs(XT).sum())


# --------------------------------------------------------------------------- #
# Kernel derivatives (for the analytic gradient)
# --------------------------------------------------------------------------- #
def _dkern_derivs(dx, K, kernel, sig_f, nvg=None, sigN_f=None, sigP_f=None):
    """Kernel-aware derivatives of the unit profile (no A) w.r.t. its arguments.

    Returns ``(dKdx, dKds, dKdsN, dKdsP)`` -- only the entries relevant to the
    kernel are non-None.  ``sig_f``/``sigN_f``/``sigP_f`` are ``(nF,)`` (broadcast
    over the sensor axis of ``dx``/``K``).  These are the numpy equivalents of the
    reverse-mode derivatives the Julia's Mooncake AD provides.
    """
    if kernel == "gauss":
        dKdx = K * (-dx / sig_f ** 2)
        dKds = K * (dx ** 2 / sig_f ** 3)
        return dKdx, dKds, None, None
    if kernel == "student_t":
        u = dx ** 2 / (nvg * sig_f ** 2)
        # d/du (1+u)^(-(nu+1)/2) = -(nu+1)/2 * (1+u)^(-(nu+1)/2 - 1)
        dKdx = K * (-(nvg + 1.0) / (2.0 * (1.0 + u))) * (2.0 * dx / (nvg * sig_f ** 2))
        dKds = K * (-(nvg + 1.0) / (2.0 * (1.0 + u))) * (-2.0 * u / sig_f)
        return dKdx, dKds, None, None
    if kernel == "split":
        sig_side = np.where(dx >= 0.0, sigP_f, sigN_f)
        dKdx = K * (-dx / sig_side ** 2)
        dKds_side = K * (dx ** 2 / sig_side ** 3)
        dKdsN = dKds_side * (dx < 0.0)
        dKdsP = dKds_side * (dx >= 0.0)
        return dKdx, None, dKdsN, dKdsP
    raise ValueError(kernel)


def _rw_grad(actual, tau):
    """grad of sum(diff(actual)^2)/(2 tau^2) w.r.t. actual (discrete Laplacian)."""
    g = np.zeros_like(actual)
    if actual.size > 1:
        d = np.diff(actual)
        g[0] = -d[0] / (tau * tau)
        g[-1] = d[-1] / (tau * tau)
        g[1:-1] = (d[:-1] - d[1:]) / (tau * tau)
    return g


# --------------------------------------------------------------------------- #
# MAP re-fit (analytic gradient)
# --------------------------------------------------------------------------- #
class _MapRefit:
    """Joint MAP re-fit over all systems' reduced series (Gaussian / Student-t /
    split-sigma).  Holds x-independent structure; ``f_and_g(xd)`` returns the
    objective and its analytic gradient; ``build(xd)`` reconstructs the series."""

    # K-Gaussian component warm-start multipliers (A x, sigma x), from
    # PECWA_julia/fit_variants.jl COMPONENT_INIT: primary + wide faint halo(s).
    COMPONENT_INIT = [(1.0, 1.0), (0.2, 2.5), (0.08, 5.0)]

    def __init__(self, XT, BG, waves, dt, Nfr, thetap, kernel="gauss", thin=20,
                 b=None, nu0=None, K=1):
        self.K = max(1, int(K))
        self.Nb = XT.shape[0]
        self.Nt = waves[0]["v"].size
        self.Nfr_t = max(3, (Nfr - 1) // thin + 1)   # count of every-`thin`-th frames
        self.dt_t = dt * thin
        # every-`thin`-th frame spread across the record (Julia thin_frames:
        # XT[:, 1:thin:end]); thinned frame k == full frame thin*k, which is where
        # the reduced sample k maps to under the (k/(Nfr_t-1))*(Nt-1) interp.
        self.Xt_t = XT[:, ::thin][:self.Nfr_t]
        self.BG_t = BG[:, ::thin][:self.Nfr_t]
        self.thetap = np.asarray(thetap, float)
        self.kernel = kernel
        self.Nfr = Nfr
        self.dt = dt
        self.b = b
        self.waves0 = waves

        # reduced-position interp maps: A/sig over frames 0..Nfr_t-1, v over 0..Nfr_t-2
        fA = np.arange(self.Nfr_t)
        aA = (fA / (self.Nfr_t - 1)) * (self.Nt - 1)
        self.jA0 = np.clip(aA.astype(int), 0, self.Nt - 1)
        self.frA = aA - self.jA0
        self.jA1 = np.minimum(self.jA0 + 1, self.Nt - 1)
        fV = np.arange(self.Nfr_t - 1)
        aV = (fV / (self.Nfr_t - 1)) * (self.Nt - 1)
        self.jV0 = np.clip(aV.astype(int), 0, self.Nt - 1)
        self.frV = aV - self.jV0
        self.jV1 = np.minimum(self.jV0 + 1, self.Nt - 1)

        self.nsys = len(waves)
        self.n_g = [int(w["th0"].size) for w in waves]
        self.K = self.K
        self.scaleA = np.zeros((self.nsys, max(self.n_g), self.K))
        self.tauA = np.zeros((self.nsys, max(self.n_g), self.K))
        self.tauS = np.zeros((self.nsys, max(self.n_g), self.K))
        self.tauV = np.zeros(self.nsys)
        self.scaleS, self.scaleV, self.scaleT = 0.1, 10.0, 0.1
        # K-Gaussian: component c of position g is a scaled copy of the warm-start
        # Gaussian (COMPONENT_INIT[c] = (A x, sigma x)); K==1 is the plain wave.
        self.A_init = []
        self.sig_init = []
        for i, w in enumerate(waves):
            self.tauV[i] = 2.0 * max(float(np.std(np.diff(w["v"]))), 1e-12)
            Ai = np.zeros((self.n_g[i], self.K, self.Nt))
            Si = np.zeros((self.n_g[i], self.K, self.Nt))
            for g in range(self.n_g[i]):
                for c in range(self.K):
                    am = self.COMPONENT_INIT[c][0]
                    sm = self.COMPONENT_INIT[c][1]
                    Ag = am * w["A"][g].ravel(); sg = sm * w["sig"][g].ravel()
                    Ai[g, c] = Ag; Si[g, c] = sg
                    self.scaleA[i, g, c] = 0.05 * max(1e-12, abs(float(np.mean(Ag))))
                    self.tauA[i, g, c] = 2.0 * max(float(np.std(np.diff(Ag))), 1e-12)
                    self.tauS[i, g, c] = 2.0 * max(float(np.std(np.diff(sg))), 1e-12)
            self.A_init.append(Ai)
            self.sig_init.append(Si)
        # student-t nu warm start (per gaussian scalar)
        self.nu_init = [np.full(self.n_g[i], float(nu0) if nu0 else 8.0) for i in range(self.nsys)]

        # parameter offsets (A and S carry K components per position)
        off = 0
        self.off = {}
        for i in range(self.nsys):
            ng = self.n_g[i]
            self.off[(i, "A")] = off; off += ng * self.K * self.Nt
            self.off[(i, "S")] = off; off += ng * self.K * self.Nt
            self.off[(i, "V")] = off; off += self.Nt
            self.off[(i, "T")] = off; off += ng
        self.n_delta = off
        if kernel == "student_t":
            for i in range(self.nsys):
                self.off[(i, "NU")] = off; off += self.n_g[i]
        if kernel == "split":
            for i in range(self.nsys):
                self.off[(i, "SN")] = off; off += self.n_g[i] * self.Nt
                self.off[(i, "SP")] = off; off += self.n_g[i] * self.Nt
        self.n = off

    # -- reconstruct actual reduced series from a delta vector --
    def build(self, xd):
        waves = []
        for i in range(self.nsys):
            ng = self.n_g[i]; K = self.K
            A = self.A_init[i] + self.scaleA[i, :ng, :, None] * xd[self.off[(i, "A")]:self.off[(i, "A")] + ng * K * self.Nt].reshape(ng, K, self.Nt)
            sig = np.exp(np.log(np.abs(self.sig_init[i]) + 1e-12)
                         + self.scaleS * xd[self.off[(i, "S")]:self.off[(i, "S")] + ng * K * self.Nt].reshape(ng, K, self.Nt))
            v = self.waves0[i]["v"] + self.scaleV * xd[self.off[(i, "V")]:self.off[(i, "V")] + self.Nt]
            th0 = self.waves0[i]["th0"] + self.scaleT * xd[self.off[(i, "T")]:self.off[(i, "T")] + ng]
            waves.append({"th0": th0, "A": A, "sig": sig, "v": v})
        nu = None
        if self.kernel == "student_t":
            # nu = exp(log(nu_init) + 0.5*delta) spans (0, inf); clamp to avoid the
            # singular nu->0 limit (dx^2/(nu sigma^2) -> inf) which is a near-Dirac.
            nu = [np.maximum(self.nu_init[i] * np.exp(0.5 * xd[self.off[(i, "NU")]:self.off[(i, "NU")] + self.n_g[i]]), 0.02)
                  for i in range(self.nsys)]
        sigN = sigP = None
        if self.kernel == "split":
            sigN = [np.exp(np.log(np.abs(self.waves0[i]["sig"]) + 1e-12)
                           + self.scaleS * xd[self.off[(i, "SN")]:self.off[(i, "SN")] + self.n_g[i] * self.Nt].reshape(self.n_g[i], self.Nt))
                    for i in range(self.nsys)]
            sigP = [np.exp(np.log(np.abs(self.waves0[i]["sig"]) + 1e-12)
                           + self.scaleS * xd[self.off[(i, "SP")]:self.off[(i, "SP")] + self.n_g[i] * self.Nt].reshape(self.n_g[i], self.Nt))
                    for i in range(self.nsys)]
        return waves, nu, sigN, sigP

    def _comp(self, i, g, c):
        return g * self.K + c          # flat component index for (position g, component c)

    def f_and_g(self, xd):
        Nfr_t, Nt, Nb = self.Nfr_t, self.Nt, self.Nb
        thetap = self.thetap
        waves, nu, sigN, sigP = self.build(xd)
        K = self.K

        S = np.zeros((Nb, Nfr_t))
        cache = []                     # per-system: (A_f, sig_f, theta, deriv_list)
        for i in range(self.nsys):
            w = waves[i]; ng = self.n_g[i]
            v_interp = self._interp(w["v"], self.jV0, self.jV1, 1.0 - self.frV, self.frV)
            base = np.zeros(Nfr_t)
            base[1:] = np.cumsum(v_interp * self.dt_t)
            A_f = np.stack([self._interp(w["A"][g, c], self.jA0, self.jA1, 1.0 - self.frA, self.frA)
                            for g in range(ng) for c in range(K)]).reshape(ng, K, Nfr_t)
            sig_f = np.stack([self._interp(w["sig"][g, c], self.jA0, self.jA1, 1.0 - self.frA, self.frA)
                              for g in range(ng) for c in range(K)]).reshape(ng, K, Nfr_t)
            theta = w["th0"][:, None] + base[None, :]             # (ng, Nfr_t) shared over c
            if self.kernel == "split":                            # per-position split widths (per-frame)
                sN_pos = np.stack([self._interp(sigN[i][g], self.jA0, self.jA1, 1.0 - self.frA, self.frA) for g in range(ng)])
                sP_pos = np.stack([self._interp(sigP[i][g], self.jA0, self.jA1, 1.0 - self.frA, self.frA) for g in range(ng)])
            else:
                sN_pos = sP_pos = None
            deriv_list = []
            for g in range(ng):
                dx = np.mod(thetap[:, None] - theta[g][None, :] + _PI, _TAU) - _PI
                for c in range(K):
                    if self.kernel == "split":
                        pr = self._derivs(dx, None, None, sN_pos[g], sP_pos[g])
                    elif self.kernel == "student_t":
                        pr = self._derivs(dx, sig_f[g, c], float(nu[i][g]), None, None)
                    else:
                        pr = self._derivs(dx, sig_f[g, c], None, None, None)
                    S += A_f[g, c][None, :] * pr[0]
                    deriv_list.append(pr)
            cache.append((A_f, sig_f, theta, deriv_list))
        r = self.Xt_t - (S + self.BG_t)
        W = -np.sign(r) / self.b
        f_data = float(np.abs(r).sum() / self.b)
        wA0, wA1 = 1.0 - self.frA, self.frA

        gA = np.zeros(self.n); gS = np.zeros(self.n); gV = np.zeros(self.n)
        gT = np.zeros(self.n); gSN = np.zeros(self.n); gSP = np.zeros(self.n)
        for i in range(self.nsys):
            w = waves[i]; ng = self.n_g[i]
            A_f, sig_f, theta, deriv_list = cache[i]
            H_sys = np.zeros(Nfr_t)            # shared-v sensitivity (summed over g,c)
            di = 0
            for g in range(ng):
                Hg_sum = np.zeros(Nfr_t)       # th0 sensitivity, accumulated over c
                for c in range(K):
                    Kp, dKdx, dKds, dKdsN, dKdsP = deriv_list[di]; di += 1
                    D = (W * Kp).sum(axis=0)   # d f / d A_f[k] (kernel-independent)
                    lo = self.off[(i, "A")] + self._comp(i, g, c) * Nt
                    gA[lo:lo + Nt] += self.scaleA[i, g, c] * self._scatter_arr(D, self.jA0, self.jA1, wA0, wA1)
                    if dKds is not None:       # base-sig data term (gauss / student-t / K)
                        Sig = A_f[g, c] * (W * dKds).sum(axis=0)
                        loS = self.off[(i, "S")] + self._comp(i, g, c) * Nt
                        gS[loS:loS + Nt] += self.scaleS * w["sig"][g, c] * self._scatter_arr(Sig, self.jA0, self.jA1, wA0, wA1)
                    if self.kernel == "split":  # split sigN / sigP data term (per position)
                        loN = self.off[(i, "SN")] + g * Nt
                        loP = self.off[(i, "SP")] + g * Nt
                        gSN[loN:loN + Nt] += self.scaleS * sigN[i][g] * self._scatter_arr(A_f[g, c] * (W * dKdsN).sum(axis=0), self.jA0, self.jA1, wA0, wA1)
                        gSP[loP:loP + Nt] += self.scaleS * sigP[i][g] * self._scatter_arr(A_f[g, c] * (W * dKdsP).sum(axis=0), self.jA0, self.jA1, wA0, wA1)
                    Hg_sum += -A_f[g, c] * (W * dKdx).sum(axis=0)   # dK/dtheta = -dK/dx
                gT[self.off[(i, "T")] + g] += Hg_sum.sum() * self.scaleT
                H_sys += Hg_sum
            suffix = np.cumsum(H_sys[::-1])[::-1]             # suffix[i] = sum_{k>=i} H[k]
            R = suffix[1:]                                    # R[j] = sum_{k>j} H[k], len Nfr_t-1
            sc_V = self._scatter_arr(R * self.dt_t, self.jV0, self.jV1, 1.0 - self.frV, self.frV)
            gV[self.off[(i, "V")]:self.off[(i, "V")] + Nt] += self.scaleV * sc_V

        # smoothness penalty + gradient (on ACTUAL series)
        f_pen = 0.0
        for i in range(self.nsys):
            ng = self.n_g[i]; w = waves[i]
            for g in range(ng):
                for c in range(K):
                    offA = self.off[(i, "A")] + self._comp(i, g, c) * Nt
                    f_pen += float(np.sum(np.diff(w["A"][g, c]) ** 2) / (2 * self.tauA[i, g, c] ** 2))
                    gA[offA:offA + Nt] += self.scaleA[i, g, c] * _rw_grad(w["A"][g, c], self.tauA[i, g, c])
                    if self.kernel != "split":
                        offS = self.off[(i, "S")] + self._comp(i, g, c) * Nt
                        f_pen += float(np.sum(np.diff(w["sig"][g, c]) ** 2) / (2 * self.tauS[i, g, c] ** 2))
                        gS[offS:offS + Nt] += self.scaleS * w["sig"][g, c] * _rw_grad(w["sig"][g, c], self.tauS[i, g, c])
            f_pen += float(np.sum(np.diff(w["v"]) ** 2) / (2 * self.tauV[i] ** 2))
            gV[self.off[(i, "V")]:self.off[(i, "V")] + Nt] += self.scaleV * _rw_grad(w["v"], self.tauV[i])
            if self.kernel == "split":
                for g in range(ng):
                    for (sn, off) in ((sigN[i][g], self.off[(i, "SN")]), (sigP[i][g], self.off[(i, "SP")])):
                        f_pen += float(np.sum(np.diff(sn) ** 2) / (2 * self.tauS[i, g, 0] ** 2))
                        grad_arr = gSN if off == self.off[(i, "SN")] else gSP
                        grad_arr[off + g * Nt:off + (g + 1) * Nt] += self.scaleS * sn * _rw_grad(sn, self.tauS[i, g, 0])
        grad = np.zeros(self.n)
        for i in range(self.nsys):
            ng = self.n_g[i]
            grad[self.off[(i, "A")]:self.off[(i, "A")] + ng * K * Nt] = gA[self.off[(i, "A")]:self.off[(i, "A")] + ng * K * Nt]
            grad[self.off[(i, "S")]:self.off[(i, "S")] + ng * K * Nt] = gS[self.off[(i, "S")]:self.off[(i, "S")] + ng * K * Nt]
            grad[self.off[(i, "V")]:self.off[(i, "V")] + Nt] = gV[self.off[(i, "V")]:self.off[(i, "V")] + Nt]
            grad[self.off[(i, "T")]:self.off[(i, "T")] + ng] = gT[self.off[(i, "T")]:self.off[(i, "T")] + ng]
        if self.kernel == "student_t":
            for i in range(self.nsys):
                grad[self.off[(i, "NU")]:self.off[(i, "NU")] + self.n_g[i]] = self._grad_nu(i, waves, nu, cache, W) * 0.5 * self.nu_init[i]
        if self.kernel == "split":
            for i in range(self.nsys):
                ng = self.n_g[i]
                grad[self.off[(i, "SN")]:self.off[(i, "SN")] + ng * Nt] = gSN[self.off[(i, "SN")]:self.off[(i, "SN")] + ng * Nt]
                grad[self.off[(i, "SP")]:self.off[(i, "SP")] + ng * Nt] = gSP[self.off[(i, "SP")]:self.off[(i, "SP")] + ng * Nt]
        return f_data + f_pen, grad

    def _interp(self, series, j0, j1, w0, w1):
        series = np.asarray(series, float).ravel()
        return series[j0] * w0 + series[j1] * w1

    def _scatter_arr(self, vals, j0, j1, w0, w1):
        """Scatter per-frame ``vals`` to reduced samples: out[m] = sum_k w0[k]*vals[k]
        (m==j0[k]) + w1[k]*vals[k] (m==j1[k])."""
        out = np.zeros(self.Nt)
        np.add.at(out, j0, w0 * vals)
        np.add.at(out, j1, w1 * vals)
        return out

    def _derivs(self, dx, sig_f, nvg, sN_f, sP_f):
        """(K, dKdx, dKds, dKdsN, dKdsP) for the active kernel.  ``sig_f``/``sN_f``/
        ``sP_f`` are per-frame ``(Nfr_t,)`` widths (None where unused)."""
        if self.kernel == "gauss":
            K = _kernel(dx, sig_f[None, :], "gauss")
            dKdx, dKds, _, _ = _dkern_derivs(dx, K, "gauss", sig_f[None, :])
            return K, dKdx, dKds, None, None
        if self.kernel == "student_t":
            K = _kernel(dx, sig_f[None, :], "student_t", nu=float(nvg))
            dKdx, dKds, _, _ = _dkern_derivs(dx, K, "student_t", sig_f[None, :], nvg=float(nvg))
            return K, dKdx, dKds, None, None
        if self.kernel == "split":
            K = _kernel_split(dx, sN_f[None, :], sP_f[None, :])
            dKdx, dKds, dKdsN, dKdsP = _dkern_derivs(dx, K, "split", None, None,
                                                     sN_f[None, :], sP_f[None, :])
            return K, dKdx, dKds, dKdsN, dKdsP
        raise ValueError(self.kernel)

    def _grad_nu(self, i, waves, nu, cache, W):
        ng = self.n_g[i]
        out = np.zeros(ng)
        A_f, sig_f, theta, _ = cache[i]
        for g in range(ng):
            dx = np.mod(self.thetap[:, None] - theta[g][None, :] + _PI, _TAU) - _PI
            nvg = float(nu[i][g])
            Kp = _kernel(dx, sig_f[g, 0][None, :], "student_t", nu=nvg)
            u = dx ** 2 / (nvg * sig_f[g, 0][None, :] ** 2)
            # d/ dnu of (1+u)^(-(nu+1)/2): ln K = -(nu+1)/2 * ln(1+u); du/dnu = -u/nu
            dKdn = Kp * (-(1.0 + u) / (2.0 * nvg) + (-(nvg + 1.0) / (2.0 * (1.0 + u))) * (-u / nvg))
            out[g] = (A_f[g, 0][None, :] * (W * dKdn)).sum()
        return out

def check_gradient(XT, BG, waves, dt, Nfr, thetap, kernel="gauss", thin=20,
                   b=None, nu0=None, n_probe=6, seed=0, K=1):
    """Compare the analytic gradient to central finite differences at a random
    small delta.  Returns (max_abs_diff, max_rel_diff)."""
    if b is None:
        Nt = waves[0]["v"].size
        S0 = synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel="gauss")
        b = float(np.mean(np.abs(XT - (S0 + BG))))
    ctx = _MapRefit(XT, BG, waves, dt, Nfr, thetap, kernel, thin, b, nu0, K)
    rng = np.random.default_rng(seed)
    xd = rng.normal(0.0, 0.3, ctx.n)
    _, g = ctx.f_and_g(xd)
    h = 1e-5
    idx = rng.choice(ctx.n, size=min(n_probe, ctx.n), replace=False)
    max_abs = 0.0
    max_rel = 0.0
    for m in idx:
        xp = xd.copy(); xp[m] += h
        xm = xd.copy(); xm[m] -= h
        fp, _ = ctx.f_and_g(xp)
        fm, _ = ctx.f_and_g(xm)
        fd = (fp - fm) / (2.0 * h)
        max_abs = max(max_abs, abs(fd - g[m]))
        max_rel = max(max_rel, abs(fd - g[m]) / max(1e-12, abs(g[m])))
    return max_abs, max_rel


def map_refit(XT, BG, waves, dt, Nfr, thetap, kernel="gauss", thin=20,
              b=None, maxiter=300, gtol=1e-6, nu0=None, K=1, log=True):
    """Joint MAP re-fit of all systems' reduced series (wave-count-preserving).

    ``K>1`` (with ``kernel='gauss'``) is the K-Gaussian: each position carries K
    components (core + wide faint halos, ``COMPONENT_INIT``) at the same theta.
    Returns ``(refit_waves, nu, sigN, sigP, eps_full)`` where ``refit_waves`` is
    in the ``make_waves`` layout (``A``/``sig`` are ``(n_g, K, Nt)`` for ``K>1``),
    ``nu``/``sigN``/``sigP`` are per-system lists (None for the base Gaussian), and
    ``eps_full`` is the full-frame checker epsilon of the re-fit synthesis.
    """
    if b is None:
        Nt = waves[0]["v"].size
        S0 = synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel="gauss")
        b = float(np.mean(np.abs(XT - (S0 + BG))))
    ctx = _MapRefit(XT, BG, waves, dt, Nfr, thetap, kernel, thin, b, nu0, K)
    if log:
        print(f"  MAP: b={b:.4g}  total_n={ctx.n}  fit on {ctx.Nfr_t} frames (thin={thin}) "
              f"kernel={kernel}  waves={[ctx.n_g[i] for i in range(ctx.nsys)]}", flush=True)

    def fg(xd):
        return ctx.f_and_g(xd)

    x0 = np.zeros(ctx.n)
    f0, _ = fg(x0)
    eps0 = residual_fraction(XT, synthesize_waves(thetap, waves, dt, Nfr, ctx.Nt,
                                                  kernel="gauss") + BG)
    if log:
        print(f"  MAP: f(warm)={f0:.6f}  eps(warm)={eps0:.5f}", flush=True)
    res = minimize(fg, x0, method="L-BFGS-B", jac=True,
                   options={"maxiter": maxiter, "gtol": gtol, "maxfun": 30000})
    if log:
        print(f"  MAP: L-BFGS-B done nit={res.nit} f={res.fun:.6f} "
              f"success={res.success} ({res.message})", flush=True)
    refit_waves, nu, sigN, sigP = ctx.build(res.x)
    eps_full = residual_fraction(XT, synthesize_waves(thetap, refit_waves, dt, Nfr, ctx.Nt,
                                                      kernel=kernel, nu=nu,
                                                      sigN=sigN, sigP=sigP) + BG)
    return refit_waves, nu, sigN, sigP, eps_full
