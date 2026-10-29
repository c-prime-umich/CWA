#!/usr/bin/env python
# Author: Timothy J. Welch
"""Tests for the PECWA_julia MAP re-fit port (ecwa.maprefit).

The port must reproduce the reference v4 ``add_wave`` synthesis bit-for-bit
(single Gaussian, on the reduced series) before any re-fit is trusted.  Later
tests check the MAP re-fit lowers epsilon on the run-3433 reduced series.
"""
import os
import sys
import numpy as np
import pytest

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # ECWA_python_v4
ROOT = os.path.dirname(BASE)
if BASE in sys.path:
    sys.path.remove(BASE)
sys.path.insert(0, BASE)
# The sibling v3/ecwa is a regular package too; a co-collected test module may
# have already cached `ecwa` as v3/ecwa (which lacks maprefit). Re-resolve to v4.
for _m in [m for m in list(sys.modules) if m == "ecwa" or m.startswith("ecwa.")]:
    del sys.modules[_m]

from ecwa.core import add_wave, checker, clean_xt            # noqa: E402
from ecwa.maprefit import (synthesize_gauss, make_waves,
                           synthesize_waves, residual_fraction,
                           check_gradient, map_refit)        # noqa: E402
from ecwa.io import load_xt_full                             # noqa: E402

_W1 = os.path.join(BASE, "results", "run3433data", "wave_sys_1")


def _nfr_from_nt(nt, win=20):
    """Full-frame count for a reduced series of length nt (sample m at frame m*win)."""
    return (nt - 1) * win + 1


def _load_reduced(dirpath):
    """Load a single-Gaussian reduced series (theta0 scalar, A/sig/v Nt arrays)."""
    th0 = float(np.atleast_1d(np.loadtxt(dirpath + os.sep + "theta0.csv",
                                         delimiter=",")).ravel()[0])
    sig = np.loadtxt(dirpath + os.sep + "sigma.csv", delimiter=",")
    A = np.loadtxt(dirpath + os.sep + "A.csv", delimiter=",")
    v = np.loadtxt(dirpath + os.sep + "v.csv", delimiter=",")
    return th0, sig, A, v


def test_vectorized_synth_matches_add_wave_single():
    """synthesize_gauss == reference add_wave for the run-3433 wave-1 reduced series."""
    th0, sig, A, v = _load_reduced(_W1)
    Nfr = _nfr_from_nt(len(sig))              # 501 -> 10001
    # reference (v4 per-frame loop)
    thetap = np.arange(101) * (2.0 * np.pi / 101)
    ref = add_wave(np.zeros((101, Nfr)), Nfr, thetap, th0, v, A, sig, dt=2e-5, win=20)
    # vectorized port (matches to float64 accumulation ~1e-11 relative)
    got = synthesize_gauss(thetap, th0, A, sig, v, dt=2e-5, Nfr=Nfr, win=20)
    assert got.shape == ref.shape
    assert np.allclose(got, ref, rtol=1e-9, atol=1e-6), \
        f"max rel diff {(np.abs(got - ref) / (np.abs(ref) + 1e-12)).max():.3e}"


def test_make_waves_matches_add_wave_two():
    """A two-Gaussian wave (shared v) synthesizes the same as two add_wave calls."""
    th0, sig, A, v = _load_reduced(_W1)
    Nfr = _nfr_from_nt(len(sig))
    thetap = np.arange(101) * (2.0 * np.pi / 101)
    dt = 2e-5
    # reference: two add_wave calls (a primary + a pi-offset companion)
    ref = np.zeros((101, Nfr))
    ref = add_wave(ref, Nfr, thetap, th0, v, A, sig, dt=dt, win=20)
    A2, sig2 = A * 0.5, sig.copy()
    th02 = (th0 + np.pi) % (2.0 * np.pi)
    ref = add_wave(ref, Nfr, thetap, th02, v, A2, sig2, dt=dt, win=20)
    # port: one two-gaussian wave
    got = synthesize_gauss(thetap, [th0, th02], np.stack([A, A2]),
                           np.stack([sig, sig2]), v, dt=dt, Nfr=Nfr, win=20)
    assert np.allclose(got, ref, rtol=1e-9, atol=1e-6), \
        f"max rel diff {(np.abs(got - ref) / (np.abs(ref) + 1e-12)).max():.3e}"


def _load_3433():
    """(XT, BG, waves, dt, Nfr, thetap) for run 3433 (all single-Gaussian)."""
    XT, t0, fps = load_xt_full(ROOT, 3433)
    Nfr = XT.shape[1]
    thetap = np.arange(XT.shape[0]) * (2.0 * np.pi / XT.shape[0])
    BG = XT - clean_xt(XT, win=20)
    waves = make_waves(os.path.join(BASE, "results", "run3433data"))
    return XT, BG, waves, 1.0 / fps, Nfr, thetap


@pytest.mark.parametrize("kernel,nu0", [("gauss", None), ("student_t", 8.0),
                                        ("split", None)])
def test_gradient_analytic_matches_fd(kernel, nu0):
    """The analytic gradient must match central finite differences (all kernels)."""
    XT, BG, waves, dt, Nfr, thetap = _load_3433()
    max_abs, max_rel = check_gradient(XT, BG, waves, dt, Nfr, thetap,
                                      kernel=kernel, thin=20, nu0=nu0,
                                      n_probe=10, seed=7)
    # 1-norm subgradient kink + FD error allow a loose-but-meaningful bound
    assert max_rel < 5e-3, f"{kernel}: gradient max_rel {max_rel:.3e}"


def test_map_refit_lowers_epsilon_and_preserves_waves():
    """The Gaussian MAP re-fit must lower the run-3433 epsilon and keep the counts."""
    XT, BG, waves, dt, Nfr, thetap = _load_3433()
    Nt = waves[0]["v"].size
    S0 = synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel="gauss")
    eps0 = residual_fraction(XT, S0 + BG)
    counts0 = [int(w["th0"].size) for w in waves]
    refit, nu, sigN, sigP, eps = map_refit(XT, BG, waves, dt, Nfr, thetap,
                                            kernel="gauss", thin=20, maxiter=80,
                                            gtol=1e-6, log=False)
    counts1 = [int(w["th0"].size) for w in refit]
    assert eps < eps0, f"re-fit did not lower epsilon: {eps:.4f} !< {eps0:.4f}"
    assert counts0 == counts1, f"wave count changed: {counts0} -> {counts1}"


def test_load_refit_waves_round_trip(tmp_path):
    """load_refit_waves inverts the driver's save_refit npz layout (any K)."""
    from ecwa.maprefit import load_refit_waves
    n_t, K, nsys = 50, 2, 3
    waves = []
    for i in range(nsys):
        n_g = 1 + (i % 2)                     # mix 1- and 2-position systems
        waves.append({"th0": np.array([0.5 * (i + 1)] * n_g),
                      "A": (np.random.rand(n_g, K, n_t) * 100).astype(np.float64),
                      "sig": (np.random.rand(n_g, K, n_t) * 0.2 + 0.1),
                      "v": np.random.rand(n_t) * 100})
    for i, w in enumerate(waves):
        d = tmp_path / f"wave_sys_{i + 1}"
        d.mkdir()
        np.savez(d / "waves.npz", th0=w["th0"], A=w["A"], sig=w["sig"], v=w["v"])
    loaded = load_refit_waves(str(tmp_path))
    assert len(loaded) == nsys
    for i, w in enumerate(waves):
        for key in ("A", "sig", "v", "th0"):
            assert np.allclose(loaded[i][key], w[key]), f"sys {i} {key} mismatch"
