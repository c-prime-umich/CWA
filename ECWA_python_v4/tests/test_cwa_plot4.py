#!/usr/bin/env python
# Author: Timothy J. Welch
"""End-to-end validation: my CWA ``plot4`` must reproduce the saved MATLAB
ground truth (CWA_MATLAB/CWA_results/plot4_run3433.mat) to high precision."""
import os
import numpy as np
import pytest

from scipy.io import loadmat

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GT = f"{ROOT}/CWA_MATLAB/CWA_results/plot4_run3433.mat"
pytestmark = pytest.mark.skipif(not os.path.exists(GT), reason="ground-truth not present")


def _load_plot4(path):
    m = loadmat(path, squeeze_me=True, struct_as_record=False)
    p = m["plot4"]
    return {f: np.asarray(getattr(p, f), float) for f in p._fieldnames}


def _run_cwa():
    from cwa.cwa import cwa
    from common.det_props import load_det_props
    fm = loadmat(f"{ROOT}/XT_diagrams/Run_03433-full.mat")
    XTS = {"XT": fm["XT"], "t0": fm["t0"].squeeze(), "fps": float(fm["fps"][0, 0])}
    dat = load_det_props(f"{ROOT}/ECWA_python_v4/cwa/H2AirDetProp.xlsx")
    return cwa({}, XTS, 1.46, 5.76, [6.8, 6.9], dat)


def test_cwa_plot4_matches_ground_truth():
    res = _run_cwa()
    mine = {k: np.asarray(res["plot4"][k], float) for k in res["plot4"]}
    gt = _load_plot4(GT)

    # Fields unaffected by the vcdets cross-plane correction: must match the
    # reference bit-for-bit (to ~1e-12 in practice).
    for k in ["detins", "cdetins", "crwpins", "ttp", "vdets", "vcrwps", "intens"]:
        assert mine[k].shape == gt[k].shape, f"{k} shape {mine[k].shape} vs {gt[k].shape}"
        assert np.array_equal(np.isnan(mine[k]), np.isnan(gt[k])), f"{k} NaN pattern differs"
        a = mine[k][~np.isnan(mine[k])]
        b = gt[k][~np.isnan(gt[k])]
        assert np.allclose(a, b, rtol=1e-8, atol=1e-8), f"{k} values differ (max {np.abs(a-b).max()})"

    # vcdets: the reference was produced by the *buggy* original (cross-plane fit).
    # The port corrects it, so it won't equal the reference.  Assert the fix only
    # ever adds a detection (never blanks a reference-finite value) and is complete.
    assert mine["vcdets"].shape == gt["vcdets"].shape
    assert not (np.isnan(mine["vcdets"]) & np.isfinite(gt["vcdets"])).any(), \
        "corrected vcdets blanked a reference-finite value"
    assert np.isfinite(mine["vcdets"]).sum() > 0.5 * mine["vcdets"].size

    assert int(mine["Ntp"]) == int(gt["Ntp"])
    assert np.isclose(mine["maxI"], gt["maxI"], rtol=1e-9)
    assert np.isclose(mine["minI"], gt["minI"], rtol=1e-9)


def test_cwa_derivatives():
    res = _run_cwa()
    assert np.isclose(res["Ucj"], 2081.99944716477, rtol=1e-9)
    assert np.isclose(res["Cd"], 5.76 * np.pi * 0.0254)
    assert res["plot4"]["Ntp"] == 140


def test_vcdets_lean_not_all_nan():
    """Regression for a cross-plane bug in the original CWA.m.

    The vcdets fit read ``lights(detn, ...)`` (the main-detonation plane) while its
    gate/location used ``lights(1, ...)``.  For rich runs (e.g. 3433) ``detn`` is
    almost always 1 so it was harmless; for lean runs (e.g. 3423, phi=0.59)
    ``detn`` is 2, the fit sampled a zeroed plane, the quadratic coefficient
    collapsed to zero and every ``vcdets`` came back NaN.  The port fits the gate
    plane, so ``vcdets`` must be substantially finite here.
    """
    from cwa.cwa import cwa
    from common.det_props import load_det_props
    fm = loadmat(f"{ROOT}/XT_diagrams/Run_03423-full.mat")
    XTS = {"XT": fm["XT"], "t0": fm["t0"].squeeze(), "fps": float(fm["fps"][0, 0])}
    res = cwa({}, XTS, 0.59, 5.76, [],
              load_det_props(f"{ROOT}/ECWA_python_v4/cwa/H2AirDetProp.xlsx"))
    vcdets = np.asarray(res["plot4"]["vcdets"], float).ravel()
    assert np.isfinite(vcdets).sum() > 0.5 * vcdets.size, \
        f"vcdets all/too-many NaN: {int(np.isnan(vcdets).sum())}/{vcdets.size}"


def test_save_plot4_figure_writes(tmp_path):
    """The original CWA Plot-4 figure (wave velocities vs time, jet intensity)
    is recreated as a non-trivial PNG."""
    from cwa.plots import save_plot4_figure
    res = _run_cwa()
    out = os.path.join(str(tmp_path), "plot4_run3433.png")
    ret = save_plot4_figure(res["plot4"], 3433, out)
    assert ret == out
    assert os.path.exists(out) and os.path.getsize(out) > 1000
