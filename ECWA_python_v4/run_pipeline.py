#!/usr/bin/env python
# Author: Timothy J. Welch
"""Self-contained CWA -> ECWA_MATLAB pipeline for a single run.

Runs the three logical-flow stages with no manual hand-off:
    1. ``cwa``            -> ``plot4`` struct (saved to results)
    2. ``gauss_opt_runner`` -> ``wave{1,2,3}_opt_results.mat``
    3. ``gauss_syn_runner`` -> XT/BG/dt CSVs, per-wave reduced CSVs, 9 figures,
                               and the checker ``epsilon``

Usage:
    python run_pipeline.py                 # run 3433 (phi=1.46, Dm=5.76)
    python run_pipeline.py --run 4012 --phi 1.5
    python run_pipeline.py --run 3423 --phi 0.59 --movie   # + sliding-window movies
"""
import os
import sys
import time
import argparse
import numpy as np
from types import SimpleNamespace
from scipy.io import loadmat, savemat

BASE = os.path.dirname(os.path.abspath(__file__))          # ECWA_python_v4
ROOT = os.path.dirname(BASE)                               # project root
sys.path.insert(0, BASE)

from cwa.cwa import cwa                                   # noqa: E402
from cwa.plots import save_plot4_figure                   # noqa: E402
from common.det_props import load_det_props               # noqa: E402
from ecwa.run_opt import gauss_opt_runner                 # noqa: E402
from ecwa.run_syn import gauss_syn_runner                 # noqa: E402


def run_pipeline(run=3433, phi=1.46, Dm=5.76, do_plot=True, movie=False,
                 re_fit=False, re_fit_kernel="gauss", re_fit_K=1,
                 re_fit_thin=1, re_fit_maxiter=1500, re_fit_gtol=1e-8,
                 base=BASE):
    det_path = os.path.join(base, "cwa", "H2AirDetProp.xlsx")   # bundled in cwa/ (self-contained)
    out = os.path.join(base, "results", f"run{run}data")
    os.makedirs(out, exist_ok=True)

    # --- stage 1: CWA -> plot4 ---
    print("== CWA ==", flush=True)
    t_start = time.time()
    fm = loadmat(os.path.join(ROOT, "XT_diagrams", f"Run_{run:05d}-full.mat"))
    XTS = {"XT": fm["XT"], "t0": fm["t0"].squeeze(), "fps": float(fm["fps"][0, 0])}
    dat = load_det_props(det_path)
    cwa_res = cwa({}, XTS, phi, Dm, [], dat)
    plot4 = {k: np.asarray(v) for k, v in cwa_res["plot4"].items()}
    savemat(os.path.join(out, f"plot4_run{run:03d}.mat"), {"plot4": plot4})
    save_plot4_figure(plot4, run, os.path.join(out, f"plot4_run{run:03d}.png"))
    plot4_ns = SimpleNamespace(**plot4)

    XT = np.asarray(XTS["XT"], float)
    t0 = float(np.asarray(XTS["t0"]).ravel()[0])
    fps = float(XTS["fps"])
    t = np.arange(XT.shape[1]) / fps + t0
    print(f"   CWA: {time.time() - t_start:.1f} s", flush=True)

    # --- stage 2: ECWA optimisation ---
    print("== ECWA optimisation ==", flush=True)
    t_start = time.time()
    gauss_opt_runner(XT, t, fps, phi, Dm, det_path, plot4_ns, out, log=True)
    print(f"   optimisation: {time.time() - t_start:.1f} s", flush=True)

    # --- stage 3: ECWA synthesis ---
    print("== ECWA synthesis ==" + (" (PECWA_julia MAP re-fit)" if re_fit else ""),
          flush=True)
    t_start = time.time()
    syn = gauss_syn_runner(XT, t, fps, out, out, plot=(do_plot or movie), movie=movie,
                           re_fit=re_fit, re_fit_kernel=re_fit_kernel, re_fit_K=re_fit_K,
                           re_fit_thin=re_fit_thin, re_fit_maxiter=re_fit_maxiter,
                           re_fit_gtol=re_fit_gtol)
    print(f"   synthesis: {time.time() - t_start:.1f} s", flush=True)
    return syn


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", type=int, default=3433)
    ap.add_argument("--phi", type=float, default=1.46)
    ap.add_argument("--Dm", type=float, default=5.76)
    ap.add_argument("--no-plot", action="store_true")
    ap.add_argument("--movie", action="store_true",
                    help="also write a sliding-window animation (mp4 if ffmpeg is "
                         "available, else gif) of each x-t diagram")
    ap.add_argument("--re-fit", action="store_true",
                    help="warm-start each wave's reduced series into the PECWA_julia "
                         "MAP re-fit and synthesise the improved waves")
    ap.add_argument("--re-fit-kernel", default="gauss",
                    choices=["gauss", "student_t", "split"])
    ap.add_argument("--re-fit-K", type=int, default=1,
                    help="K-Gaussian components per position (2/3); K>1 two-stage "
                         "warm-starts from a Gaussian re-fit")
    args = ap.parse_args()
    res = run_pipeline(args.run, args.phi, args.Dm,
                       do_plot=not args.no_plot, movie=args.movie,
                       re_fit=args.re_fit, re_fit_kernel=args.re_fit_kernel,
                       re_fit_K=args.re_fit_K)
    print(f"epsilon = {res['epsilon']:.10e}")
