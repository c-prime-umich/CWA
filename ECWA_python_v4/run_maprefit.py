#!/usr/bin/env python
# Author: Timothy J. Welch
"""PECWA_julia MAP re-fit driver for ECWA_python_v4.

For each run: load XT, form the v4 background (BG = XT - clean_xt(XT)), load the
v4 warm-start reduced series (make_waves), run the MAP re-fit (a chosen kernel),
and report baseline vs re-fit checker epsilon, the (unchanged) wave counts, and
wall time.  This is the test harness for incorporating the PECWA_julia methods
without losing the physical wave counts.

Usage:
    python run_maprefit.py                      # gaussian re-fit, run 3433
    python run_maprefit.py --runs 3423 3426 3433 3443
    python run_maprefit.py --kernel student_t --nu0 20
"""
import os
import sys
import time
import argparse
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))     # ECWA_python_v4
ROOT = os.path.dirname(BASE)
sys.path.insert(0, BASE)

from ecwa.core import clean_xt
from ecwa.io import load_xt_full
from ecwa.maprefit import (make_waves, synthesize_waves, residual_fraction,
                           map_refit)

# run -> phi (Dm fixed 5.76)
PHI = {3423: 0.59, 3426: 0.85, 3433: 1.46, 3443: 0.81}
DM = 5.76


def wave_counts(waves):
    return [int(w["th0"].size) for w in waves]


def save_refit(run, kernel, K, refit_waves, nu, sigN, sigP, base=BASE):
    """Write the re-fit reduced series to
    results/maprefit/run{run}_{kernel}_K{K}/wave_sys_{i}/waves.npz (one .npz per
    position-system: th0, A[n_g,K,n_t], sig[n_g,K,n_t], v[n_t]; +nu/sigN/sigP
    when present).  Unambiguous for any K and any position count.  Load with
    ecwa.maprefit.load_refit_waves and synthesize with ecwa.maprefit.
    synthesize_waves."""
    out = os.path.join(base, "results", "maprefit", f"run{run}_{kernel}_K{K}")
    for i, w in enumerate(refit_waves):
        d = os.path.join(out, f"wave_sys_{i + 1}")
        os.makedirs(d, exist_ok=True)
        payload = {"th0": np.atleast_1d(w["th0"]), "A": np.asarray(w["A"]),
                   "sig": np.asarray(w["sig"]), "v": np.asarray(w["v"])}
        if nu is not None:
            payload["nu"] = np.atleast_1d(nu[i])
        if sigN is not None:
            payload["sigN"] = np.asarray(sigN[i])
            payload["sigP"] = np.asarray(sigP[i])
        np.savez(os.path.join(d, "waves.npz"), **payload)
    return out


def run_case(run, kernel="gauss", thin=20, maxiter=300, gtol=1e-5, nu0=None,
             K=1, save=False, plot=False, log=True):
    t_start = time.time()
    XT, t0, fps = load_xt_full(ROOT, run)
    Nb, Nfr = XT.shape
    thetap = np.arange(Nb) * (2.0 * np.pi / Nb)
    dt = 1.0 / fps
    BG = XT - clean_xt(XT, win=20)                     # v4 background (full)

    res_dir = os.path.join(BASE, "results", f"run{run}data")
    waves = make_waves(res_dir)
    Nt = waves[0]["v"].size
    counts = wave_counts(waves)

    if log:
        print(f"\n=== run {run} (phi={PHI[run]})  kernel={kernel}  K={K}  waves={counts} ===",
              flush=True)

    # baseline (warm start) full-frame epsilon
    S0 = synthesize_waves(thetap, waves, dt, Nfr, Nt, kernel="gauss")
    eps0 = residual_fraction(XT, S0 + BG)
    if log:
        print(f"  baseline eps = {eps0:.5f}  ({100 * eps0:.3f}%)", flush=True)

    # MAP re-fit (for K>1: two-stage -- Gaussian re-fit first, then K re-fit from
    # that warm start, matching the Julia's stage_k)
    t_fit = time.time()
    ws = waves
    if K > 1 and kernel == "gauss":
        ws, _, _, _, eps_stage1 = map_refit(
            XT, BG, waves, dt, Nfr, thetap, kernel="gauss", thin=thin,
            maxiter=maxiter, gtol=gtol, log=log)
        if log:
            print(f"  [stage 1] gauss re-fit eps = {eps_stage1:.5f}", flush=True)
    refit_waves, nu, sigN, sigP, eps_full = map_refit(
        XT, BG, ws, dt, Nfr, thetap, kernel=kernel, thin=thin,
        maxiter=maxiter, gtol=gtol, nu0=nu0, K=K, log=log)
    fit_wall = time.time() - t_fit
    counts_after = wave_counts(refit_waves)

    if log:
        print(f"  re-fit   eps = {eps_full:.5f}  ({100 * eps_full:.3f}%)   "
              f"delta_eps = {100 * (eps0 - eps_full):+.3f} pts", flush=True)
        print(f"  waves: {counts} -> {counts_after}   "
              f"preserved={counts == counts_after}", flush=True)
        if nu is not None:
            print(f"  nu (student-t) = {[ [round(float(x),3) for x in n] for n in nu] }",
                  flush=True)
        print(f"  fit wall = {fit_wall:.1f} s   total = {time.time() - t_start:.1f} s",
              flush=True)
    if save:
        saved = save_refit(run, kernel, K, refit_waves, nu, sigN, sigP)
        if log:
            print(f"  saved re-fit reduced series -> {saved}", flush=True)
    if plot:
        # fig4 = the re-created waves (S) at full frame; fig3 = clean_xt(XT)
        # (= XT - BG, the data's wave crests, identical for every method of a run).
        # save_all_figures writes all 9 reference figures to
        # results/maprefit/plots/{kernel}_K{K}_{run}/ for visual wave-count checks.
        plot_dir = os.path.join(BASE, "results", "maprefit", "plots",
                                f"{kernel}_K{K}_{run}")
        os.makedirs(plot_dir, exist_ok=True)
        t = np.arange(Nfr) / fps + t0
        XT_cleaned = XT - BG                 # == clean_xt(XT)
        S = synthesize_waves(thetap, refit_waves, dt, Nfr, Nt, kernel=kernel,
                             nu=nu, sigN=sigN, sigP=sigP)
        eps_check = residual_fraction(XT, S + BG)
        from ecwa.plots import save_all_figures
        save_all_figures(t, fps, thetap, XT, XT_cleaned, S, BG, plot_dir,
                         win=20, run=run)
        if log:
            print(f"  plots -> {plot_dir}   "
                  f"(S eps = {100 * eps_check:.3f}% vs re-fit {100 * eps_full:.3f}%)",
                  flush=True)
    return {"run": run, "kernel": kernel, "eps0": eps0, "eps": eps_full,
            "counts": counts, "counts_after": counts_after,
            "fit_wall": fit_wall, "total_wall": time.time() - t_start,
            "waves": refit_waves, "nu": nu, "sigN": sigN, "sigP": sigP}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, nargs="+", default=[3433])
    ap.add_argument("--kernel", default="gauss",
                    choices=["gauss", "student_t", "split"])
    ap.add_argument("--thin", type=int, default=20)
    ap.add_argument("--maxiter", type=int, default=300)
    ap.add_argument("--gtol", type=float, default=1e-5)
    ap.add_argument("--nu0", type=float, default=None)
    ap.add_argument("--k", type=int, default=1,
                    help="K-Gaussian components per position (2/3); two-stage "
                         "warm-starts from a Gaussian re-fit")
    ap.add_argument("--save", action="store_true",
                    help="write the re-fit reduced series to results/maprefit/")
    ap.add_argument("--plot", action="store_true",
                    help="write fig1..fig9 (incl. fig3_cleaned_XT / fig4_syn_XT) "
                         "to results/maprefit/plots/{kernel}_K{k}_{run}/")
    ap.add_argument("--csv", type=str, default=None,
                    help="append results to this CSV")
    args = ap.parse_args()

    rows = []
    for run in args.runs:
        r = run_case(run, kernel=args.kernel, thin=args.thin, maxiter=args.maxiter,
                     gtol=args.gtol, nu0=args.nu0, K=args.k, save=args.save,
                     plot=args.plot)
        r["K"] = args.k
        rows.append(r)
    if args.csv:
        import csv
        new = not os.path.exists(args.csv)
        with open(args.csv, "a", newline="") as f:
            w = csv.writer(f)
            if new:
                w.writerow(["run", "kernel", "thin", "eps0_pct", "eps_pct",
                            "delta_pts", "waves", "waves_after", "preserved",
                            "fit_wall_s", "total_wall_s"])
            for r in rows:
                w.writerow([r["run"], r["kernel"], args.thin, f"{100*r['eps0']:.4f}",
                            f"{100*r['eps']:.4f}", f"{100*(r['eps0']-r['eps']):+.4f}",
                            r["counts"], r["counts_after"],
                            r["counts"] == r["counts_after"],
                            f"{r['fit_wall']:.1f}", f"{r['total_wall']:.1f}"])
        print(f"\nappended {len(rows)} row(s) to {args.csv}", flush=True)


if __name__ == "__main__":
    main()
