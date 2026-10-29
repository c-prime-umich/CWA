# ECWA_python

Python port of the ECWA wave‑analysis pipeline, with the
PECWA_julia MAP re‑fit incorporated as an **opt‑in** synthesis step that
possibly lowers the checker ε.

For each dataset it runs:

```
CWA  ->  3‑wave Gaussian optimisation  ->  synthesis  (checker ε + 9 figures)
                 [opt‑in: PECWA_julia MAP re‑fit between optimisation and synthesis]
```

## Directory layout

```
ECWA_python_v4/
├── run_pipeline.py         # entry point: CWA -> opt -> syn (+ optional re-fit)
├── run_maprefit.py         # driver: compare re-fit methods (ε / wall / wave counts)
├── requirements.txt        # Python dependencies (create a venv: pip install -r requirements.txt)
├── cwa/                    # continuous-wave analysis: cwa.py, plots.py, xt_reader.py, helpers.py,
│                           #   H2AirDetProp.xlsx (bundled detector properties)
├── common/                 # shared helpers: det_props.py, interp.py
├── ecwa/
│   ├── core.py             # clean_xt, movmean, add_wave, checker, periodic_gaussian
│   ├── io.py               # load_xt_full / load_xt_short (read ../XT_diagrams)
│   ├── opt.py              # auto_select_waves (chooses 1 vs 2 Gaussians per system)
│   ├── run_opt.py          # gauss_opt_runner -> wave{1,2,3}_opt_results.mat
│   ├── run_syn.py          # gauss_syn_runner -> XT/BG CSVs, reduced CSVs, 9 figures, ε
│   │                       #     (also hosts the opt-in PECWA_julia re-fit stage)
│   ├── maprefit.py         # the ported PECWA_julia MAP re-fit
│   │                       #     (gauss / student-t / split / K-gauss, analytic gradient)
│   └── plots.py            # the 9 reference figures (fig1..fig9)
├── tests/                  # pytest suite (synthesis, re-fit gradient, save/load round-trip, ...)
└── results/
    ├── run<NNNN>data/      # per-run pipeline output (see below)
    └── maprefit/           # re-fit results: REPORT.md, results_*.csv, plots/, saved series
```

## Setup

**Python environment** — self-contained; create a local venv from `requirements.txt`
(Python 3.13):

```
cd ECWA_python_v4
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt    # numpy, scipy, matplotlib, pandas, openpyxl, Pillow, pytest
```

**Input data** — the only external dependency is the XT diagrams, provided separately as a sibling
of this directory (the detector properties are bundled in `cwa/H2AirDetProp.xlsx`):

```
<root>/
├── ECWA_python_v4/     # this directory (the code, self-contained)
└── XT_diagrams/        # Run_<NNNNN>-full.mat   -- the sensor-time XT diagrams
```

> **Provenance (not required to run):** this is a Python port of the `ECWA_MATLAB` and `PECWA_julia`
> reference (`checker.m`, `Gauss_Opt_Runner.m`, `Gauss_Syn_Runner.m`); the re-fit methods in
> `ecwa/maprefit.py` are ported.

## How to run

**Baseline** (the reference behaviour, no re‑fit):

```
python run_pipeline.py                          # run 3433 (phi=1.46, Dm=5.76)
python run_pipeline.py --run 3423 --phi 0.59
python run_pipeline.py --run 3423 --movie       # + sliding-window animations (mp4/gif)
```

**With the PECWA_julia MAP re-fit** (opt-in; improves ε, preserves the wave count):

```
python run_pipeline.py --run 3433 --re-fit                 # Gaussian re-fit (K=1)
python run_pipeline.py --run 3433 --re-fit --re-fit-K 2    # K=2 K-Gaussian (best)
python run_pipeline.py --run 3433 --re-fit --re-fit-kernel split
```

**Compare re-fit methods** (ε / wall / wave counts; writes to `results/maprefit/`):

```
python run_maprefit.py --runs 3423 3426 3433 3443 --kernel gauss --k 2 \
    --thin 1 --maxiter 1500 --gtol 1e-8 --save --plot --csv results/maprefit/results_k2.csv
```

**Tests:**

```
python -m pytest tests/                 # full suite
python -m pytest tests/test_maprefit.py # just the re-fit tests
```

> Most tests are self-contained. `tests/test_ecwa.py` also validates the port against the
> reference outputs (`ECWA_python_v3` / `ECWA_MATLAB`), which are **not** part of this
> directory — run the full suite only if those references are present.

`--thin 1` fits on the full 10 001‑frame record (~2–4 min/run); `--thin 20` fits on the 501‑frame
reduced record (~5–25 s/run) for a fast preview. Both give the same wave count.

## Per-run output (`results/run<NNNN>data/`)

```
XT.csv, dt.csv, BG.csv              # data, time step, removed background
plot4_run<NNNN>.mat / .png          # CWA detection
wave{1,2,3}_opt_results.mat         # full-rate optimised (theta0, sigma, A, v) per system
wave_sys_{1,2,3}/                   # the reduced series: A.csv / sigma.csv / v.csv / theta0.csv
                                     #   (multi-Gaussian: A_<g>.csv; re-fit K>1: A_<g>c<c>.csv)
fig1_original_XT .. fig9_A_theta    # the 9 reference figures
                                     #   fig3 = cleaned_XT (data crests), fig4 = syn_XT (recreated)
```

## Results (runs 3423 / 3426 / 3433 / 3443, Dm = 5.76)

Checker ε = ‖XT − (syn + BG)‖₁ / ‖XT‖₁. **“waves”** is the per-system count, auto-selected by the
optimiser; **every re-fit method preserves it** (the re-fit is a warm-start refinement and can only
adjust amplitude / position / width, never add or drop a crest).

| run  | φ    | waves   | baseline | Gaussian (K=1) | **K=2 (best)** | Split-σ | Student-t |
|------|------|---------|----------|----------------|----------------|---------|-----------|
| 3423 | 0.59 | [2,1,1] | 6.254%   | 3.925%         | **3.399%**     | 3.918%  | 6.207%    |
| 3426 | 0.85 | [2,2,1] | 6.361%   | 4.137%         | **3.408%**     | 4.290%  | 6.316%    |
| 3433 | 1.46 | [1,1,1] | 14.788%  | 9.362%         | **8.766%**     | 9.825%  | 14.619%   |
| 3443 | 0.81 | [2,1,1] | 9.073%   | 6.161%         | **6.002%**     | 6.159%  | 9.017%    |

- **K=2 K‑Gaussian** is the best: each wave becomes a core + a faint wide halo **at the same θ0 and
  the same velocity v**, so no wave identity or count changes. Improves ε by **2.9–6.0 pts** over
  baseline. (Two‑stage warm start: Gaussian re‑fit → K=2 re‑fit.)
- **Gaussian (K=1)** is the simpler strong alternative (same model as v4, just re‑fit): 2.3–5.4 pts.
- **Split‑σ ≈ Gaussian** (no consistent gain).
- **Student‑t does not win**: with free ν it either stalls at the warm start (≈ baseline) or drives
  ν→0 (a near‑Dirac over‑fit, 12.6% on 3433).
- The **counter‑wave** variant (PECWA_julia “phys”) *changes* the wave identities (co‑rotating →
  counter‑rotating) and is 3433‑specific, so it is **not** a wave‑count‑safe improvement.

The full write‑up (per-method wall times, the gradient/round-trip validation, and the saved K=2
reduced series) is in `results/maprefit/REPORT.md`; the per-method run logs are `results/maprefit/*.log`
and the method-run figures are `results/maprefit/plots/<method>_K<k>_<run>/`.
