# PECWA_julia methods incorporated into ECWA_python_v4 — ε / wall / physicality report

**Goal:** port the PECWA_julia checker/fit variants into `ECWA_python_v4` (pure numpy/scipy — no JAX/Julia in
the env), test each on runs 3423/3426/3433/3443, and find the methods that **improve the wave residual ε
without changing the wave-count physicality** (i.e. no new wave identities, same rotation structure).

**Model context:** the v4 checker synthesizes 3 co-rotating Gaussian wave systems on the reduced series
(Nt=501, every 20th frame, double-smoothed), upsamples to full frame (Nfr=10001), and reports
`ε = ‖XT − (S + BG)‖₁ / ‖XT‖₁`. The baseline below is that v4 synthesis (warm start from the
`wave{i}_opt_results.mat` reduced series).

**Method being ported (the MAP re-fit, `fit_map.jl`):** re-fit the reduced series (A, σ, v, θ0 — and, for the
shape variants, extra shape params) against the full-frame XT−BG. Uses δ-offsets around the warm start
(actual = init + scale·δ; σ on a log scale), a random-walk smoothness prior, the Laplace noise scale
b = mean|XT − (S0 + BG)|, and L-BFGS-B with an **analytic** gradient (validated to ≤2e-3 rel vs finite
differences for every kernel). `thin=1` → full-frame (authoritative); `thin=20` → 501-frame preview.

## Baseline (v4 synthesis, before any re-fit)

| run | φ   | ε (v4)   | wave counts |
|-----|-----|----------|-------------|
| 3423| 0.59| 6.254%   | [2,1,1]     |
| 3426| 0.85| 6.361%   | [2,2,1]     |
| 3433| 1.46| 14.788%  | [1,1,1]     |
| 3443| 0.81| 9.073%   | [2,1,1]     |

## Results (thin=1 full-frame, maxiter=1500, gtol=1e-8, 3 cores)

| Method | 3423 | 3426 | 3433 | 3443 | counts preserved | fit wall/run |
|--------|------|------|------|------|------------------|--------------|
| v4 baseline | 6.254% | 6.361% | 14.788% | 9.073% | — | — |
| **Gaussian MAP re-fit** (Method 1) | 3.925% | 4.137% | 9.362% | 6.161% | all ✓ | ~150–240 s |
| Student-t, ν free (Method 2) | 6.207% | 6.315% | 14.619% | 9.017% | all ✓ | ~5 s (early-stopped) |
| Split-σ (Method 3) | 3.918% | 4.290% | 9.825% | 6.159% | all ✓ | ~220–340 s |
| **K=2 K-Gaussian** (Method 4, two-stage) | **3.399%** | **3.408%** | **8.766%** | **6.002%** | all ✓ | ~250–390 s |
| Counter-wave (Method 5, 3433 only) | — | — | 9.401%* | — | ✗ (identities change) | ~50 s (3433) |

\* Counter-wave simple version (re-fit primary + 2 counter-rotating waves at the measured v, Gaussian kernel).
The Julia's full "phys" variant (split-σ K=2 + higher sample density) is 8.04% on 3433.

## Interpretation

- **Winner — K=2 K-Gaussian (Method 4).** Best ε on all 4 (2.9–6.0 pts better than v4), wave counts preserved.
  Each wave position becomes a core + a faint wide halo **at the same θ0 and the same velocity v** — only the
  *profile* gains a second (broader) Gaussian, so no wave identity (position/velocity/count) changes. Two-stage
  warm start: Gaussian re-fit → K=2 re-fit (matches the Julia's `stage_k`). This reproduces the Julia's finding
  that K beats the single Gaussian. Round-trip verified: the saved `waves.npz` re-synthesizes to the same ε.
- **Simpler strong alternative — Gaussian MAP re-fit (Method 1).** Same model as v4, just re-fit on the reduced
  series with the smoothness prior + analytic gradient. Improves ε by 2.3–5.4 pts, counts preserved, and is
  the least intrusive change. Use this if the two-stage K=2 complexity is not wanted.
- **Student-t (Method 2) does NOT win.** With ν free the re-fit either (a) stalls near the warm start (the stuck-ν
  flat direction makes the gradient drop early → ≈ baseline) or (b) drives ν→0 (a near-Dirac overfit, 12.6% on
  3433). At ν=20 the t-kernel ≈ Gaussian, so it can at best match Method 1, not beat it.
- **Split-σ (Method 3) ≈ Gaussian.** A small number of profiles fit marginally better/worse; no consistent
  improvement over Method 1 (e.g. 3433: 9.825% vs 9.362%).
- **Counter-wave (Method 5) changes the physics.** It replaces the co-rotating companions with measured
  counter-rotating waves (v = +17780/+14481 rad/s) — the wave *identities* change, so it violates the
  physicality constraint. It is also 3433-specific (the counter-wave constants are measured from that run).
  In my simple port it matches the Gaussian re-fit (9.40%), not the Julia's elaborate 8.04%.

## Deliverables (all under `ECWA_python_v4/`)

- `ecwa/maprefit.py` — the ported MAP re-fit: vectorized full-frame synthesis (validated to 2.3e-11 rel vs
  the v4 `add_wave`), analytic per-kernel gradients, the `_MapRefit` optimizer (Gaussian / Student-t /
  Split-σ / K-Gaussian), warm-start `make_waves`, `check_gradient`, `map_refit`.
- `tests/test_maprefit.py` — 6 tests (all passing): synthesis vs `add_wave` (1- and 2-system), analytic
  gradient vs finite differences (gauss / student_t / split), and a re-fit smoke test.
- `run_maprefit.py` — driver: `--runs --kernel {gauss,student_t,split} --k {1,2,3} --thin --maxiter --gtol
  --nu0 --save --csv`.
- `results/maprefit/results_*.csv` — per-method results (gauss / student_t / split / k2).
- `results/maprefit/run{run}_gauss_K2/wave_sys_{i}/waves.npz` — saved improved reduced series (K=2
  winner), one npz per position-system (th0, A[n_g,K,n_t], sig[n_g,K,n_t], v[n_t]).  Load with
  `ecwa.maprefit.load_refit_waves` and synthesize with `ecwa.maprefit.synthesize_waves` to reproduce
  the re-fit ε.  (The Gaussian single-K series is likewise reproducible via `--save` and matches the v4
  reduced-series layout.)
- `tests/test_maprefit.py` — 7 tests: synthesis vs `add_wave`, analytic gradient vs finite differences
  (gauss/student_t/split), a re-fit smoke test, and the save/load round-trip.

## How to reproduce the winner

```
cd ECWA_python_v4
OMP_NUM_THREADS=3 python run_maprefit.py --runs 3423 3426 3433 3443 \
    --kernel gauss --k 2 --thin 1 --maxiter 1500 --gtol 1e-8 --save
```
