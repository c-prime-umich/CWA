# Julia port and probabilistic re-fitting of the CWA hypothesis

This directory contains a Julia translation of the verifier (`checker.c`), a
probabilistic-programming analyzer built on it, and re-fitted hypotheses that
substantially improve on the MATLAB pipeline's fit — measured by the verifier's
own 1-norm criterion and validated on held-out camera frames.

The fitting layer searches for better
*inputs* to the same verifier; model-shape experiments are implemented as
separate, minimally-perturbed copies of the verified loop (see "Variants").

## Files

| File | Contents |
|---|---|
| `checker.jl` | Julia translation of `checker.c`: `synthesize_ref` (faithful port), `synthesize_c!` (statement-for-statement mirror of the C `synthesize`, bit-compatible), an optimized `synthesize!` (identical output, ~2× faster), CSV loaders, `residual_fraction` (the verifier metric) |
| `checker_variants.jl` | Model variants, each a full copy of the verified loop with the diff marked by `ONLY CHANGE` comments: Student-t shape (`WaveT`), K Gaussian components per wave (`WaveK`), split-σ two-piece Gaussians (`WaveKS`). Each reduces **bitwise** to the verified model when its extra freedom is switched off |
| `fit_map.jl` | Turing.jl MAP re-fit of the *unmodified* Gaussian model: δ-offset parameterization around a warm start, random-walk smoothness priors, Laplace likelihood ≡ verifier 1-norm, random-frame holdout |
| `fit_variants.jl` | Same fitting machinery generalized to the variants |
| `regenerate.jl` | Reproduces every fitted hypothesis below (`julia --project=analyzer analyzer/regenerate.jl [stage...]`) |
| `Project.toml` / `Manifest.toml` | Julia environment (Turing, Mooncake reverse-mode AD, Optim, FFTW, …) |

## Quick start

```sh
julia --project=analyzer
julia> include("analyzer/checker.jl")
julia> data = load_all_data("analyzer/data")
julia> residual_fraction(data.XT, synthesize_c(data))   # 0.14851, matches ./checker data
```

Reproduce the Gaussian re-fit (≈1 min):

```julia
include("analyzer/fit_map.jl")
result, init, scales, tr, te = fit_gauss(data; holdout=0.2, maxiters=400)
waves = waves_from_result(result, init, scales)
score(data, waves)              # ≈ 0.108
```

The C verifier accepts the re-fitted hypothesis directly (build without the
LAProof-dependent Makefile rules, since `densemat.*`/`alloc.*` are already
present):

```sh
cd analyzer
gcc -O2 -c checker.c densemat.c alloc.c && gcc *.o -o checker -lm
./checker data_refit        # residual energy fraction = 1.085e-01
```

## Results

All hypotheses were fit with 20% of frames held out (fixed split); "test ε" is
the verifier 1-norm on those unseen frames. The camera-noise floor of this
record is ε ≈ 0.012 (measured by spatial-whiteness analysis + photon-transfer
curve).

No fitted results are committed — all `data_refit*` directories are
git-ignored experiment outputs. Regenerate any of them with:

```sh
julia --project=analyzer analyzer/regenerate.jl            # gauss → split → phys (best result)
julia --project=analyzer analyzer/regenerate.jl gauss      # ~2 min, verifier-format output
julia --project=analyzer analyzer/regenerate.jl measure    # re-derive counter-wave constants
```

Stages, runtimes, and output directories are documented at the top of
`regenerate.jl`. The `gauss` stage must run first (the others warm-start from
its output); its result is in the verified CSV format and can be checked
directly with the C verifier (`./checker data_refit`).

| Hypothesis | test ε | note |
|---|---|---|
| MATLAB pipeline (baseline, `data/`) | 0.1486 | |
| Gaussian re-fit — **same verified model, better values** (`data_refit/`) | 0.1082 | C-verifier confirmed: 1.085e-01 |
| Student-t shape | 0.0979 | degenerate ν→0; superseded |
| 2 Gaussians/wave | 0.0911 | core + wide halo |
| 3 Gaussians/wave | 0.0911 | no gain over 2 |
| Split-σ core + halo | 0.0856 | wave-1 asymmetry emerges |
| **Split-σ + corrected wave physics** | **0.0804** | best; all 3 waves ablation-verified |
| … at 2×/3× parameter-sample density | 0.0808 / 0.0811 | sample density is not the bottleneck |

Extended CSV formats: variants add `nu.csv` (Student-t), `A2.csv`/`sigma2.csv`
(K components), `sigmaN*.csv`/`sigmaP*.csv` (split-σ) per wave directory; a
directory without the extra files is exactly the verified format.

## Findings

1. **Wave 1** (−17,880 rad/s) is asymmetric: steep leading edge (σ ≈ 0.33 rad)
   vs slow trailing decay (σ ≈ 0.52), plus a large trailing halo (σ ≈ 3.9 rad,
   ~28% of core amplitude). Confirmed model-free in the co-moving raw-data
   profile (HWHM ratio 1.67).
2. **The original waves 2/3 velocities appear to be wrong for this record.**
   `vcrwps`/`vcdets` × Dcj gives +83,646 / +105,691 rad/s; the space-time FFT
   of the data shows essentially zero power there (≤0.04% of wave 1), and
   removing those fitted waves *improves* the fit. The record instead contains
   two dim counter-rotating waves at ≈ **+17,780** and **+14,470 rad/s**
   (0.66/0.54 × CJ), both of which survive ablation once fit. Worth checking
   the units/interpretation of `plot4_data_conditioned.mat`.
3. **A hot sector near mid-ring** (px ≈ 45–90) both raises the static
   background (1.6×) and doubles the waves' own brightness when they pass it.
   The wave model cannot express angle-dependent brightness; this is the
   dominant remaining structured residual (lap-period recurrence in the
   residual autocorrelation). Proposed next variant: a per-ring angular gain
   `g(θ)` multiplying the wave term — one extra multiply in the verified loop,
   reducing to the current model at g ≡ 1.
4. Of the remaining ε ≈ 0.08, about 0.012 is camera noise (photon-transfer
   verified); the rest is fast, wave-locked turbulent brightness fluctuation.

## Verified-code impact of the variants

| Variant | diff vs verified `synthesize` |
|---|---|
| K components | `A`,`sigma` become K series; accumulation line wrapped in a K-loop (K=1 ≡ current, bitwise) |
| Split-σ | one extra width series per component + a sign test choosing the side |
| Student-t | one scalar field ν per wave; accumulation expression swapped |
