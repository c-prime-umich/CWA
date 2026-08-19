# regenerate.jl — reproduces every fitted hypothesis in README-julia.md.
#
# Usage (from the repo root):
#   julia --project=analyzer analyzer/regenerate.jl [stage ...]
#
# Stages (default: gauss split phys — the pipeline to the best result):
#   gauss    Gaussian re-fit of the verified model      -> data_refit/      (~2 min)
#   t        Student-t shape variant                    -> data_refit_t/    (~10 min)
#   2g / 3g  K-component Gaussian variants              -> data_refit_{2,3}g/ (~20/60 min)
#   split    split-σ core + halo                        -> data_refit_2s/   (~50 min)
#   phys     split-σ with measured counter-waves,
#            1×/2×/3× parameter-sample density          -> data_refit_phys{1,2,3}x/ (~1-2 h)
#   measure  re-derive the counter-wave constants used by `phys`
#            (space-time FFT peaks + θ0 scans; prints, writes nothing)
#
# All fits are deterministic given the seed: variant stages use a fixed 20%
# random-frame holdout (seed 42); the gauss stage fits the full record.
# Expected verifier scores are listed in README-julia.md.

include(joinpath(@__DIR__, "fit_variants.jl"))   # pulls in fit_map.jl and checker*.jl
using FFTW

const DATA_DIR = joinpath(@__DIR__, "data")

# Counter-rotating wave parameters measured from the data (see `measure` stage):
# dominant counter-wave mirrors wave 1; a weaker second component sits at +14.5k.
const COUNTER_WAVES = [
    (v = 17780.0, θ0 = 3.36, A = 1200.0, σ = 0.25),   # ≈ 0.66 × CJ, counter-rotating
    (v = 14481.0, θ0 = 2.76, A = 800.0,  σ = 0.25),   # ≈ 0.54 × CJ
]

upsample(y, Nt) = [begin
    a = (j - 1) / (Nt - 1) * (length(y) - 1); i = floor(Int, a)
    i + 1 < length(y) ? (1 - (a - i)) * y[i+1] + (a - i) * y[i+2] : y[end]
  end for j in 1:Nt]

function write_gauss_waves(dir, waves)
    for (i, w) in enumerate(waves)
        d = joinpath(dir, "wave_$i"); mkpath(d)
        writedlm(joinpath(d, "A.csv"), w.A, ',')
        writedlm(joinpath(d, "sigma.csv"), w.sigma, ',')
        writedlm(joinpath(d, "v.csv"), w.v, ',')
        writedlm(joinpath(d, "theta0.csv"), [w.theta0], ',')
    end
    # symlinks so the C verifier can run on the directory directly
    for f in ("XT.csv", "BG.csv", "dt.csv")
        p = joinpath(dir, f)
        islink(p) || isfile(p) || symlink(joinpath("..", "data", f), p)
    end
end

function stage_gauss(data)
    # stage 1: converge on 10×-thinned frames; stage 2: full-resolution polish
    r1, init, scales = fit_gauss(data; thin = 10, maxiters = 500)
    p1 = (; δA = collect(r1.params[@varname(δA)]), δs = collect(r1.params[@varname(δs)]),
            δv = collect(r1.params[@varname(δv)]), δθ = collect(r1.params[@varname(δθ)]))
    r2, _, _ = fit_gauss(data; maxiters = 100, initial_params = p1)
    waves = waves_from_result(r2, init, scales)
    dir = joinpath(@__DIR__, "data_refit")
    write_gauss_waves(dir, waves)
    println("gauss: full ε = ", round(score(data, waves), digits = 5),
            "  (expect ≈ 0.1085; C verifier: ./checker data_refit)")
    return waves
end

load_refit(data) = load_all_data(joinpath(@__DIR__, "data_refit")).waves

function stage_k(data, refit_waves, K, dir)
    pk, build, np, b = make_pack_k(data, refit_waves, K)
    r, δ, tr, te = fit_variant(data, pk, np, b; maxiters = 1500)
    w, _ = build(δ)
    S = synthesize_multi(data.BG, w, data.dt, data.Nb, data.Nfr)
    write_waves_k(dir, w); writedlm(joinpath(dir, "delta.csv"), δ, ',')
    println(K, "g: test ε = ", round(score_cols(data.XT, S, te), digits = 5))
end

function stage_t(data, refit_waves)
    pt, build, np, b = make_pack_t(data, refit_waves)
    r, δ, tr, te = fit_variant(data, pt, np, b; maxiters = 400)
    w, _ = build(δ)
    S = synthesize_t(data.BG, w, data.dt, data.Nb, data.Nfr)
    write_waves_t(joinpath(@__DIR__, "data_refit_t"), w)
    println("t: test ε = ", round(score_cols(data.XT, S, te), digits = 5),
            "   ν = ", round.([x.nu for x in w], digits = 3), "  (degenerate ν→0 expected)")
end

function stage_split(data, refit_waves)
    ps, build, np, b = make_pack_ks(data, refit_waves, 2)
    r, δ, tr, te = fit_variant(data, ps, np, b; maxiters = 1500)
    w, _ = build(δ)
    S = synthesize_split(data.BG, w, data.dt, data.Nb, data.Nfr)
    dir = joinpath(@__DIR__, "data_refit_2s")
    write_waves_ks(dir, w); writedlm(joinpath(dir, "delta.csv"), δ, ',')
    println("split: test ε = ", round(score_cols(data.XT, S, te), digits = 5))
end

function stage_phys(data, refit_waves)
    w1g = refit_waves[1]
    for m in (1, 2, 3)
        Nt = 500m + 1
        w1 = Wave(upsample(w1g.A, Nt), upsample(w1g.sigma, Nt), upsample(w1g.v, Nt),
                  Nt, w1g.theta0)
        counters = [Wave(fill(c.A, Nt), fill(c.σ, Nt), fill(c.v, Nt), Nt, c.θ0)
                    for c in COUNTER_WAVES]
        ps, build, np, b = make_pack_ks(data, [w1; counters], 2; scv = 50.0)
        r, δ, tr, te = fit_variant(data, ps, np, b; maxiters = 1500)
        w, _ = build(δ)
        S = synthesize_split(data.BG, w, data.dt, data.Nb, data.Nfr)
        dir = joinpath(@__DIR__, "data_refit_phys$(m)x")
        write_waves_ks(dir, w); writedlm(joinpath(dir, "delta.csv"), δ, ',')
        println("phys ", m, "x: test ε = ", round(score_cols(data.XT, S, te), digits = 5))
    end
end

# Re-derive COUNTER_WAVES from the data: space-time spectrum + θ0 scans.
function stage_measure(data)
    S_bg = synthesize(data.BG, Wave{Float64}[], data.dt, data.Nb, data.Nfr)
    Xw = data.XT .- S_bg
    θs = [2π * (i - 1) / data.Nb for i in 1:data.Nb]
    freqs = fftfreq(data.Nfr, 1 / data.dt)
    # a wave at velocity v appears at temporal frequency f = -n·v/(2π)
    for n in 1:2
        cn = [sum(Xw[i, k] * cis(-n * θs[i]) for i in 1:data.Nb) for k in 1:data.Nfr]
        P = abs2.(fft(cn .- mean(cn)))
        ord = sortperm(P; rev = true)
        picked = Tuple{Float64, Float64}[]
        for j in ord
            f = freqs[j]; abs(f) < 300 && continue
            any(abs(f - p[1]) < 900 for p in picked) && continue
            push!(picked, (f, P[j])); length(picked) == 6 && break
        end
        println("n=$n peaks (v rad/s, rel power): ",
                [(round(Int, -2π * f / n), round(p / picked[1][2], digits = 3))
                 for (f, p) in picked])
    end
    # θ0 by direct verifier-metric scan for each counter-wave candidate
    refit_waves = load_refit(data)
    placed = Wave{Float64}[refit_waves[1]]
    for c in COUNTER_WAVES
        θgrid = 0:0.06:2π
        mk(θ) = Wave(fill(c.A, 501), fill(c.σ, 501), fill(c.v, 501), 501, θ)
        εs = [residual_fraction(data.XT,
                 synthesize(data.BG, [placed; mk(θ)], data.dt, data.Nb, data.Nfr))
              for θ in θgrid]
        θb = θgrid[argmin(εs)]
        println("v=+", c.v, ": best θ0 = ", round(θb, digits = 2),
                " (ε ", round(minimum(εs), digits = 5), ")")
        push!(placed, mk(θb))
    end
end

function main(stages)
    data = load_all_data(DATA_DIR)
    refit = nothing
    getrefit() = refit === nothing ? (refit = load_refit(data)) : refit
    for s in stages
        s == "gauss"   ? (refit = stage_gauss(data)) :
        s == "t"       ? stage_t(data, getrefit()) :
        s == "2g"      ? stage_k(data, getrefit(), 2, joinpath(@__DIR__, "data_refit_2g")) :
        s == "3g"      ? stage_k(data, getrefit(), 3, joinpath(@__DIR__, "data_refit_3g")) :
        s == "split"   ? stage_split(data, getrefit()) :
        s == "phys"    ? stage_phys(data, getrefit()) :
        s == "measure" ? stage_measure(data) :
        error("unknown stage: $s (gauss|t|2g|3g|split|phys|measure)")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main(isempty(ARGS) ? ["gauss", "split", "phys"] : ARGS)
end
