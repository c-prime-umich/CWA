# fit_variants.jl — MAP fitting for the synthesize variants.
#
# Same architecture as fit_map.jl, generalized: one Turing model; each variant
# supplies a `pack` closure δ -> (S, smoothness penalty). Fits warm-start from
# the Gaussian re-fit (data_refit/) and use a fixed random-frame holdout.

include(joinpath(@__DIR__, "fit_map.jl"))
include(joinpath(@__DIR__, "checker_variants.jl"))

# ---------------- shared helpers ----------------

series_scale(a) = max(0.05 * mean(abs, a), 1e-12)

# Smoothness scale from the warm start's own roughness. Constant-initialized
# series (new waves with no fitted history) get a floor of 1% of their
# magnitude per sample so the fit can discover their shape.
function series_τ(a)
    s = std(diff(a))
    return 2 * (s > 0 ? s : 0.01 * mean(abs, a) + 1e-12)
end

function holdout_split(Nfr::Int, holdout::Float64, seed::Int)
    holdout <= 0 && return collect(1:Nfr), Int[]
    perm = randperm(MersenneTwister(seed), Nfr)
    ntest = round(Int, holdout * Nfr)
    return sort(perm[ntest+1:end]), sort(perm[1:ntest])
end

@model function variant_map(XT, train_cols, npar, pack, b)
    δ ~ filldist(Normal(0.0, 5.0), npar)
    S, pen = pack(δ)
    @addlogprob! -pen
    @views @addlogprob! -sum(abs, XT[:, train_cols] .- S[:, train_cols]) / b
    return nothing
end

function fit_variant(data::Data, pack, npar, b;
                     holdout::Float64 = 0.2, seed::Int = 42, maxiters::Int = 400,
                     adtype = AutoMooncake(; config = nothing))
    train_cols, test_cols = holdout_split(data.Nfr, holdout, seed)
    model = variant_map(data.XT, train_cols, npar, pack, b)
    result = maximum_a_posteriori(model, LBFGS();
                                  adtype = adtype,
                                  initial_params = InitFromParams((; δ = zeros(npar))),
                                  maxiters = maxiters)
    δhat = collect(result.params[@varname(δ)])
    return result, δhat, train_cols, test_cols
end

score_cols(XT, S, cols) = residual_fraction(view(XT, :, cols), view(S, :, cols))

# ---------------- Student-t variant ----------------

"""
    make_pack_t(data, waves0; nu0 = 2.0)

δ layout: [δA (ntot); δlogσ (ntot); δv (ntot); δθ0 (Nw); δlogν (Nw)].
ν = nu0·exp(0.7 δ) per wave: positive, spanning ~[0.06, 66] within the ±5-sd
trust region, with the Gaussian limit approached as ν grows.
"""
function make_pack_t(data::Data, waves0; nu0 = 2.0)
    Nw   = length(waves0)
    Nts  = [w.Nt for w in waves0]
    ntot = sum(Nts)
    initA  = [copy(w.A) for w in waves0]
    initls = [log.(w.sigma) for w in waves0]
    initv  = [copy(w.v) for w in waves0]
    initθ  = [w.theta0 for w in waves0]
    scA = series_scale.(initA); scls = 0.1; scv = 10.0; scθ = 0.1; scln = 0.7
    τA = [series_τ(a) for a in initA]
    τσ = [series_τ(exp.(s)) for s in initls]
    τv = [series_τ(v) for v in initv]
    BG = data.BG; dt = data.dt; Nb = data.Nb; Nfr = data.Nfr
    npar = 3 * ntot + 2 * Nw

    function build(δ)
        T = eltype(δ)
        waves = Vector{WaveT{T}}(undef, Nw)
        pen = zero(T)
        off = 0
        for w in 1:Nw
            Nt = Nts[w]
            Aw = initA[w]  .+ scA[w] .* view(δ, off+1:off+Nt)
            σw = exp.(initls[w] .+ scls .* view(δ, ntot+off+1:ntot+off+Nt))
            vw = initv[w]  .+ scv .* view(δ, 2ntot+off+1:2ntot+off+Nt)
            θw = initθ[w] + scθ * δ[3ntot + w]
            νw = nu0 * exp(scln * δ[3ntot + Nw + w])
            waves[w] = WaveT(Aw, σw, vw, Nt, θw, νw)
            pen += sum(abs2, diff(Aw)) / (2 * τA[w]^2) +
                   sum(abs2, diff(σw)) / (2 * τσ[w]^2) +
                   sum(abs2, diff(vw)) / (2 * τv[w]^2)
            off += Nt
        end
        return waves, pen
    end

    function pack(δ)
        waves, pen = build(δ)
        return synthesize_t(BG, waves, dt, Nb, Nfr), pen
    end

    S0, _ = pack(zeros(npar))
    b = mean(abs.(data.XT .- S0))
    return pack, build, npar, b
end

# ---------------- K-Gaussian variant ----------------

# Component init ratios (amplitude ×, width ×) relative to the fitted single
# Gaussian. Component 1 is the warm start; extras start as wide, low "halo"
# components so the optimizer can grow tails where the data pays for them.
const COMPONENT_INIT = [(1.0, 1.0), (0.2, 2.5), (0.08, 5.0)]

"""
    make_pack_k(data, waves0, K)

δ layout: [δA (K·ntot, component-major); δlogσ (K·ntot); δv (ntot); δθ0 (Nw)].
Amplitude scale for every component is based on component 1's magnitude, so
halos can grow well beyond their small initial amplitude.
"""
function make_pack_k(data::Data, waves0, K::Int)
    @assert 1 <= K <= length(COMPONENT_INIT)
    Nw   = length(waves0)
    Nts  = [w.Nt for w in waves0]
    ntot = sum(Nts)
    initA  = [[COMPONENT_INIT[c][1] .* w.A for c in 1:K] for w in waves0]
    initls = [[log.(COMPONENT_INIT[c][2] .* w.sigma) for c in 1:K] for w in waves0]
    initv  = [copy(w.v) for w in waves0]
    initθ  = [w.theta0 for w in waves0]
    scA = [series_scale(initA[w][1]) for w in 1:Nw]
    scls = 0.1; scv = 10.0; scθ = 0.1
    τA = [[series_τ(initA[w][c]) for c in 1:K] for w in 1:Nw]
    τσ = [[series_τ(exp.(initls[w][c])) for c in 1:K] for w in 1:Nw]
    τv = [series_τ(v) for v in initv]
    BG = data.BG; dt = data.dt; Nb = data.Nb; Nfr = data.Nfr
    npar = 2 * K * ntot + ntot + Nw

    function build(δ)
        T = eltype(δ)
        waves = Vector{WaveK{T}}(undef, Nw)
        pen = zero(T)
        off = 0
        for w in 1:Nw
            Nt = Nts[w]
            Acs = Vector{Vector{T}}(undef, K)
            σcs = Vector{Vector{T}}(undef, K)
            for c in 1:K
                oA = (c - 1) * ntot + off
                os = K * ntot + (c - 1) * ntot + off
                Acs[c] = initA[w][c] .+ scA[w] .* view(δ, oA+1:oA+Nt)
                σcs[c] = exp.(initls[w][c] .+ scls .* view(δ, os+1:os+Nt))
                pen += sum(abs2, diff(Acs[c])) / (2 * τA[w][c]^2) +
                       sum(abs2, diff(σcs[c])) / (2 * τσ[w][c]^2)
            end
            ov = 2 * K * ntot + off
            vw = initv[w] .+ scv .* view(δ, ov+1:ov+Nt)
            θw = initθ[w] + scθ * δ[2 * K * ntot + ntot + w]
            waves[w] = WaveK(Acs, σcs, vw, Nt, θw)
            pen += sum(abs2, diff(vw)) / (2 * τv[w]^2)
            off += Nt
        end
        return waves, pen
    end

    function pack(δ)
        waves, pen = build(δ)
        return synthesize_multi(BG, waves, dt, Nb, Nfr), pen
    end

    S0, _ = pack(zeros(npar))
    b = mean(abs.(data.XT .- S0))
    return pack, build, npar, b
end

# ---------------- split-σ K-Gaussian variant ----------------

"""
    make_pack_ks(data, waves0, K; scv = 10.0)

Like `make_pack_k` with independent widths per side of the peak. Both sides
initialize to the same symmetric warm start, so δ = 0 is the symmetric model
and asymmetry appears only where the data pays for it. `scv` is the velocity
step in rad/s; widen it when wave velocities are only approximately known.
δ layout: [δA (K·ntot); δlogσN (K·ntot); δlogσP (K·ntot); δv (ntot); δθ0 (Nw)].
"""
function make_pack_ks(data::Data, waves0, K::Int; scv = 10.0)
    @assert 1 <= K <= length(COMPONENT_INIT)
    Nw   = length(waves0)
    Nts  = [w.Nt for w in waves0]
    ntot = sum(Nts)
    initA  = [[COMPONENT_INIT[c][1] .* w.A for c in 1:K] for w in waves0]
    initls = [[log.(COMPONENT_INIT[c][2] .* w.sigma) for c in 1:K] for w in waves0]
    initv  = [copy(w.v) for w in waves0]
    initθ  = [w.theta0 for w in waves0]
    scA = [series_scale(initA[w][1]) for w in 1:Nw]
    scls = 0.1; scθ = 0.1
    τA = [[series_τ(initA[w][c]) for c in 1:K] for w in 1:Nw]
    τσ = [[series_τ(exp.(initls[w][c])) for c in 1:K] for w in 1:Nw]
    τv = [series_τ(v) for v in initv]
    BG = data.BG; dt = data.dt; Nb = data.Nb; Nfr = data.Nfr
    npar = 3 * K * ntot + ntot + Nw

    function build(δ)
        T = eltype(δ)
        waves = Vector{WaveKS{T}}(undef, Nw)
        pen = zero(T)
        off = 0
        for w in 1:Nw
            Nt = Nts[w]
            Acs = Vector{Vector{T}}(undef, K)
            σNs = Vector{Vector{T}}(undef, K)
            σPs = Vector{Vector{T}}(undef, K)
            for c in 1:K
                oA = (c - 1) * ntot + off
                oN = K * ntot + (c - 1) * ntot + off
                oP = 2 * K * ntot + (c - 1) * ntot + off
                Acs[c] = initA[w][c] .+ scA[w] .* view(δ, oA+1:oA+Nt)
                σNs[c] = exp.(initls[w][c] .+ scls .* view(δ, oN+1:oN+Nt))
                σPs[c] = exp.(initls[w][c] .+ scls .* view(δ, oP+1:oP+Nt))
                pen += sum(abs2, diff(Acs[c])) / (2 * τA[w][c]^2) +
                       sum(abs2, diff(σNs[c])) / (2 * τσ[w][c]^2) +
                       sum(abs2, diff(σPs[c])) / (2 * τσ[w][c]^2)
            end
            ov = 3 * K * ntot + off
            vw = initv[w] .+ scv .* view(δ, ov+1:ov+Nt)
            θw = initθ[w] + scθ * δ[3 * K * ntot + ntot + w]
            waves[w] = WaveKS(Acs, σNs, σPs, vw, Nt, θw)
            pen += sum(abs2, diff(vw)) / (2 * τv[w]^2)
            off += Nt
        end
        return waves, pen
    end

    function pack(δ)
        waves, pen = build(δ)
        return synthesize_split(BG, waves, dt, Nb, Nfr), pen
    end

    S0, _ = pack(zeros(npar))
    b = mean(abs.(data.XT .- S0))
    return pack, build, npar, b
end
