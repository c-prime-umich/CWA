# fit_map.jl — MAP re-fit of the verified Gaussian wave model.
#
# checker.jl is included unmodified; this file searches for better inputs to
# the same verifier. Each parameter is a dimensionless offset δ from a warm
# start (actual = init + scale·δ; σ on the log scale), so δ = 0 reproduces the
# warm start exactly.

include(joinpath(@__DIR__, "checker.jl"))

using Turing
using Optim
using ADTypes
using Mooncake
using Statistics
using Random

function fit_setup(data::Data)
    init = (
        A    = [copy(w.A) for w in data.waves],
        logσ = [log.(w.sigma) for w in data.waves],
        v    = [copy(w.v) for w in data.waves],
        θ0   = [w.theta0 for w in data.waves],
        Nt   = [w.Nt for w in data.waves],
    )
    # Velocity moves in absolute rad/s: phase error accumulates as ∫δv dt, so
    # small velocity offsets displace the wave far downstream.
    scales = (
        A    = [max(0.05 * mean(abs, a), 1e-12) for a in init.A],
        logσ = [0.1 for _ in init.A],
        v    = [10.0 for _ in init.A],          # rad/s
        θ0   = [0.1 for _ in init.A],           # rad
    )
    τ = (
        A = [2 * max(std(diff(a)), 1e-12) for a in init.A],
        σ = [2 * max(std(diff(exp.(s))), 1e-12) for s in init.logσ],
        v = [2 * max(std(diff(v)), 1e-12) for v in init.v],
    )
    # Laplace scale: mean absolute residual of the warm start.
    S0 = synthesize(data; kernel = kernel_gauss_c)
    b = mean(abs.(data.XT .- S0))
    return init, scales, τ, b
end

function build_waves(init, scales, δA, δs, δv, δθ)
    T = eltype(δA)
    Nw = length(init.A)
    waves = Vector{Wave{T}}(undef, Nw)
    off = 0
    for w in 1:Nw
        Nt = init.Nt[w]
        r = off+1:off+Nt
        Aw  = init.A[w] .+ scales.A[w] .* view(δA, r)
        σw  = exp.(init.logσ[w] .+ scales.logσ[w] .* view(δs, r))
        vw  = init.v[w] .+ scales.v[w] .* view(δv, r)
        θ0w = init.θ0[w] + scales.θ0[w] * δθ[w]
        waves[w] = Wave(Aw, σw, vw, Nt, θ0w)
        off += Nt
    end
    return waves
end

smoothness_penalty(x, τ) = sum(abs2, diff(x)) / (2 * τ^2)

@model function gauss_map(XT, BG, dt, Nb, Nfr, init, scales, τ, b, kernel, train_cols)
    Nw   = length(init.A)
    ntot = sum(init.Nt)

    δA ~ filldist(Normal(0.0, 5.0), ntot)
    δs ~ filldist(Normal(0.0, 5.0), ntot)
    δv ~ filldist(Normal(0.0, 5.0), ntot)
    δθ ~ filldist(Normal(0.0, 5.0), Nw)

    waves = build_waves(init, scales, δA, δs, δv, δθ)

    pen = zero(eltype(δA))
    for w in 1:Nw
        pen += smoothness_penalty(waves[w].A, τ.A[w])
        pen += smoothness_penalty(waves[w].sigma, τ.σ[w])
        pen += smoothness_penalty(waves[w].v, τ.v[w])
    end
    @addlogprob! -pen

    # S must be synthesized over all frames (the theta recurrence marches
    # frame by frame); only the likelihood is restricted to training columns.
    S = synthesize(BG, waves, dt, Nb, Nfr; kernel = kernel)
    @views @addlogprob! -sum(abs, XT[:, train_cols] .- S[:, train_cols]) / b
    return nothing
end

# Every step-th frame with dt scaled to match: a smaller problem with the same
# structure (coarser Euler integration of the same v(t)).
function thin_frames(data::Data, step::Int)
    XT = data.XT[:, 1:step:end]
    return XT, data.dt * step, size(XT, 2)
end

function fit_gauss(data::Data; kernel = kernel_gauss_c, thin::Int = 1,
                   maxiters::Int = 200, adtype = AutoMooncake(; config = nothing),
                   initial_params = nothing, holdout::Float64 = 0.0, seed::Int = 42)
    init, scales, τ, b = fit_setup(data)
    XT, dt, Nfr = thin == 1 ? (data.XT, data.dt, data.Nfr) : thin_frames(data, thin)

    # Random frame holdout. Parameter samples are ~20 frames apart, so a
    # random test set leaves every sample constrained by nearby training frames.
    if holdout > 0
        perm = randperm(MersenneTwister(seed), Nfr)
        ntest = round(Int, holdout * Nfr)
        test_cols  = sort(perm[1:ntest])
        train_cols = sort(perm[ntest+1:end])
    else
        train_cols = collect(1:Nfr)
        test_cols  = Int[]
    end

    model = gauss_map(XT, data.BG, dt, data.Nb, Nfr, init, scales, τ, b, kernel,
                      train_cols)

    ntot = sum(init.Nt)
    Nw = length(init.A)
    p0 = initial_params === nothing ?
        (; δA = zeros(ntot), δs = zeros(ntot), δv = zeros(ntot), δθ = zeros(Nw)) :
        initial_params

    result = maximum_a_posteriori(model, LBFGS();
                                  adtype = adtype,
                                  initial_params = InitFromParams(p0),
                                  maxiters = maxiters)
    return result, init, scales, train_cols, test_cols
end

function waves_from_result(result, init, scales)
    p = result.params
    return build_waves(init, scales, p[@varname(δA)], p[@varname(δs)],
                       p[@varname(δv)], p[@varname(δθ)])
end

function score(data::Data, waves; kernel = kernel_gauss_c)
    S = synthesize(data.BG, waves, data.dt, data.Nb, data.Nfr; kernel = kernel)
    return residual_fraction(data.XT, S)
end
