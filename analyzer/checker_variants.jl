# checker_variants.jl — minimally-perturbed variants of the verified synthesize loop.
# ======================== Variant 1: Student-t ========================

struct WaveT{T<:Real}
    A::Vector{T}
    sigma::Vector{T}
    v::Vector{T}
    Nt::Int
    theta0::T
    nu::T                       # ONLY CHANGE vs Wave: one scalar field
end

function synthesize_t!(S::AbstractMatrix,
                       theta_buf::AbstractVector,
                       BG::AbstractMatrix,
                       waves::AbstractVector{<:WaveT},
                       dt::Real)
    Nb, Nfr = size(S)
    Nbg = size(BG, 2)
    Nw  = length(waves)
    @assert length(theta_buf) >= Nw

    @inbounds for k in 0:Nfr - 1
        bg_col = trunc(Int, (k / (Nfr - 1)) * (Nbg - 1))
        for i in 0:Nb - 1
            a = BG[i + 1, bg_col + 1]
            for w in 1:Nw
                Nt = waves[w].Nt
                A     = interpolate(Nfr, Nt, waves[w].A,     k)
                sigma = interpolate(Nfr, Nt, waves[w].sigma, k)

                if i == 0
                    if k == 0
                        theta_buf[w] = waves[w].theta0
                    else
                        v = interpolate(Nfr, Nt, waves[w].v, k - 1)
                        theta_buf[w] = range2pi(theta_buf[w] + v * dt)
                    end
                end

                dx = wrap(i * (L / Nb) - theta_buf[w])
                nu = waves[w].nu
                # ONLY CHANGE vs synthesize_c!: Student-t shape instead of Gaussian
                a += A * (1.0 + dx * dx / (nu * (sigma * sigma)))^(-(nu + 1.0) / 2.0)
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize_t(BG::AbstractMatrix, waves::AbstractVector{<:WaveT},
                      dt::Real, Nb::Int, Nfr::Int)
    T = promote_type(eltype(BG), typeof(dt),
                     isempty(waves) ? Float64 : eltype(first(waves).A))
    S = Matrix{T}(undef, Nb, Nfr)
    theta_buf = Vector{T}(undef, length(waves))
    return synthesize_t!(S, theta_buf, BG, waves, dt)
end

# ======================== Variant 2: K Gaussian components ========================

struct WaveK{T<:Real}
    A::Vector{Vector{T}}        # ONLY CHANGE vs Wave: K series instead of 1
    sigma::Vector{Vector{T}}    # ONLY CHANGE vs Wave: K series instead of 1
    v::Vector{T}
    Nt::Int
    theta0::T
end

ncomponents(w::WaveK) = length(w.A)

function synthesize_multi!(S::AbstractMatrix,
                           theta_buf::AbstractVector,
                           BG::AbstractMatrix,
                           waves::AbstractVector{<:WaveK},
                           dt::Real)
    Nb, Nfr = size(S)
    Nbg = size(BG, 2)
    Nw  = length(waves)
    @assert length(theta_buf) >= Nw

    @inbounds for k in 0:Nfr - 1
        bg_col = trunc(Int, (k / (Nfr - 1)) * (Nbg - 1))
        for i in 0:Nb - 1
            a = BG[i + 1, bg_col + 1]
            for w in 1:Nw
                Nt = waves[w].Nt

                if i == 0
                    if k == 0
                        theta_buf[w] = waves[w].theta0
                    else
                        v = interpolate(Nfr, Nt, waves[w].v, k - 1)
                        theta_buf[w] = range2pi(theta_buf[w] + v * dt)
                    end
                end

                dx = wrap(i * (L / Nb) - theta_buf[w])
                # ONLY CHANGE vs synthesize_c!: sum K components, same expression each
                for c in 1:ncomponents(waves[w])
                    A     = interpolate(Nfr, Nt, waves[w].A[c],     k)
                    sigma = interpolate(Nfr, Nt, waves[w].sigma[c], k)
                    a += A * exp(-(dx * dx / (2.0 * (sigma * sigma))))
                end
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize_multi(BG::AbstractMatrix, waves::AbstractVector{<:WaveK},
                          dt::Real, Nb::Int, Nfr::Int)
    T = promote_type(eltype(BG), typeof(dt),
                     isempty(waves) ? Float64 : eltype(first(first(waves).A)))
    S = Matrix{T}(undef, Nb, Nfr)
    theta_buf = Vector{T}(undef, length(waves))
    return synthesize_multi!(S, theta_buf, BG, waves, dt)
end

# ======================== Variant 3: split-σ (two-piece) Gaussians ========================
# Each component has separate width series per side of the peak: sigmaN for
# dx < 0, sigmaP for dx >= 0. Which side leads follows from sign(v) and is
# resolved at analysis time. sigmaN == sigmaP reduces bit-for-bit to variant 2.

struct WaveKS{T<:Real}
    A::Vector{Vector{T}}
    sigmaN::Vector{Vector{T}}   # widths for dx < 0 side
    sigmaP::Vector{Vector{T}}   # ONLY CHANGE vs WaveK: second width series set
    v::Vector{T}
    Nt::Int
    theta0::T
end

ncomponents(w::WaveKS) = length(w.A)

function synthesize_split!(S::AbstractMatrix,
                           theta_buf::AbstractVector,
                           BG::AbstractMatrix,
                           waves::AbstractVector{<:WaveKS},
                           dt::Real)
    Nb, Nfr = size(S)
    Nbg = size(BG, 2)
    Nw  = length(waves)
    @assert length(theta_buf) >= Nw

    @inbounds for k in 0:Nfr - 1
        bg_col = trunc(Int, (k / (Nfr - 1)) * (Nbg - 1))
        for i in 0:Nb - 1
            a = BG[i + 1, bg_col + 1]
            for w in 1:Nw
                Nt = waves[w].Nt

                if i == 0
                    if k == 0
                        theta_buf[w] = waves[w].theta0
                    else
                        v = interpolate(Nfr, Nt, waves[w].v, k - 1)
                        theta_buf[w] = range2pi(theta_buf[w] + v * dt)
                    end
                end

                dx = wrap(i * (L / Nb) - theta_buf[w])
                for c in 1:ncomponents(waves[w])
                    A = interpolate(Nfr, Nt, waves[w].A[c], k)
                    # ONLY CHANGE vs synthesize_multi!: pick width series by side
                    sser  = dx >= 0.0 ? waves[w].sigmaP[c] : waves[w].sigmaN[c]
                    sigma = interpolate(Nfr, Nt, sser, k)
                    a += A * exp(-(dx * dx / (2.0 * (sigma * sigma))))
                end
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize_split(BG::AbstractMatrix, waves::AbstractVector{<:WaveKS},
                          dt::Real, Nb::Int, Nfr::Int)
    T = promote_type(eltype(BG), typeof(dt),
                     isempty(waves) ? Float64 : eltype(first(first(waves).A)))
    S = Matrix{T}(undef, Nb, Nfr)
    theta_buf = Vector{T}(undef, length(waves))
    return synthesize_split!(S, theta_buf, BG, waves, dt)
end

# ======================== hypothesis IO ========================
# The CSV layout extends the verified format backward-compatibly: Student-t
# adds wave_i/nu.csv; K-component adds A2.csv, sigma2.csv, ...; split-σ writes
# sigmaN*.csv / sigmaP*.csv in place of sigma*.csv.

function write_waves_t(dir::AbstractString, waves::AbstractVector{<:WaveT})
    for (i, w) in enumerate(waves)
        d = joinpath(dir, "wave_$i"); mkpath(d)
        writedlm(joinpath(d, "A.csv"), w.A, ',')
        writedlm(joinpath(d, "sigma.csv"), w.sigma, ',')
        writedlm(joinpath(d, "v.csv"), w.v, ',')
        writedlm(joinpath(d, "theta0.csv"), [w.theta0], ',')
        writedlm(joinpath(d, "nu.csv"), [w.nu], ',')
    end
end

function write_waves_k(dir::AbstractString, waves::AbstractVector{<:WaveK})
    for (i, w) in enumerate(waves)
        d = joinpath(dir, "wave_$i"); mkpath(d)
        for c in 1:ncomponents(w)
            suffix = c == 1 ? "" : string(c)
            writedlm(joinpath(d, "A$(suffix).csv"), w.A[c], ',')
            writedlm(joinpath(d, "sigma$(suffix).csv"), w.sigma[c], ',')
        end
        writedlm(joinpath(d, "v.csv"), w.v, ',')
        writedlm(joinpath(d, "theta0.csv"), [w.theta0], ',')
    end
end

function write_waves_ks(dir::AbstractString, waves::AbstractVector{<:WaveKS})
    for (i, w) in enumerate(waves)
        d = joinpath(dir, "wave_$i"); mkpath(d)
        for c in 1:ncomponents(w)
            suffix = c == 1 ? "" : string(c)
            writedlm(joinpath(d, "A$(suffix).csv"), w.A[c], ',')
            writedlm(joinpath(d, "sigmaN$(suffix).csv"), w.sigmaN[c], ',')
            writedlm(joinpath(d, "sigmaP$(suffix).csv"), w.sigmaP[c], ',')
        end
        writedlm(joinpath(d, "v.csv"), w.v, ',')
        writedlm(joinpath(d, "theta0.csv"), [w.theta0], ',')
    end
end
